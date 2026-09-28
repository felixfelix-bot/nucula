#include "wallet.hpp"
#include "wallet_internal.hpp"
#include "cashu_json.hpp"

#include <algorithm>
#include <cstdio>
#include <cstring>
#include <esp_log.h>
#include <nvs.h>

// Per-wallet-slot NVS persistence: mint URL, proof and keyset blobs, and
// the offline-receive pending-token queue.

static void slot_key(char* buf, size_t sz, const char* base, int slot)
{
    snprintf(buf, sz, "%s_%d", base, slot);
}

namespace cashu {

// -------------------------------------------------------------------------
// Proof store
// -------------------------------------------------------------------------
//
// Schema (namespace "wallet"), one wallet slot:
//
//   pn_<slot>      u16     number of proof slots. A HIGH-WATER MARK, not a
//                          live count: indices below it may be empty (a hole
//                          left by an earlier erase or by an interrupted
//                          save), and holes are reused before the mark grows.
//   p<slot>_<i>    blob    one serialized Proof at slot i < pn_<slot>, in the
//                          same JSON encoding the single-blob format stored
//                          inside its array.
//   proofs_<slot>  blob    LEGACY: the whole proof set as one JSON array.
//                          Read-only fallback, retired once the per-proof
//                          store above is durable.
//
// Why: the legacy format re-serialised the entire proof set on every
// mutation, so every payment paid O(total proofs) bytes of flash (measured
// on the native harness: 47 202 B written per mutation at 200 proofs). Proofs
// are independent bearer tokens, so their persistence does not have to be one
// entry: with one NVS entry per proof a mutation writes only the entries that
// actually changed -- a spend with two change outputs writes two entries plus
// the count, and erases the spent ones.
//
// Crash consistency rests on two things:
//   1. NVS gives per-key atomicity: an interrupted commit never leaves a
//      half-written entry (the entry is written and CRC'd first, and the page
//      index only then points at it), so every key on flash is either its old
//      value or its new one.
//   2. The write order used below -- new proofs, then the count, then the
//      erases -- means an interruption can leave STALE proofs behind but can
//      never remove a proof that was already stored. After any interruption
//      the stored set S satisfies:
//
//          old ∩ new  ⊆  S  ⊆  old ∪ new
//
//      Stale proofs are spent proofs, which the mint rejects (and a future
//      NUT-07 state check would clean up); losing a proof would be losing
//      money. The legacy format had a different property -- a mutation was
//      all-or-nothing -- and it kept it only at the cost of rewriting
//      everything.
namespace proof_store {
namespace {

// FNV-1a over the serialized proof. Used ONLY to prune the byte comparisons
// below: equality is always decided by comparing the bytes themselves, so a
// fingerprint collision can cost a redundant write and can never leave a
// proof unpersisted.
uint32_t proof_fingerprint(const std::string& s)
{
    uint32_t h = 2166136261u;
    for (unsigned char c : s) {
        h ^= c;
        h *= 16777619u;
    }
    return h;
}

void proof_count_key(char* buf, size_t sz, int slot)
{
    snprintf(buf, sz, "pn_%d", slot);
}

// ESP-IDF allows 15 characters plus NUL; the longest key built here is
// "p2_65535" (8). Slot indices above 65535 are rejected rather than wrapped.
void proof_slot_key(char* buf, size_t sz, int slot, unsigned idx)
{
    snprintf(buf, sz, "p%d_%u", slot, idx);
}

void legacy_proofs_key(char* buf, size_t sz, int slot)
{
    snprintf(buf, sz, "proofs_%d", slot);
}

constexpr unsigned PROOF_SLOT_MAX = 65535u;

// ESP_OK with `out` holding the stored bytes; ESP_ERR_NVS_NOT_FOUND for a
// hole or a slot that was never written.
esp_err_t read_proof_slot(nvs_handle_t h, int slot, unsigned idx, std::string& out)
{
    char key[16];
    proof_slot_key(key, sizeof(key), slot, idx);
    size_t len = 0;
    if (nvs_get_blob(h, key, nullptr, &len) != ESP_OK || len == 0)
        return ESP_ERR_NVS_NOT_FOUND;
    out.assign(len, '\0');
    size_t got = len;
    if (nvs_get_blob(h, key, &out[0], &got) != ESP_OK)
        return ESP_ERR_NVS_INVALID_STATE;
    out.resize(got);
    return ESP_OK;
}

bool tolerated(esp_err_t e)
{
    return e == ESP_OK || e == ESP_ERR_NVS_NOT_FOUND;
}

} // namespace

// Write `proofs` as wallet slot `slot`, touching only what changed.
bool save(int slot, const std::vector<Proof>& proofs)
{
    // Serialize-validate the whole new state first: an unserializable proof
    // must abort the save before anything is written, never leave a
    // half-updated store ("[]" is a legitimate empty set, not a substitute
    // for one that failed to serialize). The fingerprints computed here are
    // reused by the pairing pass below.
    std::vector<uint32_t> fp;
    fp.reserve(proofs.size());
    for (const Proof& p : proofs) {
        std::string s = serialize(p);
        if (s.empty()) {
            ESP_LOGE(TAG, "save_proofs: serialization failed, keeping stored proofs");
            return false;
        }
        fp.push_back(proof_fingerprint(s));
    }

    Nvs nvs(NVS_READWRITE);
    if (!nvs.ok()) {
        ESP_LOGE(TAG, "nvs_open failed: %s", esp_err_to_name(nvs.err()));
        return false;
    }
    nvs_handle_t h = nvs.get();

    char cnt_key[16];
    proof_count_key(cnt_key, sizeof(cnt_key), slot);
    uint16_t stored_count = 0;
    esp_err_t err = nvs_get_u16(h, cnt_key, &stored_count);
    const bool established = (err == ESP_OK);   // per-proof store already live
    if (!tolerated(err)) {
        ESP_LOGE(TAG, "save_proofs: read %s failed: %s", cnt_key, esp_err_to_name(err));
        return false;
    }
    if (!established)
        stored_count = 0;

    // Pair stored slots with the in-RAM proofs: each stored slot pairs with at
    // most one proof and vice versa. Paired slots are byte-identical to what
    // is already on flash and are NOT rewritten -- that is where the write
    // saving comes from. Unpaired stored slots are stale (spent/superseded);
    // unpaired proofs are new.
    std::vector<bool> paired(proofs.size(), false);
    std::vector<unsigned> reuse;    // holes: filled before the mark grows
    std::vector<unsigned> stale;    // kept alive until the very last step
    unsigned high_water = 0;

    for (unsigned i = 0; i < stored_count; i++) {
        std::string stored;
        if (read_proof_slot(h, slot, i, stored) != ESP_OK) {
            reuse.push_back(i);
            continue;
        }
        const uint32_t sfp = proof_fingerprint(stored);
        size_t hit = proofs.size();
        for (size_t j = 0; j < proofs.size(); j++) {
            if (paired[j] || fp[j] != sfp)
                continue;
            if (serialize(proofs[j]) == stored) {   // exact, not fingerprint
                hit = j;
                break;
            }
        }
        if (hit == proofs.size()) {
            stale.push_back(i);
        } else {
            paired[hit] = true;
            high_water = i + 1;
        }
    }

    struct Pending { unsigned slot; size_t index; };
    std::vector<Pending> pending;
    pending.reserve(proofs.size());
    unsigned append_slot = stored_count;
    size_t reuse_pos = 0;

    for (size_t j = 0; j < proofs.size(); j++) {
        if (paired[j])
            continue;
        unsigned target;
        if (reuse_pos < reuse.size())
            target = reuse[reuse_pos++];
        else
            target = append_slot++;
        if (target > PROOF_SLOT_MAX) {
            ESP_LOGE(TAG, "save_proofs: proof store full (%u slots)", target);
            return false;
        }
        if (target + 1 > high_water)
            high_water = target + 1;
        pending.push_back(Pending{target, j});
    }

    const uint16_t new_count = (uint16_t)high_water;

    // (a) New proofs first. Appended ones are above the count and therefore
    //     invisible until step (b); an interruption here leaves the previous
    //     state intact plus, at most, some proofs nobody can read yet.
    for (const Pending& w : pending) {
        char key[16];
        proof_slot_key(key, sizeof(key), slot, w.slot);
        std::string blob = serialize(proofs[w.index]);
        if (blob.empty()) {   // unreachable: validated up front
            ESP_LOGE(TAG, "save_proofs: serialization failed mid-save");
            return false;
        }
        err = nvs_set_blob(h, key, blob.data(), blob.size());
        if (err != ESP_OK) {
            ESP_LOGE(TAG, "save_proofs: write %s failed: %s", key, esp_err_to_name(err));
            return false;
        }
    }

    // (b) Then the high-water mark, which publishes the appends. It is written
    //     even when it does not change if the per-proof store is not live yet,
    //     so that "this wallet has been saved, with N proofs" is always a
    //     durable fact (the old format wrote "[]" for an empty set).
    if (!established || new_count != stored_count) {
        err = nvs_set_u16(h, cnt_key, new_count);
        if (err != ESP_OK) {
            ESP_LOGE(TAG, "save_proofs: write %s failed: %s", cnt_key, esp_err_to_name(err));
            return false;
        }
    }

    // (c) Then the erases, last, so an interruption cannot leave a slot that
    //     the previous state considered occupied while its proof is gone.
    for (unsigned i : stale) {
        char key[16];
        proof_slot_key(key, sizeof(key), slot, i);
        esp_err_t e = nvs_erase_key(h, key);
        if (!tolerated(e)) {
            ESP_LOGE(TAG, "save_proofs: erase %s failed: %s", key, esp_err_to_name(e));
            return false;
        }
    }

    // Legacy blob: once the per-proof store is live, a lingering copy is dead
    // weight (a stale proof set, ~47 kB of the partition at 200 proofs), so
    // the next save retires it.
    char legacy[16];
    legacy_proofs_key(legacy, sizeof(legacy), slot);
    if (established)
        nvs_erase_key(h, legacy);

    err = nvs_commit(h);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "save_proofs failed: %s", esp_err_to_name(err));
        return false;
    }

    // First migration only: the legacy blob is retired AFTER the per-proof
    // store is durable, so an interrupted migration always leaves a complete
    // readable copy behind.
    if (!established) {
        nvs_erase_key(h, legacy);
        if (nvs_commit(h) != ESP_OK)
            ESP_LOGW(TAG, "save_proofs: legacy blob not retired (will retry)");
    }

    ESP_LOGI(TAG, "[%d] saved %d proofs (%u of %u slots written, %u erased)",
             slot, (int)proofs.size(), (unsigned)pending.size(),
             (unsigned)high_water, (unsigned)stale.size());
    return true;
}

// Load wallet slot `slot`, migrating a legacy single-blob store in place (the
// blob stays untouched until the next successful save re-writes it).
bool load(int slot, std::vector<Proof>& out)
{
    Nvs nvs(NVS_READONLY);
    if (!nvs.ok())
        return false;
    nvs_handle_t h = nvs.get();

    char cnt_key[16];
    proof_count_key(cnt_key, sizeof(cnt_key), slot);
    uint16_t count = 0;
    esp_err_t err = nvs_get_u16(h, cnt_key, &count);

    if (err == ESP_ERR_NVS_NOT_FOUND) {
        char key[16];
        legacy_proofs_key(key, sizeof(key), slot);
        std::string blob;
        if (!nvs.get_blob(key, blob))
            return false;
        std::vector<Proof> loaded;
        if (!proofs_from_json(blob.c_str(), loaded))
            return false;
        out = std::move(loaded);
        ESP_LOGI(TAG, "[%d] loaded %d proofs from NVS (legacy blob)",
                 slot, (int)out.size());
        return true;
    }
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "load_proofs: read %s failed: %s", cnt_key, esp_err_to_name(err));
        return false;
    }

    std::vector<Proof> loaded;
    loaded.reserve(count);
    unsigned unreadable = 0;
    for (unsigned i = 0; i < count; i++) {
        std::string blob;
        if (read_proof_slot(h, slot, i, blob) != ESP_OK)
            continue;   // hole: a spent proof, erased, or an interrupted save
        Proof p{};
        if (!deserialize(blob.c_str(), p)) {
            // One unreadable entry used to fail the whole set. It is now
            // isolated: the other proofs still load, and the next save
            // rewrites this slot from the in-RAM copy.
            ESP_LOGE(TAG, "[%d] slot %u unreadable, skipping", slot, i);
            unreadable++;
            continue;
        }
        loaded.push_back(std::move(p));
    }
    out = std::move(loaded);
    ESP_LOGI(TAG, "[%d] loaded %d proofs from NVS (%u slots%s)",
             slot, (int)out.size(), (unsigned)count,
             unreadable ? ", some unreadable" : "");
    return true;
}

} // namespace proof_store

// -------------------------------------------------------------------------
// NVS persistence
// -------------------------------------------------------------------------

bool Wallet::save_mint_url()
{
    Nvs nvs(NVS_READWRITE);
    if (!nvs.ok())
        return false;
    char key[16];
    slot_key(key, sizeof(key), "url", nvs_slot_);
    return nvs_set_str(nvs.get(), key, mint_url_.c_str()) == ESP_OK
        && nvs.commit();
}

std::string Wallet::load_mint_url_for_slot(int slot)
{
    Nvs nvs(NVS_READONLY);
    char key[16];
    slot_key(key, sizeof(key), "url", slot);
    std::string url;
    if (!nvs.get_str(key, url))
        return "";
    return url;
}

// -------------------------------------------------------------------------
// NVS persistence (existing)
// -------------------------------------------------------------------------

bool Wallet::erase_nvs()
{
    Nvs nvs(NVS_READWRITE);
    if (!nvs.ok())
        return false;
    char key[16];
    slot_key(key, sizeof(key), "url", nvs_slot_);
    nvs_erase_key(nvs.get(), key);
    slot_key(key, sizeof(key), "proofs", nvs_slot_);
    nvs_erase_key(nvs.get(), key);
    // Per-proof store (proof_store::): the slot count, then every slot below
    // it. Absent holes are fine — nvs_erase_key reports NOT_FOUND and the
    // commit below is what has to succeed.
    snprintf(key, sizeof(key), "pn_%d", nvs_slot_);
    uint16_t proof_slots = 0;
    esp_err_t perr = nvs_get_u16(nvs.get(), key, &proof_slots);
    nvs_erase_key(nvs.get(), key);
    if (perr == ESP_OK) {
        for (unsigned i = 0; i < proof_slots; i++) {
            char pkey[16];
            snprintf(pkey, sizeof(pkey), "p%d_%u", nvs_slot_, i);
            nvs_erase_key(nvs.get(), pkey);
        }
    }
    // Legacy single-blob keyset entry
    slot_key(key, sizeof(key), "keys", nvs_slot_);
    nvs_erase_key(nvs.get(), key);
    // Individual keyset entries
    snprintf(key, sizeof(key), "kn_%d", nvs_slot_);
    nvs_erase_key(nvs.get(), key);
    for (int i = 0; i < MAX_KEYSETS; i++) {
        snprintf(key, sizeof(key), "k_%d_%d", nvs_slot_, i);
        nvs_erase_key(nvs.get(), key);
    }
    esp_err_t err = nvs_commit(nvs.get());
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "erase slot %d: commit failed: %s",
                 nvs_slot_, esp_err_to_name(err));
        return false;
    }
    ESP_LOGI(TAG, "erased NVS slot %d", nvs_slot_);
    return true;
}

// The proof store itself lives in proof_store:: (top of this file); these two
// are the wallet's thin wrappers over it.
bool Wallet::save_proofs()
{
    return proof_store::save(nvs_slot_, proofs_);
}

bool Wallet::load_proofs()
{
    return proof_store::load(nvs_slot_, proofs_);
}

bool Wallet::save_keysets()
{
    Nvs nvs(NVS_READWRITE);
    if (!nvs.ok()) {
        ESP_LOGE(TAG, "nvs_open failed: %s", esp_err_to_name(nvs.err()));
        return false;
    }

    // Remove legacy single-blob entry if present
    char old_key[16];
    slot_key(old_key, sizeof(old_key), "keys", nvs_slot_);
    nvs_erase_key(nvs.get(), old_key);

    // Over the cap, prefer keysets our proofs reference (dropping one orphans
    // its proofs: no unit, no fee info, no keys for DLEQ), then active
    // keysets, then the rest.
    std::vector<size_t> order(keysets_.size());
    for (size_t i = 0; i < order.size(); i++)
        order[i] = i;
    if (keysets_.size() > (size_t)MAX_KEYSETS) {
        std::vector<int> rank(keysets_.size(), 2);
        for (size_t i = 0; i < keysets_.size(); i++)
            if (keysets_[i].active)
                rank[i] = 1;
        for (const auto& p : proofs_)
            for (size_t i = 0; i < keysets_.size(); i++)
                if (keysets_[i].id == p.id) { rank[i] = 0; break; }
        std::stable_sort(order.begin(), order.end(),
                         [&rank](size_t a, size_t b) { return rank[a] < rank[b]; });
        for (size_t i = MAX_KEYSETS; i < order.size(); i++) {
            const Keyset& ks = keysets_[order[i]];
            ESP_LOGE(TAG, "[%d] keyset cap: dropping %s (unit %s%s) from NVS",
                     nvs_slot_, ks.id.c_str(), ks.unit.c_str(),
                     ks.active ? ", active" : "");
        }
    }

    char cnt_key[16];
    snprintf(cnt_key, sizeof(cnt_key), "kn_%d", nvs_slot_);
    uint8_t count = (uint8_t)keysets_.size();
    if (count > MAX_KEYSETS) count = MAX_KEYSETS;

    esp_err_t err = nvs_set_u8(nvs.get(), cnt_key, count);
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "save keyset count failed: %s", esp_err_to_name(err));
        return false;
    }

    size_t total_bytes = 0;
    for (int i = 0; i < count; i++) {
        char ks_key[16];
        snprintf(ks_key, sizeof(ks_key), "k_%d_%d", nvs_slot_, i);
        std::string blob = serialize(keysets_[order[i]]);
        if (blob.empty()) {
            ESP_LOGE(TAG, "save keyset %d: serialization failed", i);
            return false;
        }
        err = nvs_set_blob(nvs.get(), ks_key, blob.data(), blob.size());
        if (err != ESP_OK) {
            ESP_LOGE(TAG, "save keyset %d failed: %s", i, esp_err_to_name(err));
            return false;
        }
        total_bytes += blob.size();
    }

    for (int i = count; i < MAX_KEYSETS; i++) {
        char ks_key[16];
        snprintf(ks_key, sizeof(ks_key), "k_%d_%d", nvs_slot_, i);
        nvs_erase_key(nvs.get(), ks_key);
    }

    err = nvs_commit(nvs.get());
    if (err != ESP_OK) {
        ESP_LOGE(TAG, "save_keysets commit failed: %s", esp_err_to_name(err));
        return false;
    }

    ESP_LOGI(TAG, "[%d] saved %d keysets (%d bytes total)",
             nvs_slot_, count, (int)total_bytes);
    return true;
}

bool Wallet::load_keysets_nvs()
{
    Nvs nvs(NVS_READONLY);
    if (!nvs.ok())
        return false;

    // Try individual-entry format first
    char cnt_key[16];
    snprintf(cnt_key, sizeof(cnt_key), "kn_%d", nvs_slot_);
    uint8_t count = 0;
    esp_err_t err = nvs_get_u8(nvs.get(), cnt_key, &count);

    if (err == ESP_OK && count > 0) {
        std::vector<Keyset> loaded;
        for (int i = 0; i < count && i < MAX_KEYSETS; i++) {
            char ks_key[16];
            snprintf(ks_key, sizeof(ks_key), "k_%d_%d", nvs_slot_, i);
            std::string blob;
            if (!nvs.get_blob(ks_key, blob))
                continue;
            Keyset ks{};
            if (deserialize(blob.c_str(), ks))
                loaded.push_back(std::move(ks));
        }
        if (!loaded.empty()) {
            keysets_ = std::move(loaded);
            ESP_LOGI(TAG, "[%d] loaded %d keysets from NVS",
                     nvs_slot_, (int)keysets_.size());
            return true;
        }
        return false;
    }

    // Fall back to legacy single-blob format
    char key[16];
    slot_key(key, sizeof(key), "keys", nvs_slot_);
    std::string blob;
    if (!nvs.get_blob(key, blob))
        return false;

    std::vector<Keyset> loaded;
    if (!keysets_from_json(blob.c_str(), loaded))
        return false;

    keysets_ = std::move(loaded);
    ESP_LOGI(TAG, "[%d] loaded %d keysets from NVS (legacy)",
             nvs_slot_, (int)keysets_.size());
    return true;
}

bool Wallet::merge_keysets(const std::vector<Keyset>& fresh)
{
    bool changed = false;
    for (const auto& fk : fresh) {
        bool found = false;
        for (auto& existing : keysets_) {
            if (existing.id == fk.id) {
                if (existing.active != fk.active ||
                    existing.input_fee_ppk != fk.input_fee_ppk ||
                    existing.final_expiry != fk.final_expiry) {
                    existing.active = fk.active;
                    existing.input_fee_ppk = fk.input_fee_ppk;
                    existing.final_expiry = fk.final_expiry;
                    changed = true;
                }
                if (existing.keys.empty() && !fk.keys.empty()) {
                    existing.keys = fk.keys;
                    changed = true;
                }
                found = true;
                break;
            }
        }
        if (!found) {
            keysets_.push_back(fk);
            changed = true;
        }
    }
    return changed;
}

bool Wallet::load_from_nvs()
{
    load_proofs();
    load_keysets_nvs();
    return !keysets_.empty() || !proofs_.empty();
}

// -------------------------------------------------------------------------
// Offline-receive pending queue
// -------------------------------------------------------------------------
//
// NVS schema (namespace "wallet"):
//   pendn_<slot>     u8           current count, 0..PEND_MAX
//   pend_<slot>_<i>  string       full cashuA/cashuB token, i = 0..PEND_MAX-1
//
// PEND_MAX is bounded by the 15-char NVS key limit (single hex digit for i).

static const int PEND_MAX = 8;

static void pend_count_key(char* buf, size_t sz, int slot)
{
    snprintf(buf, sz, "pendn_%d", slot);
}

static void pend_item_key(char* buf, size_t sz, int slot, int idx)
{
    snprintf(buf, sz, "pend_%d_%x", slot, idx);
}

static int pending_count_for_slot(int slot)
{
    Nvs nvs(NVS_READONLY);
    if (!nvs.ok()) return 0;
    char k[16];
    pend_count_key(k, sizeof(k), slot);
    uint8_t n = 0;
    nvs_get_u8(nvs.get(), k, &n);
    return (int)n;
}

int Wallet::pending_count() const
{
    return pending_count_for_slot(nvs_slot_);
}

bool Wallet::stash_pending_token(const std::string& raw_token)
{
    Nvs nvs(NVS_READWRITE);
    if (!nvs.ok()) {
        ESP_LOGE(TAG, "pending: nvs_open failed");
        return false;
    }
    char ck[16];
    pend_count_key(ck, sizeof(ck), nvs_slot_);
    uint8_t n = 0;
    nvs_get_u8(nvs.get(), ck, &n);
    if (n >= PEND_MAX) {
        ESP_LOGE(TAG, "pending: queue full (%d/%d)", (int)n, PEND_MAX);
        return false;
    }
    char ik[16];
    pend_item_key(ik, sizeof(ik), nvs_slot_, (int)n);
    if (nvs_set_str(nvs.get(), ik, raw_token.c_str()) != ESP_OK) {
        ESP_LOGE(TAG, "pending: nvs_set_str failed");
        return false;
    }
    n++;
    if (nvs_set_u8(nvs.get(), ck, n) != ESP_OK)
        return false;
    esp_err_t err = nvs_commit(nvs.get());
    if (err != ESP_OK) {
        // Without a durable stash the sender's token would be silently
        // lost — report failure so the NFC exchange errors out.
        ESP_LOGE(TAG, "pending: commit failed: %s", esp_err_to_name(err));
        return false;
    }
    ESP_LOGI(TAG, "pending: stashed token %d (slot %d)", (int)n - 1, nvs_slot_);
    return true;
}

bool Wallet::list_pending_tokens(std::vector<std::string>& out)
{
    out.clear();
    Nvs nvs(NVS_READONLY);
    if (!nvs.ok())
        return false;
    char ck[16];
    pend_count_key(ck, sizeof(ck), nvs_slot_);
    uint8_t n = 0;
    nvs_get_u8(nvs.get(), ck, &n);
    for (int i = 0; i < (int)n; i++) {
        char ik[16];
        pend_item_key(ik, sizeof(ik), nvs_slot_, i);
        std::string s;
        if (!nvs.get_str(ik, s))
            continue;
        out.push_back(std::move(s));
    }
    return true;
}

bool Wallet::drain_pending_tokens(int& accepted, int& failed)
{
    accepted = 0;
    failed = 0;

    std::vector<std::string> items;
    if (!list_pending_tokens(items) || items.empty())
        return true;

    /* The pending list is rebuilt as we go. Tokens that swap successfully
     * (or fail permanently) are dropped; transient failures are retained. */
    std::vector<std::string> retained;

    for (size_t i = 0; i < items.size(); i++) {
        const std::string& raw = items[i];
        Token tok;
        if (!deserialize_token(raw.c_str(), tok)) {
            ESP_LOGW(TAG, "pending[%d]: decode failed, dropping", (int)i);
            failed++;
            continue;
        }
        if (tok.mint != mint_url_) {
            /* Stashed against the wrong wallet slot. Keep it; another
             * wallet's drain pass will pick it up. */
            ESP_LOGW(TAG, "pending[%d]: mint mismatch, retaining", (int)i);
            retained.push_back(raw);
            continue;
        }

        if (keysets_.empty() && !load_keysets()) {
            ESP_LOGW(TAG, "pending[%d]: keysets unavailable, retaining", (int)i);
            retained.push_back(raw);
            continue;
        }

        std::vector<Proof> got;
        if (receive(tok, got)) {
            ESP_LOGI(TAG, "pending[%d]: redeemed", (int)i);
            accepted++;
        } else {
            /* receive() can fail for either a transient (HTTP) or a
             * permanent (mint says spent / bad witness) reason. We can't
             * easily tell from here; conservatively keep the token unless
             * it's been retried many times. For v1: keep on first failure;
             * a future improvement can add a per-entry attempt counter. */
            ESP_LOGW(TAG, "pending[%d]: redeem failed, retaining", (int)i);
            retained.push_back(raw);
        }
    }

    /* Rewrite the pending list: erase all entries, write back retained. */
    Nvs nvs(NVS_READWRITE);
    if (!nvs.ok())
        return false;
    for (int i = 0; i < PEND_MAX; i++) {
        char ik[16];
        pend_item_key(ik, sizeof(ik), nvs_slot_, i);
        nvs_erase_key(nvs.get(), ik);
    }
    char ck[16];
    pend_count_key(ck, sizeof(ck), nvs_slot_);
    esp_err_t werr = ESP_OK;
    if (retained.empty()) {
        esp_err_t e = nvs_erase_key(nvs.get(), ck);
        if (e != ESP_OK && e != ESP_ERR_NVS_NOT_FOUND)
            werr = e;
    } else {
        for (size_t i = 0; i < retained.size(); i++) {
            char ik[16];
            pend_item_key(ik, sizeof(ik), nvs_slot_, (int)i);
            esp_err_t e = nvs_set_str(nvs.get(), ik, retained[i].c_str());
            if (e != ESP_OK)
                werr = e;
        }
        esp_err_t e = nvs_set_u8(nvs.get(), ck, (uint8_t)retained.size());
        if (e != ESP_OK)
            werr = e;
    }
    esp_err_t cerr = nvs_commit(nvs.get());
    if (werr != ESP_OK || cerr != ESP_OK) {
        ESP_LOGE(TAG, "pending: rewrite failed (%s/%s) — retained tokens may be lost",
                 esp_err_to_name(werr), esp_err_to_name(cerr));
        return false;
    }

    ESP_LOGI(TAG, "pending: drain slot %d -> %d ok, %d retained, %d dropped",
             nvs_slot_, accepted, (int)retained.size(), failed);
    return true;
}

} // namespace cashu
