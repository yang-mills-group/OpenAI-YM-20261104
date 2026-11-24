import YM.RG17.Pitch
import YM.RG17.Gathers
import YM.SharpGram.Weak.Bill
/-!
# Price beads across levels both born in history. Still physical.

Stronger than just RateLE spatial. Used for moving Length map,
not same as converting actual reports from one level to another
(coefficients would have distinct norm bill and profile payments).
Supports at finite cutoff and charts on full alphabet. Constants
completely explicit before spending powers of coupling.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set Filter Spec Extraction Table OPE OPE.Orbits SharpGram Trace RG12 Next.UVStress
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{S:Table C.book}{f:Extraction.Order}{F:Final C f S}
   (L:Layout F)(E:Services C f S) {d k m:ℕ} {D:ℝ}
set_option quotPrecheck false
local notation "a"=> C.S.a
local notation "M"=> L.charts
variable (he:C.S.a k / C.S.a m ≤ D) (hd:1≤D)
include E he hd
lemma podQuota (hc:C.Makes) (v:C.label d) {i:UVIndex} (hk:C.ref d ≤ k) (hm:C.ref d ≤ m)
   (hv:k ≤ i.1)(hw:m ≤ i.1):
     quota C d m i.1 i.2 v ≤ (a m / a k)^d * D^(d+1)* quota C d k i.1 i.2 v := by
   obtain ⟨W,r,D',hp⟩:= E.purchase
   let T:= hp.toTableTickets
   have ha:= C.S.a_pos k; have hb:= C.S.a_pos m
   let t:= a k/a m; have ht:0<t:=div_pos ha hb
   rcases le_total m k with hh|hh
   · exact (passPrice T v hm hh hv).trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (pow_nonneg (div_nonneg hb.le ha.le) _) (one_le_pow₀ hd)) (quota_nonneg _))
   apply (Weak.Portfolio.reverseWalk (H:=hc) T v hk hh hw).trans
   refine mul_le_mul_of_nonneg_right ?_ (quota_nonneg _)
   have hz : t^(d+1)≤ D^(d+1):=pow_le_pow_left₀ ht.le he _
   rw [show a m/a k=t⁻¹ from (inv_div _ _).symm, inv_pow,inv_mul_eq_div,le_div_iff₀ (pow_pos ht _)]
   exact (pow_succ' t d).symm ▸ hz
private abbrev funds {G:Gauge}(C:Family G)(k d:ℕ):ℂ:=↑(C.S.a k^d)
omit E he hd in
private lemma costsAt (hc:C.Makes){i:UVIndex}(v:C.label d)(hk:C.ref d ≤ k)(hw:k ≤ i.1) : quota C d k i.1 i.2 (funds C k d • atK C hc d k i v)= a k^d * mass C d v:= by
   rw [quota_smul, quota_atK, funds,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (C.S.a_pos _).le _)] <;> assumption -- order inspect
/-- pre-limit, UNCHANGED reference tag. For shifted alphabets pay mass AFTER the shift in
coupling copies. Target seat w can vary with i. -/
lemma podPermit (hc:C.Makes) (v:C.label d){i:UVIndex} (hk:C.ref d ≤ k) (hm:C.ref d ≤ m)
   (hv:k ≤ i.1)(hw:m ≤ i.1): ∃ w:C.label d, mass C d w ≤ D^(d+1)*mass C d v ∧
      ((a m^d:ℝ):ℂ) • atK C hc d m i w=((a k^d:ℝ):ℂ) • atK C hc d k i v:=by
   let s:=funds C k d; let t:= funds C m d
   have ha:=pow_pos (C.S.a_pos k) d; have hb:=pow_pos (C.S.a_pos m) d; have ht:t≠0:= by unfold t funds; exact_mod_cast hb.ne'
   let q:=s • atK C hc d k i v
   let w:= t⁻¹ • charts C hc d m i q
   have hh : t • atK C hc d m i w=q:= by
       unfold w; rw [map_smul,smul_smul,mul_inv_cancel₀ ht,one_smul]; exact LinearEquiv.symm_apply_apply ..
   refine ⟨w,?_ ,hh⟩
   have he:= podQuota E he hd hc q hk hm hv hw
   rw [← mul_le_mul_iff_right₀ hb,← mul_assoc] -- inspect
   calc
     _ = quota C d m i.1 i.2 q:= hh ▸ (costsAt hc w hm hw).symm -- rewriting direction
     _ ≤ _ := he
     _ = _ := by unfold q; rw [costsAt hc v hk hv,div_pow]; field_simp
-- Limit columns at M fixed. Also FULL alphabet, may not be injected at S.
lemma podPass (v:C.label d)(hk:C.ref d ≤ k)(hm:C.ref d ≤ m):
    ∃ w:C.label d, mass C d w ≤ D^(d+1)*mass C d v ∧ ((a m^d:ℝ):ℂ) • M d m w = ((a k^d:ℝ):ℂ) • M d k v:=by
   let s:=funds C k d; let t:= funds C m d
   let hc:= F.room.cutoff; letI:= L.notbot
   have ha:=pow_pos (C.S.a_pos k) d; have hb:=pow_pos (C.S.a_pos m) d; have ht:t≠0:= by unfold t funds; exact_mod_cast hb.ne'
   let q (i:UVIndex):= atK C hc d k i (s • v)
   have hz:Tendsto q L.lens (𝓝 (s • M d k v)):=by
       rw [← map_smul]; exact L.observes.columns d k hk _ le_rfl
   have hu: ∀ᶠ i in L.lens, quota C d m i.1 i.2 (q i) ≤ a m^d * (D^(d+1)*mass C d v):=by
       filter_upwards [L.observes.grows.eventually_ge_atTop k, L.observes.grows.eventually_ge_atTop m] with i hv hw
       exact (podQuota E he hd hc (q i) hk hm hv hw).trans_eq (by unfold q; rw [map_smul,costsAt hc v hk hv, div_pow]; field_simp)
   obtain ⟨w,hy,hw⟩:= L.observes.value d m hm le_rfl _ _ _ hu hz
   refine ⟨t⁻¹ • w, ?_,?_⟩
   · rw [show mass _ _ (t⁻¹ • w)=‖t⁻¹‖ *mass C d w from ?_]; rotate_left
     · unfold mass Labels.Frame.coeffSize; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _=> norm_smul t⁻¹ (w i) -- fix namespace
     rw [norm_inv]; unfold t funds; rw [Complex.norm_real,Real.norm_of_nonneg hb.le]
     exact (mul_le_mul_of_nonneg_left hw (inv_pos.mpr hb).le).trans_eq (by field_simp)
   change t • _= s • _; rw [map_smul,smul_smul,mul_inv_cancel₀ ht,one_smul,← hy]
lemma tread (v:C.label d) (hk:C.ref d ≤ k) (hm:C.ref d ≤ m) : ∃ w:C.label d,mass C d w ≤ D^(d+1)*mass C d v∧
    engineering (S:=S) L.charts d m w = engineering L.charts d k v :=by
   obtain ⟨w,hx,hh⟩:= podPass L E he hd v hk hm
   exact ⟨w,hx,by rw [engineering_at,engineering_at, ← map_smul (S.project d), ← map_smul (S.project d),hh]⟩
end YM.RG17
