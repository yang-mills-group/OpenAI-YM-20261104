import YM.GradedFar.Demand
import YM.GradedFar.Operands
/-!
# Applying K_{η} in the graded basis at all needed orders

This expands the Far fields of the two measurements of (M.2) *as defined*,
with exact formal identities (no loss from Taylor re-expression). In particular the
common power `T^W` *factors out* of each multi-column. We do not use inverse changes of a Far
argument, nor a backward dilation law on one of the series. The Law used here at η is the one
with the engineering powers as in `Scale.Facets.scale_at`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar
open Function Filter Set PowerSeries
open XSpace XSpace.Normalize XSpace.Structure1 Scale
open Dframe O.Score O.Enh
open scoped Topology BigOperators Classical

variable {G : Gauge} {n m l h : ℕ}
    {A : Arenas G} {ψ : ℝ → PowerSeries ℂ} {F : ℝ → Frames G} (law : Scale.Law A ψ F)
    (η : ℝ)

def kCue (F : ℝ → Frames G) (η : ℝ) (p q : Q G) := Acres η (heft p) * cue (seats (F η)) p q

include law
lemma cap_conversion (p : Q G) (hp : heft p ≤ h) (k : ℕ) :
    coeff k (conversion F η h) (cap p hp) =
      ∑ i : Grade G (heft p), coeff k (kCue F η p (own i)) • cap (own i) (d:=h) hp := by
  rw [coeff_conversion, cap_map (O.Score.slot law η), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kCue, Acres, coeff_C_mul, _root_.map_smul,
    show Level.Dial h η (cap (own i) hp) = _ from Level.exact₀ η (low (own i) hp),
    low_size, O.Score.season, smul_smul]
  rw [mul_comm]

lemma cap_conversion_factor (t : ℝ) (ht : 0 < t) (p : Q G) (hp : heft p ≤ h) (k : ℕ) :
    coeff k (conversion F (-Real.log t) h) (cap p hp) =
      (t:ℂ) ^ heft p • ∑ i : Grade G (heft p), coeff k (cue (seats (F (-Real.log t))) p
        (own i)) • cap (own i) (d:=h) hp := by
  rw [cap_conversion law, Finset.smul_sum]; simp_rw [kCue, Acres, coeff_C_mul, ← O.Score.season,
    Extent.token, neg_neg, Real.exp_log ht, smul_smul]

-- For auditing unit/cap behavior of the conversion
lemma conversion_leaf (k : ℕ) : coeff k (conversion F η h) (leaf G h) = if k=0 then leaf G h else 0 := by
  rw [coeff_conversion]; split_ifs with hk
  · subst k; rw [(law.paid η h).zero, Module.End.one_apply, Level.Dial_leaf]
  rw [show coeff k (F η h) (leaf G h) = 0 from ((law.paid η h).high k hk).1, map_zero]

lemma conversion_caps (hhl : h ≤ l) : Walk hhl (conversion F η h) (conversion F η l) := by
  intro i p
  rw [coeff_conversion, coeff_conversion, law.continues η hhl, Level.chain]

/-- Unit-cost (up to polynomial in log T) of the unscaled factor in `cap_conversion_factor`. -/
lemma charge_cue (p q : Q G) (d : ℕ) {I : Type} :
    ChargeP d 0 (fun (_ : I) s => cue (seats (F (-s))) p q) :=
  ChargeP.town (O.Enh.Uniform.flips (rhythm_v law)) p q

omit law in
def kPlay (F : ℝ → Frames G) (η : ℝ) (p q : Scan G m) := ∏ i, kCue F η (p i) (q i)

omit law in
lemma kPlay_factor (F : ℝ → Frames G) (p q : Scan G m) :
    kPlay F η p q = Acres η (totalG p) * play (seats (F η)) p q := by
  unfold kPlay kCue Acres play; rw [Finset.prod_mul_distrib, ← map_prod]
  simp_rw [← O.Score.season]; rw [O.Score.priced, ← O.Score.season]

omit law in
lemma kPlay_at_T (F : ℝ → Frames G) (t : ℝ) (ht : 0 < t) (p q : Scan G m) :
    kPlay F (-Real.log t) p q = PowerSeries.C ((t:ℂ) ^ totalG p) *
      play (seats (F (-Real.log t))) p q := by
  rw [kPlay_factor, Acres, ← O.Score.season, Extent.token, neg_neg, Real.exp_log ht]

/-! Use negative exponent in `ChargeP` for a *growth* cost. -/
theorem charge_play (p q : Scan G m) (d : ℕ) {I : Type} : ChargeP d (-(totalG p : ℝ))
    (fun (_ : I) s => kPlay F (-s) p q) := by
  simp_rw [kPlay_factor]
  have hp : ChargeP d 0 (fun (_ : I) s => play (seats (F (-s))) p q) :=
    ChargeP.extreme (O.Enh.Uniform.flips (rhythm_v law)) p q
  simpa only [add_zero] using (ChargeP.joint (n:=d)
    (show ChargeP d (-(totalG p : ℝ)) (fun (_ : I) s => Acres (-s) (totalG p)) from reflectV) hp)

variable {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : Through l d) (he : Through l e)
lemma far_alloc (f : MultilinearMap ℂ (fun i => Sec G (e i)) ℂ)
    (v : Scan G m) (hv : InCaps e v) (k : Fin m → ℕ) :
    f (fun i => coeff (k i) (conversion F η (e i)) (loadScan v hv i)) =
      ∑ j : LivesP v, (∏ i, coeff (k i) (kCue F η (v i) (decode v j i))) *
        f (loadScan (decode v j) (stillInCaps j hv)) := by
  unfold loadScan; simp_rw [cap_conversion law]
  rw [f.map_sum]; exact Finset.sum_congr rfl fun j _ => f.map_smul_univ _ (loadScan (decode v j) (stillInCaps j hv))

theorem fullSeries_expansion (H : Regular A) (x : Points n) (y : Points m)
    (u : Scan G n) (v : Scan G m) (hu : InCaps d u) (hv : InCaps e v) :
    fullSeries A F η hd he x y (loadScan u hu) (loadScan v hv) =
      ∑ j : LivesP v, kPlay F η v (decode v j) * party (install A) x
        (squeeze η y) u (decode v j) := by
  ext k
  rw [fullSeries, coeff_mk, withFar_apply, map_sum]
  simp_rw [kPlay, Dframe.Constants.admits, far_alloc law η]
  rw [Finset.sum_comm]; simp_rw [rawCoeff_on_scan _ H]

lemma replacementSeries_expansion (H : Regular A) (hh : h ≤ l) (y : Points m)
    (q : Q G) (v : Scan G m) (hq : heft q ≤ h) (hv : InCaps e v) :
    replacementSeries A F η hh he y (cap q hq) (loadScan v hv) =
      ∑ j : LivesP v, kPlay F η v (decode v j) * lonelyG (install A)
        (squeeze η y) q (decode v j) :=
  fullSeries_expansion law η (d:=Output h) (fun _ => hh) he H (0 : Points 1) y (Single q) v
    (fun _ => hq) hv

end YM.FVA2.GradedFar
