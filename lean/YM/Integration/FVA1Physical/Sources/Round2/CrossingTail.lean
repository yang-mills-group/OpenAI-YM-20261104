import YM.Integration.FVA1Physical.Sources.Round2.CrossingBoxes
import YM.Push.GRID_APPROXIMATION.Hit

/-! Crossing forced entries have an exponential tail in their connected cover
number. A radius equal to the cover radius in lattice-distance units is paid
explicitly. All remaining support weight is retained. -/

namespace YM.LocalLTE.Sail.Round2

open Lattice RG Wilson Source Marker MergeProof MergeProof.Accent Overlay Push.AbsoluteSums
open Push.GridApprox.Attach
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {I : Type} [DecidableEq I] {B : Census I}

theorem cover_of_flag_outside {a r : ℕ} {X S : Support n} {o z : Site n}
    (ho : o ∈ X) (hs : o ∈ S) (hz : z ∈ X) (hout : z ∉ halo (r * leg a) S) :
    r ≤ coverNumber a X := by
  have hsep : r * leg a ≤ separation z o := le_of_not_ge fun h =>
    hout (halo_spec.mpr ⟨o, hs, (separation_comm o z).le.trans h⟩)
  calc
    r = (r * leg a) / leg a := (Nat.mul_div_cancel r (leg_pos _)).symm
    _ ≤ separation z o / leg a := Nat.div_le_div_right hsep
    _ ≤ _ := distance_charge X a z o hz ho

private theorem tailCharge {e σ x y : ℝ} {r m : ℕ}
    (hσ : 0 ≤ σ) (hm : r ≤ m) (hxy : x ≤ y) (hy : 0 ≤ y) :
    Real.exp ((e - σ) * m) * x ≤ Real.exp (-σ * r) * (Real.exp (e * m) * y) := by
  rw [← mul_assoc, ← Real.exp_add]
  apply (mul_le_mul_of_nonneg_left hxy (Real.exp_nonneg _)).trans
  apply mul_le_mul_of_nonneg_right _ hy
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hm : (r : ℝ) ≤ m) hσ]

private theorem activeCover (P : Rep G n) (S : Support n) (U : Config G n)
    {j r : ℕ} {o : Site n} (horg : o ∈ S) (ho : o ∈ (P.activities.forced j).support)
    (hU : Healthy P.p.threshold (halo (r * leg P.p.B) S) U)
    (he : (P.activities.forced j).eligible P.p.threshold U) :
    r ≤ coverNumber P.p.B (P.activities.forced j).support := by
  obtain ⟨z, hz⟩ := (P.activities.forced j).inventory_ne
  obtain ⟨hx, hflag⟩ := Finset.mem_inter.mp (he.1.symm ▸ hz)
  exact cover_of_flag_outside ho horg hx fun h => Finset.disjoint_left.mp hU h hflag

/-- Full mixed marked table on an anchored healthy field. The estimate is
rooted at each mark and holds for arbitrary finite subsets of all forced
rows. The reserve sigma pays the distant flag, leaving exponent e-sigma. -/
theorem mixedCrossingTail (P : Rep G n) (a : Bands B P) (hA : a.Active)
    (w : I → ℝ) {u c d b : ℝ} (h : a.Radial w u c d b)
    (S : Support n) (j : I) (ho : a.origins j ∈ S)
    (U : Config G n) (r : ℕ) (hU : Healthy P.p.threshold (halo (r * leg P.p.B) S) U)
    (σ : ℝ) (hσ : 0 ≤ σ) :
    SumBudget (fun k : ℕ × ℕ => if j ∈ (a.marks k.1 k.2).val then
      Poly.toll w (a.marks k.1 k.2) *
        (Real.exp ((P.p.supportExponent - σ) * coverNumber P.p.B (P.activities.forced k.1).support) *
          ‖a.entries k.1 k.2 U‖) else 0) (Real.exp (-σ * r) * (d * b)) := by
  obtain ⟨t, ht, hb⟩ := h.hits
  apply budget_mono (budget_scale (Real.exp_pos (-σ * r)).le (hb j))
  · intro k
    split
    · exact mul_nonneg (Poly.worth h.pure _).le (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    · exact le_rfl
  intro k
  by_cases hj : j ∈ (a.marks k.1 k.2).val
  · simp only [if_pos hj]
    by_cases hz : a.entries k.1 k.2 U = 0
    · rw [hz, norm_zero, mul_zero, mul_zero]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Poly.worth h.pure _).le
        (mul_nonneg (Real.exp_pos _).le (ht ..).1))
    have hhome := hA.retained _ _ (fun hn => hz (congrFun hn U)) j hj
    have hcov := activeCover P S U ho hhome hU (hA.keeps _ _ U hz)
    exact (mul_le_mul_of_nonneg_left
      (tailCharge hσ hcov ((ht k.1 k.2).2 U) (ht k.1 k.2).1) (Poly.worth h.pure _).le).trans_eq
        (mul_left_comm ..)
  simp [hj]

theorem singleCrossingTail (P : Rep G n) {d : ℕ} {F : Labels.Frame G d} (W : Coefficient F n)
    {o : Site n} {a : Hol G} (hF : W.Format o a P) {κ E : ℝ}
    (h : W.remBound o P κ E) (S : Support n) (ho : o ∈ S)
    (U : Config G n) (r : ℕ) (hU : Healthy P.p.threshold (halo (r * leg P.p.B) S) U)
    (σ : ℝ) (hσ : 0 ≤ σ) :
    SumBudget (fun k : ℕ =>
      Real.exp ((P.p.supportExponent - σ) * coverNumber P.p.B (P.activities.forced k).support) *
        ‖W.forced k U‖) (Real.exp (-σ * r) * (κ * E)) := by
  obtain ⟨a₀, b, ha, _, hab, hκ, _, t, ht, hb⟩ := h
  have bound := budget_scale (Real.exp_pos (-σ * r)).le ht
  have h' : SumBudget (fun k : ℕ => Real.exp ((P.p.supportExponent - σ) *
      coverNumber P.p.B (P.activities.forced k).support) * ‖W.forced k U‖)
      (Real.exp (-σ * r) * (κ * b)) := by
    apply budget_mono bound (fun _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    intro k
    by_cases hz : W.forced k U = 0
    · rw [hz, norm_zero, mul_zero]
      exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hb k).1)
    have hcov := activeCover P S U ho (hF.carried k (fun hn => hz (congrFun hn U))) hU
      (hF.forcing k U hz)
    exact tailCharge hσ hcov ((hb k).2 U) (hb k).1
  exact ⟨h'.1, h'.2.1, h'.2.2.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (by linarith only [ha, hab]) hκ.le) (Real.exp_pos _).le)⟩

end YM.LocalLTE.Sail.Round2
