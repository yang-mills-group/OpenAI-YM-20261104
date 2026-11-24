import YM.RG3.Forms.Rewrite
import YM.Corona.Halo

/-!
# Paying support realignment at one scale from canonical data

Keep *every* changed envelope on actual sets, including wrapping.
An unchanged mask discrepancy needn't pay the additional reserve; this
matters already for histories where p-bound only was issued. Deleted
regions, if any, need their own terms; this file only grows masks. Circle/halo
criterion is on actual torus (`Corona.tile`, hence no unwrap assumption or
volume dependence in this cost). Press uses a stronger exponent still on
hard letters; supply that separately. No analytic estimates in offset.
These are costs at fixed p, threshold as in P.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG3.Review
open RG RG3.Forms RG3.Press Lattice Wilson Finset Function MeasureTheory Marker Ac Push.Corrected Push.AbsoluteSums
open Extra.Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge}
variable {p : BudgetPoint} {S T : Support n}

section Masks
variable {E : Type*} {f : Config G n → E}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

lemma enlarge (h : p.Regular S f) (hs : S⊆T) : p.Regular T f :=
  ⟨fun _ _ hv => h.sites _ _ (agrees_mono hv (Finset.coe_subset.mpr hs)),h.borel,h.symmetry,
    fun U hf => h.smooth U (Finset.disjoint_of_subset_left hs hf),
    fun U hf => h.hasDerivs U (Finset.disjoint_of_subset_left hs hf)⟩
omit [MeasurableSpace E] in
lemma carry {o a} (h : p.supBounds o S f a) (hs : S⊆T) : p.supBounds o T f a :=
  ⟨h.1,fun U hf => h.2 U (Finset.disjoint_of_subset_left hs hf)⟩

def wrung (S T : Support n) (t : ℝ) (f : Config G n → E) (U : Config G n) := masked t S f U - masked t T f U


def tides (S T : Support n) (a : ℝ) := if S=T then 0 else a

lemma discipline [MeasurableSub₂ E] (h : p.Regular S f) (hs : S ⊆ T) :
    GaugeInvariant (wrung S T p.threshold f) ∧ Measurable (wrung S T p.threshold f) ∧
      UsesFinal p.threshold T (wrung S T p.threshold f) ∧
      (∀ U, wrung S T p.threshold f U ≠ 0 → ¬ Healthy p.threshold T U) := by
  have he (D : Support n) (hL : LocalOn D f) : UsesFinal p.threshold D (masked p.threshold D f) := by
    intro U V hu H
    have he : Healthy p.threshold D U ↔ Healthy p.threshold D V := by simp only [Healthy,Finset.disjoint_iff_inter_eq_empty,H]
    by_cases h : Healthy p.threshold D U
    · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ (he.mp h)]; exact hL _ _ hu
    rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ (mt he.mpr h)]
  have hq (D : Support n) k U : masked p.threshold D f (gauge k U) = masked p.threshold D f U := by
    have he : Healthy p.threshold D (gauge k U) ↔ Healthy p.threshold D U := by simp only [Healthy,gauge_flags]
    by_cases h' : Healthy p.threshold D U
    · rw [masked_eq _ _ _ _ (he.mpr h'),masked_eq _ _ _ _ h']; exact h.symmetry k U
    rw [masked_ne _ _ _ _ (mt he.mp h'),masked_ne _ _ _ _ h']
  refine ⟨fun k U => ?_, (masked_measurable _ _ _ h.borel).sub (masked_measurable _ _ _ h.borel), fun U V hu H => ?_,
    fun U hh hX => ?_⟩
  · unfold wrung; rw [hq,hq]
  · unfold wrung; rw [he T (enlarge h hs).sites U V hu H,Work.H03.reads_larger hs (he S h.sites) U V hu H]
  exact hh (by rw [wrung,masked_eq _ _ _ _ (Finset.disjoint_of_subset_left hs hX),masked_eq _ _ _ _ hX,sub_self])

omit [MeasurableSpace E] in
lemma slim (hS : S⊆T) {o a} (h : p.supBounds o S f a) (U) : ‖wrung S T p.threshold f U‖ ≤ tides S T a := by
  unfold wrung tides; split
  next he => rw [he,sub_self,norm_zero]
  by_cases hX : Healthy p.threshold T U
  · rw [masked_eq _ _ _ _ hX,masked_eq _ _ _ _ (Finset.disjoint_of_subset_left hS hX),sub_self,norm_zero]; exact h.1
  rw [masked_ne _ _ _ _ hX,sub_zero]
  by_cases hO : Healthy p.threshold S U
  · rw [masked_eq _ _ _ _ hO]; exact h.2 U hO [] (Nat.zero_le _) (by simp)
  rw [masked_ne _ _ _ _ hO,norm_zero]; exact h.1
end Masks

section Area
variable {B : ℕ} {a u C : ℝ}

lemma tides_pay {x : ℝ} (_hC : 0 ≤ C) (hx : 0 ≤ x)
    (h : S ≠ T → a*(coverNumber B T:ℕ) ≤ C+u*coverNumber B S) :
    tides S T x * Real.exp (a*coverNumber B T) ≤ Real.exp C * (x * Real.exp (u*coverNumber B S)) := by
  unfold tides; split
  · rw [zero_mul]; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg hx (Real.exp_pos _).le)
  next ht =>
    exact (mul_le_mul_of_nonneg_left (Real.exp_monotone (h ht)) hx).trans_eq (by rw [Real.exp_add]; ring)

variable {α V : Type*} [Fintype V] [DecidableEq V]
variable {X Y : α → Support n} {o : V → Site n} {μ : ℕ} {tags : α→Finset V} (k : α → ℝ) (r : α → ℝ)

lemma tides_hit (hk : ∀ i,0≤k i) (hw : ∀ i,0 ≤ r i) (hc : 0 ≤ C)
    (hP : ∀ i,X i ⊆ Y i) (hp : ∀ i, ∃ z∈tags i,o z ∈ X i)
    (H : ∀ i, X i ≠ Y i → (a+1)*coverNumber B (Y i) ≤ C + u*coverNumber B (X i))
    {b : ℝ} (hb : 0 ≤ b) (hO : Occupancy o μ) (ha : Rooted tags X B u (fun i => r i*k i) b) :
    Hit Y B (fun i => r i*tides (X i) (Y i) (k i)) a ((μ:ℝ)*siteFactor B*(Real.exp C*b)) := by
  classical
  apply root_hit hO
  · intro i; apply mul_nonneg (hw i); unfold tides; split; exact le_rfl; exact hk i
  · exact mul_nonneg (Real.exp_pos _).le hb
  · intro i _; obtain ⟨z,hz,hx⟩ := hp i; exact ⟨z,hz,hP i hx⟩
  intro z
  refine budget_mono (budget_scale (Real.exp_pos C).le (ha z)) (fun i => ?_) (fun i => ?_)
  · split
    · apply mul_nonneg (Real.exp_pos _).le (mul_nonneg (hw i) ?_); unfold tides; split; exact le_rfl; exact hk i
    exact le_rfl
  -- avoid Classical.propDecidable
  split_ifs
  · simpa only [mul_left_comm, mul_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left (tides_pay hc (hk i) (H i)) (hw i)
  simp

/-- Example for short hulls of diameter rc on the ACTUAL geometry.
On longer paths need thin support charge instead of this. -/
lemma halos_pay (hB : 0<B) (m : ℕ) (x : Site n) (h : S=T ∨ T ⊆ halo (m*B) {x}) (ha : 0 ≤ a) (hu : 0 ≤ u) :
    S ≠ T → a*coverNumber B T ≤ a*((m+m+1)^4:ℕ) + u*coverNumber B S := by
  intro hc; refine (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ((Corona.cover_mono (h.resolve_left hc) B).trans
    (Corona.tile x m B hB))) ha).trans (le_add_of_nonneg_right (by positivity))

end Area
end YM.RG3.Review
