import YM.Integration.FiniteTensorProgramCost
import YM.Integration.VacuumShardCount
import YM.Integration.ActualAnchoredGround

/-!
# A fixed-order polynomial bound for the original centered vacuum sum

The native degree-j generator keeps its negative sign and its j! multiplier.
Only the norm removes the sign. The outer 1/n! is retained explicitly in the
order-dependent constant. All original shards, slot patterns and ordered
pairing-program occurrences remain in the estimate.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Integration.FiniteVacuumProgramBound

open Finset Function
open YM.Marker YM.Multi YM.Next.Rank
open YM.Comparison.RG02 YM.Comparison.RG02.Order
open YM.Comparison.RG02.Sky
open YM.Integration.PatternTensorRows
open YM.Integration.PatternConnectedProgram
open YM.Integration.PhysicalProgramRoot
open YM.Integration.NativeTensorBound (treeEdges)
open scoped BigOperators Classical

variable {I X : Type} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The original factorial-normalized real derivative, before the generator j!. -/
def normalizedValue (e : X) (L : (I → ℝ) →ₗ[ℝ] X)
    (M : (Unit → ℝ) →ₗ[ℝ] X) (f : X → ℝ) (j : ℕ)
    (p : Fin (j + 2) → Kind) (z : State p I Unit) : ℂ :=
  tensorValue e L M
    (Complex.ofRealCLM.compContinuousMultilinearMap (Tensor.coeff f (j + 2) 0))
    ⟨p, z⟩

/-- The two exact one-port prices needed after fixing the slot pattern.
The physical direction is already the original Unit-ray map M. -/
structure PatternPrice (e : X) (L : (I → ℝ) →ₗ[ℝ] X)
    (M : (Unit → ℝ) →ₗ[ℝ] X) (f : X → ℝ)
    (n : ℕ) (A D : ℝ) : Prop where
  physical : ∀ j, 0 < j → j ≤ n → ∀ p : Fin (j + 2) → Kind,
    External p → (∑ z : State p I Unit, ‖normalizedValue e L M f j p z‖) ≤
      A * D ^ Fintype.card (External p)
  gaussian : ∀ j, 0 < j → j ≤ n → ∀ (p : Fin (j + 2) → Kind)
    (u : Internal p) (i : I),
    (∑ z : State p I Unit,
      if z.1 u = i then ‖normalizedValue e L M f j p z‖ else 0) ≤
        A * D ^ Fintype.card (External p)

/-- Every original vacuum generator scalar and its sign are still present. -/
def family {V : Type} (f : X → ℝ) (d : V → ℕ) (v : V) :
    Σ m, Tensor.T X ℂ m :=
  ⟨d v + 2, ((d v).factorial : ℂ) •
    (-Complex.ofRealCLM.compContinuousMultilinearMap (Tensor.coeff f (d v + 2) 0))⟩

def vertexPrice {V : Type} (d : V → ℕ) (p : ∀ v, Fin (d v + 2) → Kind)
    (A D : ℝ) (v : V) : ℝ :=
  ((d v).factorial : ℝ) * A * D ^ Fintype.card (External (p v))

def patternCost (n : ℕ) (A B D : ℝ) : ℝ :=
  (((3 * n + 1) ^ (3 * n) : ℕ) : ℝ) *
    (n.factorial : ℝ) ^ n * A ^ n * B ^ (3 * n) * D ^ (3 * n)

/-- This constant depends only on the fixed perturbative order. -/
def orderConstant (n : ℕ) : ℝ :=
  (n.factorial : ℝ)⁻¹ *
    ((2 ^ (2 ^ n) * 3 ^ (3 * n) * (3 * n + 1) ^ (3 * n) : ℕ) : ℝ) *
      (n.factorial : ℝ) ^ n

section FiniteFamily

variable {V : Type} [Fintype V] [DecidableEq V]
variable (e : X) (L : (I → ℝ) →ₗ[ℝ] X) (M : (Unit → ℝ) →ₗ[ℝ] X)
variable (f : X → ℝ) (d : V → ℕ)

omit [Fintype I] [Fintype V] [DecidableEq V] in
private lemma norm_vertex (p : Patterns (family f d)) (v : V)
    (z : State (p v) I Unit) :
    ‖vertexValue e L M (family f d) (fun _ => 1) p v z‖ =
      ((d v).factorial : ℝ) * ‖normalizedValue e L M f (d v) (p v) z‖ := by
  simp [vertexValue, family, tensorValue, normalizedValue, physicalWeight,
    smul_eq_mul]
  exact Or.inl (Complex.norm_real _)

omit [DecidableEq V] in
private lemma physical_slots_le (p : Patterns (family f d)) (N : ℕ)
    (hN : (∑ v, (d v + 2)) ≤ N) :
    (∑ v, Fintype.card (External (p v))) ≤ N := by
  apply le_trans (Finset.sum_le_sum ?_) hN
  intro v _
  exact (Fintype.card_le_of_injective (fun k : External (p v) => k.val)
    Subtype.val_injective).trans_eq (Fintype.card_fin (d v + 2))

omit [DecidableEq V] in
private lemma gaussian_slots_le (p : Patterns (family f d)) (N : ℕ)
    (hN : (∑ v, (d v + 2)) ≤ N) :
    Fintype.card (Σ v, Internal (p v)) ≤ N := by
  rw [Fintype.card_sigma]
  apply le_trans (Finset.sum_le_sum ?_) hN
  intro v _
  exact (Fintype.card_le_of_injective (fun k : Internal (p v) => k.val)
    Subtype.val_injective).trans_eq (Fintype.card_fin (d v + 2))

private lemma same_card {α : Type*} (a b : Fintype α) :
    @Fintype.card α a = @Fintype.card α b := by
  cases Subsingleton.elim a b
  rfl

omit [DecidableEq V] in
private lemma product_price_bound (p : Patterns (family f d)) (n : ℕ)
    (A D : ℝ) (hA : 1 ≤ A) (hD : 1 ≤ D)
    (hd : ∀ v, d v ≤ n) (hv : Fintype.card V ≤ n)
    (hs : (∑ v, (d v + 2)) ≤ 3 * n) :
    (∏ v, vertexPrice d p A D v) ≤
      (n.factorial : ℝ) ^ n * A ^ n * D ^ (3 * n) := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hF : (1 : ℝ) ≤ n.factorial := by
    exact_mod_cast (show 1 ≤ n.factorial from Nat.factorial_pos n)
  have hf : (∏ v, ((d v).factorial : ℝ)) ≤ (n.factorial : ℝ) ^ n := by
    calc
      _ ≤ ∏ _v : V, (n.factorial : ℝ) := by
        apply Finset.prod_le_prod
        · intro v _; positivity
        · intro v _; exact_mod_cast Nat.factorial_le (hd v)
      _ = (n.factorial : ℝ) ^ Fintype.card V := by simp
      _ ≤ (n.factorial : ℝ) ^ n := pow_le_pow_right₀ hF hv
  have he : (∏ v, vertexPrice d p A D v) =
      (∏ v, ((d v).factorial : ℝ)) * A ^ Fintype.card V *
        D ^ (∑ v, Fintype.card (External (p v))) := by
    simp only [vertexPrice, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Finset.prod_pow_eq_pow_sum]
    exact congrArg (fun k : ℕ => (∏ v, ((d v).factorial : ℝ)) * A ^ Fintype.card V * D ^ k)
      (Finset.sum_congr rfl (fun _ _ => same_card _ _))
  rw [he]
  exact mul_le_mul
    (mul_le_mul hf (pow_le_pow_right₀ hA hv)
      (pow_nonneg hA0 _) (by positivity))
    (pow_le_pow_right₀ hD (physical_slots_le f d p (3 * n) hs))
    (pow_nonneg hD0 _) (mul_nonneg (by positivity) (pow_nonneg hA0 _))

omit [Fintype V] [DecidableEq V] in
private lemma physical_marginal (p : Patterns (family f d)) (n : ℕ) (A D : ℝ)
    (H : PatternPrice e L M f n A D) (v : V) (hj : 0 < d v) (hn : d v ≤ n)
    (u : External (p v)) :
    (∑ z : State (p v) I Unit, ‖vertexValue e L M (family f d) (fun _ => 1) p v z‖) ≤
      vertexPrice d p A D v := by
  calc
    _ = ((d v).factorial : ℝ) *
        (∑ z : State (p v) I Unit, ‖normalizedValue e L M f (d v) (p v) z‖) := by
      simp_rw [norm_vertex]
      rw [Finset.mul_sum]
    _ ≤ ((d v).factorial : ℝ) * (A * D ^ Fintype.card (External (p v))) :=
      mul_le_mul_of_nonneg_left (H.physical (d v) hj hn (p v) u) (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

omit [Fintype V] [DecidableEq V] in
private lemma gaussian_marginal (p : Patterns (family f d)) (n : ℕ) (A D : ℝ)
    (H : PatternPrice e L M f n A D) (v : V) (hj : 0 < d v) (hn : d v ≤ n)
    (u : Internal (p v)) (i : I) :
    (∑ z : State (p v) I Unit,
      if z.1 u = i then ‖vertexValue e L M (family f d) (fun _ => 1) p v z‖ else 0) ≤
      vertexPrice d p A D v := by
  calc
    _ = ((d v).factorial : ℝ) *
        (∑ z : State (p v) I Unit,
          if z.1 u = i then ‖normalizedValue e L M f (d v) (p v) z‖ else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z.1 u = i
      · simp only [if_pos hz, norm_vertex]
      · simp only [if_neg hz, mul_zero]
    _ ≤ ((d v).factorial : ℝ) * (A * D ^ Fintype.card (External (p v))) :=
      mul_le_mul_of_nonneg_left (H.gaussian (d v) hj hn (p v) u i) (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

private lemma pattern_bound (Q : Normal.Symmetric I) (p : Patterns (family f d))
    (e0 : Σ v, External (p v)) (n : ℕ) (A B D : ℝ)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (H : PatternPrice e L M f n A D)
    (hdp : ∀ v, 0 < d v) (hdn : ∀ v, d v ≤ n)
    (hv : Fintype.card V ≤ n) (hs : (∑ v, (d v + 2)) ≤ 3 * n)
    (hrow : ∀ i, (∑ j : I, ‖Q.cov i j‖) ≤ B) :
    ‖contractionSum e L M (family f d) Q (fun _ => 1) p e0.1‖ ≤
      patternCost n A B D := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hpoint (i j : I) : ‖Q.cov i j‖ ≤ B :=
    (Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)).trans
      (hrow i)
  have h := FiniteTensorProgramCost.unit_program_bound e0
    (vertexValue e L M (family f d) (fun _ => 1) p)
    (fun _ _ i j => Q.cov i j) (vertexPrice d p A D) B (3 * n)
    (by intro v; unfold vertexPrice; positivity) hB
    (gaussian_slots_le f d p (3 * n) hs)
    (physical_marginal e L M f d p n A D H e0.1 (hdp e0.1) (hdn e0.1) e0.2)
    (by
      intro k g l _hl i
      refine le_trans (le_of_eq ?_) (gaussian_marginal e L M f d p n A D H
        (g.get l).2.1 (hdp _) (hdn _) (g.get l).2.2 i)
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z.1 (g.get l).2.2 = i <;> simp only [hz, if_true, if_false])
    (by intro k g l _hl i; exact hrow i)
    (by intro k g l _hl i j; exact hpoint i j)
  have he :
      contractionSum e L M (family f d) Q (fun _ => 1) p e0.1 =
        HeterogeneousTensorBound.programContraction e0.1
          (vertexValue e L M (family f d) (fun _ => 1) p)
          (fun _ _ i j => Q.cov i j) (fun _ => ()) := by
    simp only [contractionSum, HeterogeneousTensorBound.programContraction,
      Fintype.sum_unique]
  rw [he]
  calc
    _ ≤ (((3 * n + 1) ^ (3 * n) : ℕ) : ℝ) *
        (∏ v, vertexPrice d p A D v) * B ^ (3 * n) := h
    _ ≤ (((3 * n + 1) ^ (3 * n) : ℕ) : ℝ) *
        ((n.factorial : ℝ) ^ n * A ^ n * D ^ (3 * n)) * B ^ (3 * n) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (product_price_bound f d p n A D hA hD hdn hv hs) (by positivity))
        (pow_nonneg hB0 _)
    _ = patternCost n A B D := by unfold patternCost; ring

/-- Every slot pattern is retained. Patterns without a physical port contribute
exactly zero to the centered quantity, as in the native anchored formula. -/
theorem family_contraction_bound (Q : Normal.Symmetric I)
    (n : ℕ) (A B D : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (H : PatternPrice e L M f n A D)
    (hdp : ∀ v, 0 < d v) (hdn : ∀ v, d v ≤ n)
    (hv : Fintype.card V ≤ n) (hs : (∑ v, (d v + 2)) ≤ 3 * n)
    (hrow : ∀ i, (∑ j : I, ‖Q.cov i j‖) ≤ B) :
    ‖anchoredContraction e L M (family f d) Q (fun _ => 1)‖ ≤
      (Fintype.card (Patterns (family f d)) : ℝ) * patternCost n A B D := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hc : 0 ≤ patternCost n A B D := by unfold patternCost; positivity
  unfold anchoredContraction
  calc
    _ ≤ ∑ p : Patterns (family f d),
        ‖if h : HasExternal (family f d) p then
          contractionSum e L M (family f d) Q (fun _ => 1) p
            (physicalPort (family f d) p h).1 else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _p : Patterns (family f d), patternCost n A B D := by
      apply Finset.sum_le_sum
      intro p _
      by_cases hp : HasExternal (family f d) p
      · rw [dif_pos hp]
        exact pattern_bound e L M f d Q p (physicalPort (family f d) p hp)
          n A B D hA hB hD H hdp hdn hv hs hrow
      · simpa only [dif_neg hp, norm_zero] using hc
    _ = _ := by simp

end FiniteFamily

section NativeShards

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable (e : X) (L : (I → ℝ) →ₗ[ℝ] X) (M : (Unit → ℝ) →ₗ[ℝ] X)
variable (l : Hot R → ℕ) (F : Hot R → X → ℂ) (f : X → ℝ) (r : ℕ)

private lemma quiet_degree {n : ℕ} (q : (parts (Board R r)).Mode)
    (hq : q ∈ shards (Board R r) (Join.pair R.quiet (pick r n))) (v : q.val) :
    0 < VacuumShardCount.degree (R := R) (r := r) v.val :=
  @VacuumShardCount.member_degree_pos V inferInstance inferInstance R r n q hq v.val v.property

set_option maxHeartbeats 800000 in
private lemma quiet_family {n : ℕ} (q : (parts (Board R r)).Mode)
    (hq : q ∈ shards (Board R r) (Join.pair R.quiet (pick r n))) :
    (fun v : q.val => NormalizedKernelProgram.vertex l F f r v.val) =
      family f (fun v : q.val => VacuumShardCount.degree (R := R) (r := r) v.val) := by
  funext v
  have hleft := VacuumShardCount.member_left_quiet (R := R) (r := r) (n := n) q hq v.val v.property
  have hmark : ¬ (Join.left v.val.val).val.Nonempty := by
    rw [hleft]
    exact Finset.not_nonempty_empty
  have hp := @quiet_degree V inferInstance inferInstance R r n q hq v
  have hdegree : VacuumShardCount.degree (R := R) (r := r) v.val ≠ 0 := Nat.ne_of_gt hp
  simp only [NormalizedKernelProgram.vertex, dif_neg hmark, if_neg hdegree,
    family, VacuumShardCount.degree]

set_option maxHeartbeats 800000 in
private lemma mode_bound (Q : Normal.Symmetric I) (n : ℕ) (hn : n ≤ r)
    (A B D : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (H : PatternPrice e L M f n A D)
    (hrow : ∀ i, (∑ j : I, ‖Q.cov i j‖) ≤ B)
    (q : (parts (Board R r)).Mode)
    (hq : q ∈ shards (Board R r) (Join.pair R.quiet (pick r n))) :
    ‖anchoredMode e L M (NormalizedKernelProgram.vertex l F f r) Q (fun _ => 1) q‖ ≤
      (Fintype.card (VacuumShardCount.SlotPatterns Kind q) : ℝ) * patternCost n A B D := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  unfold anchoredMode
  by_cases hq0 : q.val.Nonempty
  · rw [if_pos hq0, quiet_family (R := R) (n := n) l F f r q hq]
    let d : q.val → ℕ := fun v => VacuumShardCount.degree (R := R) (r := r) v.val
    have hdp (v : q.val) : 0 < d v :=
      @quiet_degree V inferInstance inferInstance R r n q hq v
    have hdn (v : q.val) : d v ≤ n := by
      exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) v.property).trans_eq
        (VacuumShardCount.degree_sum (R := R) (r := r) hn q hq)
    have hv : Fintype.card q.val ≤ n := by
      simpa only [Fintype.card_coe] using VacuumShardCount.vertex_count_le (R := R) (r := r) hn q hq
    have hs : (∑ v : q.val, (d v + 2)) ≤ 3 * n := by
      exact (Finset.sum_coe_sort q.val (fun i : Hot (Board R r) =>
        VacuumShardCount.degree (R := R) (r := r) i + 2)).le.trans
        (VacuumShardCount.leg_count_le (R := R) (r := r) hn q hq)
    exact family_contraction_bound e L M f d Q n A B D hA hB hD H hdp hdn hv hs hrow
  · rw [if_neg hq0, norm_zero]
    unfold patternCost
    positivity

/-- Full native vacuum shard sum, with its original outer factorial. No field,
period or external Census cardinality occurs in the fixed-order constant. -/
theorem vacuum_program_bound (Q : Normal.Symmetric I) (n : ℕ) (hn : n ≤ r)
    (A B D : ℝ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (H : PatternPrice e L M f n A D)
    (hrow : ∀ i, (∑ j : I, ‖Q.cov i j‖) ≤ B) :
    ‖(n.factorial : ℂ)⁻¹ *
      ∑ q ∈ shards (Board R r) (Join.pair R.quiet (pick r n)),
        anchoredMode e L M (NormalizedKernelProgram.vertex l F f r) Q (fun _ => 1) q‖ ≤
      orderConstant n * A ^ n * B ^ (3 * n) * D ^ (3 * n) := by
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  have hD0 : 0 ≤ D := le_trans zero_le_one hD
  have hc : 0 ≤ patternCost n A B D := by unfold patternCost; positivity
  let S := shards (Board R r) (Join.pair R.quiet (pick r n))
  have hcount :
      (∑ q ∈ S, (Fintype.card (VacuumShardCount.SlotPatterns Kind q) : ℝ)) ≤
        ((2 ^ (2 ^ n) * 3 ^ (3 * n) : ℕ) : ℝ) := by
    exact_mod_cast
      (VacuumShardCount.total_pattern_count_le (R := R) (r := r)
        (K := Kind) (by decide) hn)
  have hsum :
      ‖∑ q ∈ S,
        anchoredMode e L M (NormalizedKernelProgram.vertex l F f r) Q (fun _ => 1) q‖ ≤
      ((2 ^ (2 ^ n) * 3 ^ (3 * n) : ℕ) : ℝ) * patternCost n A B D := by
    calc
      _ ≤ ∑ q ∈ S,
          ‖anchoredMode e L M (NormalizedKernelProgram.vertex l F f r) Q (fun _ => 1) q‖ :=
        norm_sum_le _ _
      _ ≤ ∑ q ∈ S,
          (Fintype.card (VacuumShardCount.SlotPatterns Kind q) : ℝ) * patternCost n A B D :=
        Finset.sum_le_sum (fun q hq => mode_bound e L M l F f r Q n hn
          A B D hA hB hD H hrow q hq)
      _ = (∑ q ∈ S, (Fintype.card (VacuumShardCount.SlotPatterns Kind q) : ℝ)) *
          patternCost n A B D := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hcount hc
  have hnorm : ‖(n.factorial : ℂ)⁻¹‖ = (n.factorial : ℝ)⁻¹ := by simp
  rw [norm_mul, hnorm]
  calc
    _ ≤ (n.factorial : ℝ)⁻¹ *
        (((2 ^ (2 ^ n) * 3 ^ (3 * n) : ℕ) : ℝ) * patternCost n A B D) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      simp only [orderConstant, patternCost, Nat.cast_mul]
      ring

end NativeShards

section ActualGround

open YM.RG YM.Precision YM.Lattice YM.Wilson YM.Exterior YM.Tree
open YM.Next.SectorChange

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip}
  {P : PathData G} {O : ChartRatio G}
variable (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (w : S.Choices)
variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable (W : Bulk.Colors R G f) (r : ℕ)

/-- Direct application to the original centered ground function. The supplied
prices are precisely the normalized pattern marginals and covariance rows;
their actual model construction is separate from this finite consequence. -/
theorem ground_centered_bound {n : ℕ} (hn : 0 < n) (hnr : n ≤ r)
    (Bfield : fieldDir G c 1) (A B D : ℝ)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (H : PatternPrice (ActualGroundProgram.coupling F) (Bulk.hinge F)
      (ActualGroundContraction.rayMap K F Bfield) (Bulk.geometric K F w W) n A D)
    (hrow : ∀ i, (∑ j,
      ‖(YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank
        (K.covariance F w) (K.symm F w)).cov i j‖) ≤ B) :
    ‖Symmetry.Orbit.ground K F w W r n Bfield -
      Symmetry.Orbit.ground K F w W r n 0‖ ≤
        orderConstant n * A ^ n * B ^ (3 * n) * D ^ (3 * n) := by
  rw [ActualAnchoredGround.ground_centered K F w W r hn hnr Bfield]
  exact vacuum_program_bound (ActualGroundProgram.coupling F) (Bulk.hinge F)
    (ActualGroundContraction.rayMap K F Bfield) W.power (Bulk.markFn S F W)
    (Bulk.geometric K F w W) r
    (YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.realRank
      (K.covariance F w) (K.symm F w))
    n hnr A B D hA hB hD H hrow

end ActualGround

end YM.Integration.FiniteVacuumProgramBound
end
