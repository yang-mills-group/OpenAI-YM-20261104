import YangMills.WilsonProof.NativeSupport.WilsonSharpPhysicalTreeGeometryConvoy
import YM.OPE.Mountains.Payout

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSharpPhysicalTreeGeometry
open YangMills.Hierarchy Function Finset OPE OPE.Arboreal
open scoped Classical BigOperators

variable (t : FusionTree)

theorem prod_zones (f : Node t → ℝ) : (∏ j ∈ (rawTree t).zones, f j) = ∏ v : t.Vertex, f (.inl v) :=
  (prod_coe_sort _ f).symm.trans ((zoneEquiv t).prod_comp (fun j => f j.1)).symm

theorem prod_proper (f : Node t → ℝ) : (∏ j ∈ (rawTree t).middle (rawTree t).zones, f j) =
    ∏ i : Fin t.branches, f (.inl i.succ) :=
  (prod_coe_sort _ f).symm.trans ((properEquiv t).prod_comp (fun j => f j.1)).symm

theorem sum_proper (f : Node t → ℝ) : (∑ j ∈ (rawTree t).middle (rawTree t).zones, f j) =
    ∑ i : Fin t.branches, f (.inl i.succ) :=
  (sum_coe_sort _ f).symm.trans ((properEquiv t).sum_comp (fun j => f j.1)).symm

theorem sum_leaves (f : Node t → ℝ) : (∑ j ∈ (rawTree t).leaves, f j) = ∑ i : Fin t.leaves, f (.inr i) :=
  (sum_coe_sort _ f).symm.trans ((leafEquiv t).sum_comp (fun j => f j.1)).symm

theorem prod_leaves (f : Node t → ℝ) : (∏ j ∈ (rawTree t).leaves, f j) = ∏ i : Fin t.leaves, f (.inr i) :=
  (prod_coe_sort _ f).symm.trans ((leafEquiv t).prod_comp (fun j => f j.1)).symm

def rawCutoff (D : Fin t.branches → ℕ) : Node t → ℕ := Sum.elim (Fin.cases 0 D) (fun _ => 0)

theorem grace_eq (D : Fin t.branches → ℕ) (s : t.Vertex → ℝ) :
    (rawTree t).grace (rawScale t s) (rawCutoff t D) = t.cutoffGain D s :=
  sum_proper t (fun u => ((rawTree t).ratioAt (rawScale t s) u) ^ (rawCutoff t D u + 1))

variable {g : YangMills.GaugeGroup} {C : YangMills.WilsonFamily g} (H : YangMills.Hierarchy C)
    {G : Gauge} {L : Register G} (p : Node t → L.Token) (a : Fin t.leaves → H.Tag)
    (hp : ∀ i, (p (.inr i)).1 = (a i).1)
include hp

theorem total_weight : (OPE.sigma (crop p (rawTree t).leaves) : ℝ) = H.weight a := by
  rw [sigma_set, Nat.cast_sum, sum_leaves]
  exact sum_congr rfl (fun i _ => congrArg (fun n : ℕ => (n : ℝ)) (hp i))

theorem input_weight (v : t.Vertex) :
    (OPE.sigma (crop p ((rawTree t).inputs (rawTree t).zones (.inl v))) : ℝ) = t.leafWeight H a v := by
  rw [sigma_set, Nat.cast_sum]
  change (∑ j ∈ (rawTree t).leaves.filter (fun j => (rawTree t).Anc (.inl v) j), ((p j).1 : ℝ)) = _
  rw [sum_filter, sum_leaves]
  unfold FusionTree.leafWeight
  apply sum_congr rfl
  intro i _
  simp only [leaf_ancestor, hp]

theorem tariff_eq (out : ℝ) (s : t.Vertex → ℝ) :
    (rawTree t).tariff p out 0 (rawScale t s) =
      s 0 ^ (out - H.weight a) * ∏ i : Fin t.branches, (t.ratio s i) ^ (-t.leafWeight H a i.succ) := by
  unfold OPE.Arboreal.tariff
  rw [total_weight t H p a hp, sub_zero, prod_proper]
  apply congrArg (fun y : ℝ => s 0 ^ (out - H.weight a) * y)
  apply prod_congr rfl
  intro i _
  rw [input_weight t H p a hp, sub_zero]
  rfl

omit hp in
theorem prestige_eq (s : t.Vertex → ℝ) (small : ∀ v, 0 < s v ∧ s v ≤ 1) (k : ℕ) :
    (rawTree t).prestige (rawScale t s) ^ k = ∏ v : t.Vertex, (1 + |Real.log (s v)|) ^ k := by
  unfold OPE.Arboreal.prestige
  rw [prod_zones, ← Finset.prod_pow]
  apply prod_congr rfl
  intro v _
  rw [abs_of_nonpos (Real.log_nonpos (small v).1.le (small v).2)]
  rfl

theorem listPrice_eq (m k : ℕ) (s : t.Vertex → ℝ) (small : ∀ v, 0 < s v ∧ s v ≤ 1) :
    (rawTree t).listPrice p (rawScale t s) m k = t.bound H (m : ℝ) a s k := by
  unfold OPE.Arboreal.listPrice FusionTree.bound
  rw [tariff_eq t H p a hp, prestige_eq t s small k]

theorem rent_eq (s : t.Vertex → ℝ) :
    (rawTree t).rent p (rawScale t s) (rawTree t).leaves = ∏ i, s (t.attachLeaf i) ^ (a i).1 := by
  unfold OPE.Arboreal.rent
  rw [prod_leaves]
  apply prod_congr rfl
  intro i _
  rw [hp i]; rfl

/-- The product of attached leaf powers is the same engineering price as the public descendant tariff. -/
theorem attachedBase_eq_bound (m : ℕ) (s : t.Vertex → ℝ) (gr : (rawTree t).Graduated (rawScale t s)) :
    s 0 ^ m / (∏ i, s (t.attachLeaf i) ^ (a i).1) = t.bound H (m : ℝ) a s 0 := by
  have pos (v : t.Vertex) : 0 < s v := gr.allowed (.inl v) (zone_inl t v)
  have leaves : 0 < ∏ i, s (t.attachLeaf i) ^ (a i).1 := prod_pos (fun i _ => pow_pos (pos _) _)
  have root := pow_pos (pos 0) m
  have paid := gr.reward_eq m p
  unfold OPE.Arboreal.fee at paid
  rw [rent_eq t H p a hp] at paid
  change (rawTree t).tariff p m 0 (rawScale t s) * ((∏ i, s (t.attachLeaf i) ^ (a i).1) / s 0 ^ m) = 1 at paid
  rw [←mul_div_assoc, div_eq_one_iff_eq root.ne'] at paid
  calc _ = (rawTree t).tariff p m 0 (rawScale t s) := (div_eq_iff leaves.ne').2 paid.symm
    _ = _ := by rw [tariff_eq t H p a hp]; simp [FusionTree.bound]

end YM.Integration.WilsonSharpPhysicalTreeGeometry
