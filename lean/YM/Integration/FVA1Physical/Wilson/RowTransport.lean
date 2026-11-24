import YM.Integration.FVA1Physical.Wilson.FieldRows

/-! Pull the complete rooted absolute derivative rows through the stationary
coordinate map. A remote physical derivative retains the root in the spatial
weight, also when the two successive RG maps have different coordinate types. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MvPolynomial Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Bout MSbar.Duel MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Rolling MSbar.CrossH MSbar.Measuring
open scoped Classical Topology BigOperators
variable {σ ι:Type} [Fintype σ] [Fintype ι] [DecidableEq σ] [DecidableEq ι]
variable {n:Side}

omit [DecidableEq σ] in
private theorem change_root (l:σ→Site n) (W:Finset (Site n)) (v u:Site n) (a:ℝ) (ha:0 ≤ a)
    (s k:ℕ) (ξ:View σ) (f:Pot σ) :
    lump l (insert v W) a s k ξ f ≤ liftW a s (2*separation u v)*lump l (insert u W) a s k ξ f := by
  unfold lump
  rw [←sheen]
  apply shiny
  intro T _
  let Z:=zone l (insert u W) T
  have part:zone l (insert v W) T ⊆ {v}∪Z:=by
    intro b h
    simp only [zone,mem_union,mem_insert,Finset.mem_singleton] at h ⊢
    rcases h with (h|h)|h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_union_left _ (Finset.mem_insert_of_mem h))
    · exact Or.inr (Finset.mem_union_right _ h)
  have he:=w_cast part (mem_singleton_self v) (show u∈Z from mem_union_left _ (mem_insert_self _ _)) ha s
  have extent0 : extent ({v}:Finset (Site n))=0:=Nat.eq_zero_of_le_zero (yard (by simp))
  simp only [extent0, liftW, Nat.cast_zero,add_zero,one_pow,mul_zero,Real.exp_zero,one_mul] at he
  have bump:liftW a s (separation v u) ≤ liftW a s (2*separation u v):=by
    rw [separation_comm v u];exact w_more (by omega) ha _
  have weights : spread l (insert v W) a s T ≤ liftW a s (2*separation u v)*spread l (insert u W) a s T:=
    he.trans (mul_le_mul_of_nonneg_right bump (effect ..).le)
  unfold rate
  rw [←mul_assoc]
  exact mul_le_mul_of_nonneg_right weights (abs_nonneg _)

private theorem rail_partial (M:Matrix σ ι ℝ) (v:ι) (f:Pot σ) :
    pderiv v (Rolling.rail M f) = ∑ u:σ,M u v • Rolling.rail M (pderiv u f) := by
  rw [←dintX (Rolling.rail M f) v,dimK]
  have e: M *ᵥ (Push.Uniform.bolt v) = fun u=>M u v:=by
    have bv : Push.Uniform.bolt v = (Pi.single v 1 : View ι) := by
      ext i
      by_cases hi:i=v <;> simp [Push.Uniform.bolt,hi]
    rw [bv,Matrix.mulVec_single]
    simp only [MulOpposite.op_one,one_smul]
    rfl
  simp only [e,dint,LinearMap.sum_apply,LinearMap.smul_apply,Derivation.coeFn_coe,_root_.map_sum,map_smul]

/-- Sharp total variation estimate for every fixed derivative order under a
spatially summable change of field coordinates. The total cost is the kth
power of the row-sum bound, with no dependence on the number of coordinates. -/
theorem rooted_coordinate_pullback (l:σ→Site n) (L:ι→Site n) (M:Matrix σ ι ℝ) {a C:ℝ}
    (s:ℕ) (ha:0 ≤ a) (law:Syrup l L a s M C) (z:View ι) (k:ℕ) (W:Finset (Site n)) (f:Pot σ) :
    lump L W a s k z (Rolling.rail M f) ≤ C^k*lump l W a s k (M *ᵥ z) f := by
  induction k generalizing W f with
  | zero =>
    rw [pow_zero,one_mul]
    simp only [lump,twillz,rate]
    change spread L W a s []*|MvPolynomial.eval z (Rolling.rail M f)| ≤
      spread l W a s []*|MvPolynomial.eval (M *ᵥ z) f|
    rw [show MvPolynomial.eval z (Rolling.rail M f)=_ from congr_fun (Rolling.clearL M z) f]
    rfl
  | succ k ih =>
    rw [Whisk.down,Whisk.down]
    let A:=fun u:σ=>lump l (insert (l u) W) a s k (M *ᵥ z) (pderiv u f)
    have c0:0 ≤ C:=zero_le_one.trans law.cash
    have each (v:ι) :
      lump L (insert (L v) W) a s k z (pderiv v (Rolling.rail M f)) ≤
        ∑ u:σ,(skim l L a s u v*|M u v|)*(C^k*A u) := by
      rw [rail_partial]
      apply (lump.totals ..).trans (sum_le_sum ?_)
      intro u _
      rw [lump.smul]
      have hr: liftW a s (2*separation (l u) (L v)) = skim l L a s u v:=by
        unfold liftW skim Measuring.factor
        push_cast
        rfl
      have one:=change_root l W (L v) (l u) a ha s k (M *ᵥ z) (pderiv u f)
      rw [hr] at one
      have both:=(ih (insert (L v) W) (pderiv u f)).trans (mul_le_mul_of_nonneg_left one (pow_nonneg c0 _))
      refine (mul_le_mul_of_nonneg_left both (abs_nonneg (M u v))).trans_eq ?_
      dsimp only [A];ring
    refine (sum_le_sum (fun v _=>each v)).trans ?_
    rw [Finset.sum_comm,pow_succ,Finset.mul_sum]
    apply sum_le_sum
    intro u _
    rw [←Finset.sum_mul]
    exact (mul_le_mul_of_nonneg_right (law.leftP u) (mul_nonneg (pow_nonneg c0 _) (lump.nonneg ..))).trans_eq (by ring)

theorem rooted_vault_pullback (l:σ→Site n) (L:ι→Site n) (M:Matrix σ ι ℝ) {a C B:ℝ}
    (s h:ℕ) (ha:0 ≤ a) (law:Syrup l L a s M C) (z:View ι) (W:Finset (Site n)) (f:Pot σ)
    (fund:Vault l W a s h (M *ᵥ z) f B) : Vault L W a s h z (Rolling.rail M f) (C^h*B) := by
  have c0:=zero_le_one.trans law.cash
  refine ⟨mul_nonneg (pow_nonneg c0 _) fund.1,fun k hk=>?_⟩
  exact (rooted_coordinate_pullback l L M s ha law z k W f).trans
    (mul_le_mul (pow_le_pow_right₀ law.cash hk) (fund.2 k hk) (lump.nonneg ..) (pow_nonneg c0 _))

end YM.Integration.FVA1Physical.Wilson
