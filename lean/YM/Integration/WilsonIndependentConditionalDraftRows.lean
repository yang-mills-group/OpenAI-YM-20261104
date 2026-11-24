import YM.Integration.WilsonIndependentConditionalPulledBoard
import YM.WilsonCoeffUV.Thermo.Slots

/-! A retained finite family of labeled legs applied to an absolutely rooted
row. Unprocessed legs use their literal Kronecker constraint. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalDraftRows
open RegulatorIR RegulatorIR.Budget RegulatorIR.Budget.Packet Function
open scoped Classical BigOperators
variable {I:Type}{r:ℕ}

def leg (K:Layer I I)(s:Finset (Fin r))(z y:Tuple I r)(i:Fin r):ℝ:=by
  classical
  exact if i∈s then K (z i) (y i) else if y i=z i then 1 else 0

def wires (K:Layer I I)(s:Finset (Fin r))(z y:Tuple I r):ℝ:=
  ∏ i,leg K s z y i

theorem empty (K:Layer I I)(x y:Tuple I r):wires K ∅ x y=if y=x then 1 else 0:=by
  classical
  by_cases eq:y=x
  · subst y;simp [wires,leg]
  · obtain ⟨i,diff⟩:=Function.ne_iff.mp eq
    rw [if_neg eq]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [leg,diff])

theorem full (K:Layer I I)(x y:Tuple I r):wires K Finset.univ x y=∏ i,K (x i) (y i):=by
  classical
  simp [wires,leg]

theorem single (K:Layer I I){s:Finset (Fin r)}{i:Fin r}(hi:i∉s)
    (x y:Tuple I r)(a:I):
    K (x i) a*wires K s (update x i a) y=
      if y i=a then wires K (insert i s) x y else 0:=by
  classical
  by_cases eq:y i=a
  · subst a
    rw [if_pos rfl,wires,wires,←Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ←Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [leg,hi,if_false,update_self,if_pos,Finset.mem_insert_self,one_mul]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have ne:j≠i:=(Finset.mem_erase.mp hj).1
    simp [ne]
  · rw [if_neg eq,show wires K s (update x i a) y=0 from Finset.prod_eq_zero (Finset.mem_univ i) (by simp [leg,hi,eq])]
    exact mul_zero _

theorem bound {K:Layer I I}{C:ℝ}(one:1≤C)(coeff:∀a b,|K a b|≤C)
    (s:Finset (Fin r))(x y:Tuple I r):|wires K s x y|≤C^r:=by
  classical
  rw [wires,Finset.abs_prod]
  calc
    _≤∏ _i:Fin r,C:=by
      apply Finset.prod_le_prod (fun _ _=>abs_nonneg _)
      intro i _
      unfold leg
      split
      · exact coeff _ _
      · split <;> simp [one,zero_le_one.trans one]
    _=C^r:=by simp

theorem paid {K:Layer I I}{C:ℝ}(one:1≤C)(coeff:∀a b,|K a b|≤C)
    {T:Packet I r}(price:Summable (fun y=>‖T y‖))(s:Finset (Fin r))(x:Tuple I r):
    Summable (fun y=>wires K s x y*T y):=by
  apply Summable.of_norm_bounded (price.mul_left (C^r))
  intro y
  rw [Real.norm_eq_abs,abs_mul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (bound one coeff _ _ _) (abs_nonneg _)

end YM.Integration.WilsonIndependentConditionalDraftRows
