import YM.Integration.WilsonIndependentConditionedActualCredit

/-! Finite salaries on the same fixed report keep their polynomial witness before regulator limits. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedActualBudget
open Filter Real Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Bank
open WilsonIndependentConditionedActualCredit (badge gramAge)
open WilsonIndependentConditionedBankFittedFees (age)
open WilsonOriginalPublicRelativeGramKineticMesh (thermal)
open WilsonInvariantActionPosition (berth)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}

def Pay (R:Run G)(X:ℕ→ℝ):Prop:=
  ∃P:Credit,∀ᶠ f:ℕ in atTop,1 ≤ badge R f → |X f| ≤ P.buy (badge R f)

namespace Pay
variable {X Y:ℕ→ℝ}

theorem fixed (R:Run G)(v:ℝ):Pay R (fun _=>v):=by
  refine ⟨⟨0,max 1 |v|,le_max_left ..⟩,Eventually.of_forall (fun f _=>?_)⟩
  simpa only [Credit.buy,pow_zero,mul_one] using le_max_right (1:ℝ) |v|

theorem add (x:Pay R X)(y:Pay R Y):Pay R (fun f=>X f+Y f):=by
  obtain ⟨P,hp⟩:=x
  obtain ⟨Q,hq⟩:=y
  refine ⟨P.plus Q,?_⟩
  filter_upwards [hp,hq] with f p q one
  exact (abs_add_le ..).trans ((add_le_add (p one) (q one)).trans (P.fuel Q one))

theorem mul (x:Pay R X)(y:Pay R Y):Pay R (fun f=>X f*Y f):=by
  obtain ⟨P,hp⟩:=x
  obtain ⟨Q,hq⟩:=y
  refine ⟨P.prodC Q,?_⟩
  filter_upwards [hp,hq] with f p q one
  rw [abs_mul,Credit.products]
  exact mul_le_mul (p one) (q one) (abs_nonneg _) (zero_le_one.trans (P.purchase one))

theorem abs (x:Pay R X):Pay R (fun f=>|X f|):=by simpa only [Pay,abs_abs] using x

theorem max (x:Pay R X)(y:Pay R Y):Pay R (fun f=>Max.max (X f) (Y f)):=by
  obtain ⟨P,hp⟩:=x
  obtain ⟨Q,hq⟩:=y
  refine ⟨P.plus Q,?_⟩
  filter_upwards [hp,hq] with f p q one
  rcases le_total (X f) (Y f) with h|h
  · rw [max_eq_right h]
    exact (q one).trans (Credit.thickened P one)
  · rw [max_eq_left h]
    exact (p one).trans (Credit.thickens Q one)

theorem product {ι:Type*} (s:Finset ι)(X:ι→ℕ→ℝ)(pay:∀i,Pay R (X i)):
    Pay R (fun f=>∏i∈s,X i f):=by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa only [Finset.prod_empty] using fixed R 1
  | insert i s h ih=>
    simpa only [Finset.prod_insert h] using (pay i).mul ih

theorem earned (x:Pay R X)(simple:G.Simple){ε:ℝ}(ep:0<ε):
    ∀ᶠ f:ℕ in atTop,|X f| ≤ (thermal R f)^(-ε):=by
  obtain ⟨P,p⟩:=x
  have hot:=(tendsto_log_atTop.comp (Next.Rank.Station.hat_rate R.family.path.levels simple)).eventually_ge_atTop 1
  filter_upwards [p,WilsonIndependentConditionedActualCredit.subpower R simple P ep,hot] with f c roof one
  exact (c one).trans roof
end Pay

theorem ages (R:Run G)(simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(t:ℕ)(T:Credit):
    Pay R (fun f=>T.buy (age R f f)) ∧ Pay R (fun f=>T.buy (age R f (berth R t f))) ∧
    Pay R (fun f=>T.buy (gramAge R f (berth R t f))):=by
  have v:=WilsonIndependentConditionedActualCredit.original R simple slow t
  have p:=WilsonIndependentConditionedActualCredit.polynomial R simple slow t T
  let E:=T.usingC (WilsonIndependentConditionedActualCredit.drift t)
  refine ⟨⟨E,?_⟩,⟨E,?_⟩,⟨E,?_⟩⟩ <;> filter_upwards [v,p] with f s c _
  · exact (abs_of_nonneg (zero_le_one.trans (T.purchase s.2.1))).le.trans c.1
  · exact (abs_of_nonneg (zero_le_one.trans (T.purchase s.2.2.2.1))).le.trans c.2.1
  · exact (abs_of_nonneg (zero_le_one.trans (T.purchase s.2.2.2.2.2.1))).le.trans c.2.2

end YM.Integration.WilsonIndependentConditionedActualBudget
