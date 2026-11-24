import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphPrices
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphPriceCoordinates
open YM YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.FVA2.O.Score YM.FVA2.O.Project
open YangMills.MSbar IssuedMaxwell.Reports PowerSeries
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n:ℕ}
theorem monomial (p:FLog g.core n)(w k)(t)(x)(m:(B g).toCoordinates.Key→₀ℕ):
    MvPolynomial.coeff m (GraphPrices.entered g p w k t x).val=
      ∑b:Grade g.core w,coeff k (p t x (own b))*MvPolynomial.coeff m (vertex b).val:=by
  let row:Sec g.core w→ₗ[ℂ]ℂ:=(MvPolynomial.lcoeff ℂ m).comp (coeS w)
  change row (∑b:Grade g.core w,coeff k (p t x (own b)) • vertex b)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [map_smul]
  rfl

theorem collision (p:FLog g.core n)(financed:Markup p)(w k t x)(hx:x∉conf n):
    GraphPrices.entered g p w k t x=0:=by
  simp [GraphPrices.entered,financed.off t x hx]
  exact Or.inr rfl

theorem continuous (p:FLog g.core n)(financed:Markup p)(w k t)(m:(B g).toCoordinates.Key→₀ℕ):
    ContinuousOn (fun x=>MvPolynomial.coeff m (GraphPrices.entered g p w k t x).val) (conf n):=by
  simp_rw [monomial]
  apply continuousOn_finsetSum
  intro b _
  exact (financed.stays t (own b) k).mul continuousOn_const

theorem polynomial (p:FLog g.core n)(financed:Markup p)(w k)(m:(B g).toCoordinates.Key→₀ℕ):
    ∃D:ℕ,∀x,∃q:Polynomial ℂ,q.natDegree≤D ∧ ∀t:ℝ,
      MvPolynomial.coeff m (GraphPrices.entered g p w k t x).val=q.eval (t:ℂ):=by
  have ready:Scale.Pace (fun x t=>MvPolynomial.coeff m (GraphPrices.entered g p w k t x).val):=by
    simp_rw [monomial]
    exact Scale.Pace.sum Finset.univ (fun b _=>(financed.poly (own b) k).mul
      (Scale.Pace.narrow (fun _=>MvPolynomial.coeff m (vertex b).val)))
  obtain ⟨D,files⟩:=ready
  refine ⟨D,fun x=>?_⟩
  obtain ⟨q,deg,eq⟩:=files x
  exact ⟨q,deg,fun t=>congrFun eq t⟩
end IssuedMaxwell.GraphPriceCoordinates
end
