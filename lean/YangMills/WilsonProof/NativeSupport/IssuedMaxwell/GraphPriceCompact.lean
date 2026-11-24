import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphPriceCoordinates
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphPriceCompact
open YM YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.FVA2.O.Score YM.FVA2.O.Project YM.FVA2.O.Enh
open Filter Set YangMills.MSbar IssuedMaxwell.Reports PowerSeries
open scoped BigOperators Classical Topology
variable (g:YangMills.GaugeGroup){n:ℕ}
theorem original (p:FLog g.core n)(financed:Markup p)(K:Set (Points n))(hK:IsCompact K)
    (sep:K⊆conf n)(w k:ℕ)(m:(B g).toCoordinates.Key→₀ℕ):
    ∃C:ℝ,0<C ∧ ∃L:ℕ,∀ᶠ t:ℝ in atTop,∀x∈K,
      ‖MvPolynomial.coeff m (GraphPrices.entered g p w k t x).val‖≤C*(1+t)^L:=by
  let wage (b:Grade g.core w)(x:K)(t:ℝ):=
    coeff k (p t x.val (own b))*MvPolynomial.coeff m (vertex b).val
  have each (b:Grade g.core w):Rain 0 (wage b):=by
    have live:=(financed.clocks K hK sep (own b) (k+1)) k (Nat.lt_succ_self k)
    exact live.wig (Rain.fixed _)
  obtain ⟨C,pos,L,rain⟩:=Rain.sum Finset.univ (fun b _=>each b)
  refine ⟨C,pos,L,?_⟩
  filter_upwards [rain] with t bound
  intro x hx
  simpa only [GraphPriceCoordinates.monomial,post,neg_zero,zero_mul,Real.exp_zero,mul_one,wage] using bound ⟨x,hx⟩
end IssuedMaxwell.GraphPriceCompact
end
