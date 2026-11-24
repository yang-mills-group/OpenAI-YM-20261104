import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Covariance
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.Pairings
open YM YangMills
open scoped Classical BigOperators
variable (g:YangMills.GaugeGroup)
abbrev B:=IssuedMaxwell.Shell.coordinates g

theorem monomial {n:ℕ}(z:YM.Points n)(W:YM.Maxwell.Wick.Powers g.core n):
    (B g).wickMonomial z W=YM.Maxwell.Wick.monomial z W:=by
  classical
  letI:Fintype ((B g).Occ W):=inferInstanceAs (Fintype (YM.Maxwell.Wick.Occ W))
  letI:Fintype ((B g).Pairing W):=inferInstanceAs (Fintype (YM.Maxwell.Wick.Occ.Matching W))
  unfold YangMills.Maxwell.Coordinates.wickMonomial YM.Maxwell.Wick.monomial
  rw [finsum_eq_sum_of_fintype]
  apply Finset.sum_congr rfl
  intro s _
  rw [finprod_eq_prod_of_fintype]
  simp only [YM.Maxwell.Wick.Occ.graph,YM.Maxwell.Wick.Occ.corners,Finset.prod_filter]
  rfl

theorem original {n:ℕ}(z:YM.Points n)(W:YM.Maxwell.Wick.Powers g.core n):
    YM.Maxwell.Wick.moment g.core z (fun i=>MvPolynomial.basisMonomials _ ℂ (W i))=
      (B g).wickMonomial z W:=
  (YM.Maxwell.Wick.moment_basis W z).trans (monomial g z W).symm
end IssuedMaxwell.Pairings
end
