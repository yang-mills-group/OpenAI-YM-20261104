import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.SectorSpine
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.OrthogonalShell
open YM YM.Extra.FD YM.Maxwell
open scoped Classical BigOperators RealInnerProductSpace
variable {G:YM.Gauge} {j:ℕ}

theorem adjoints (L:G.Color→L[ℝ]G.Color)(P Q:TwoJet G.Color j):
    dotF (dye L P) Q=dotF P (dye L.adjoint Q):=by
  simp only [dotF_eval,dotDir_eval]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro v _
  change ⟪L (P a b (dir v)), Q a b (dir v)⟫ =⟪P a b (dir v),L.adjoint (Q a b (dir v))⟫ 
  exact (ContinuousLinearMap.adjoint_inner_right ..).symm

theorem original (L:G.Color→L[ℝ]G.Color)(P:TwoJet G.Color j):
    asSol (dye L P)=insertColor L j (asSol P):=by
  apply (dualSol G.Color j).injective
  apply LinearMap.ext
  intro Q
  rw [asSol_duality,dualSol_val]
  change dotF (dye L P) Q.val=dotF (dye L (asSol P).val) Q.val
  rw [adjoints,adjoints]
  exact (asSol_duality P (insertColor L.adjoint j Q)).symm
end IssuedMaxwell.OrthogonalShell
end
