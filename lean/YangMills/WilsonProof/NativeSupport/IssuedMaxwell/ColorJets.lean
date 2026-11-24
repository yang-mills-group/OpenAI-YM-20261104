import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.SectorSpine
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.ColorJets
open YM YM.Tensor YM.Analysis YM.Maxwell YM.Extra.FD
variable {G:Gauge} {j:ℕ}

theorem curl (u:G.El)(A:YM.Labels.Taylor G j):
    takeCurl (YM.Labels.Taylor.paint u A)=dye (conjG u) (takeCurl A):=by
  funext a b
  ext1 t
  change ((j+1:ℕ):ℝ) • (G.adjoint u ((A.val b).curryLeft (basis a) t)-
    G.adjoint u ((A.val a).curryLeft (basis b) t)) =
    G.adjoint u (((j+1:ℕ):ℝ) • ((A.val b).curryLeft (basis a) t-(A.val a).curryLeft (basis b) t))
  rw [map_smul,map_sub]

theorem original (u:G.El)(P:Shell G j):
    gaugeJet (actionG u j P)=YM.Labels.Taylor.paint u (gaugeJet P):=by
  apply potential.injective
  apply Subtype.ext
  change takeCurl (gaugeJet _)=takeCurl _
  rw [match_leg,curl,match_leg]
  rfl
end IssuedMaxwell.ColorJets
end
