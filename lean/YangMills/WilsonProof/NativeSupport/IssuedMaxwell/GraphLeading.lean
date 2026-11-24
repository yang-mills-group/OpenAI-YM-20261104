import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphCorrelation
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphLeading
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YangMills.MSbar
open IssuedMaxwell.Reports (B)
variable (g:YangMills.GaugeGroup){n:ℕ}
theorem original (a:Fin n→Ordinary.Label (B g))(x:Points n)(hx:x∈conf n):
    GraphCorrelation.read g n 0 a x=(B g).moment x (fun i=>(a i).2.val):=by
  rw [GraphCorrelation.regular _ _ _ _ hx,Dframe.limit_lead _ _ hx]
  rfl
end IssuedMaxwell.GraphLeading
end
