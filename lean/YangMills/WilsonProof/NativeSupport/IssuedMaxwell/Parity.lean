import YM.XSpace.Parity
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Reports
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.Parity
open YM YM.Maxwell YM.XSpace.Normalize YM.XSpace.Taylor
open YangMills.MSbar
variable {g:YangMills.GaugeGroup}{d:ℕ}

theorem polynomial (V:TaylorTower g.core)(p:WickPol g.core):
    probe V (mirror _ p)=probe (fun i=>-V i) p:=by
  have he:(probe V).comp (mirror _)=probe (fun i=>-V i):=by
    ext i
    simp [mirror,probe,coord]
  exact DFunLike.congr_fun he p

theorem original (p q:Sec g.core d):
    Position.Mirrored (IssuedMaxwell.Reference.issued g) p.val q.val ↔ q=hinge d p:=by
  constructor
  · intro H
    apply Subtype.ext
    apply equalPol
    intro V
    change probe V q.val=probe V (mirror _ p.val)
    exact (H V).trans (polynomial V p.val).symm
  · rintro rfl V
    exact polynomial V p.val
end IssuedMaxwell.Parity
end
