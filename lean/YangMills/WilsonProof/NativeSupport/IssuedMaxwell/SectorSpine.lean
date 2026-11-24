import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Shell
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.SectorSpine
open YangMills YM
open scoped Classical

variable (g:YangMills.GaugeGroup)
abbrev B:=IssuedMaxwell.Shell.coordinates g

theorem reads (A:YM.Maxwell.TaylorTower g.core)(p:YM.Maxwell.WickPol g.core):
    (B g).eval A p=YM.Maxwell.probe A p:=rfl

theorem admissible (d:ℕ)(p:YM.Maxwell.WickPol g.core):
    (B g).Admissible d p ↔ p∈YM.Extra.FD.through g.core d ∧ YM.Extra.FD.secret p:=Iff.rfl

theorem original (d:ℕ)(f:YM.Maxwell.WickPol g.core):
    (B g).Admissible d f↔f∈MvPolynomial.restrictSupport ℂ
      {m:YM.Maxwell.Slot g.core→₀ℕ|Finsupp.weight (fun i=>i.1+2) m≤d} ∧
        ∀(u:g.core.El)(T:YM.Maxwell.TaylorTower g.core),
          YM.Maxwell.probe (YM.Extra.FD.stain u T) f=YM.Maxwell.probe T f:=
  admissible g d f

end IssuedMaxwell.SectorSpine
end
