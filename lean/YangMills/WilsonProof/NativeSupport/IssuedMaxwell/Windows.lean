import YM.XSpace.Symphony
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.Tangents
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.Windows
open YM YM.XSpace.Normalize
open YangMills.MSbar
open IssuedMaxwell.Reports (B printed window)
variable {g:YangMills.GaugeGroup}{d:ℕ}
variable (W:Position.Screen (B g) d)
variable (cleared:∀ z,Position.IsChange (B g) d (W.weights z))

def lifted:(Fin W.size→ℂ)→ₗ[ℝ]Change g.core d:=
  W.weights.codRestrict _ fun z=>(IssuedMaxwell.Tangents.original _).mpr (cleared z)

def screened:Screen g.core d where
  D:=(lifted W cleared).comp (LinearMap.pi fun i=>watch (window (W.window i)))
  observable:=⟨W.size,fun i=>window (W.window i),lifted W cleared,fun _=>rfl⟩

def survey:Fray (screened W cleared):=
  ⟨W.size,fun i=>window (W.window i),lifted W cleared,fun _=>rfl⟩

theorem read (P:Prediction g.core d):
    ((screened W cleared).D P).val=W.read (printed P):=rfl

theorem original:
    (survey W cleared).n=W.size ∧
    (∀ i:Fin W.size, ((survey W cleared).scope i).t = (W.window i).profile) ∧
    (∀ i:Fin W.size, ((survey W cleared).scope i).p = (W.window i).fields) ∧
    (∀ z:Fin W.size→ℂ,((survey W cleared).tally z).val=W.weights z) ∧
    ∀P:Prediction g.core d,((screened W cleared).D P).val=W.read (printed P):=
  ⟨rfl,fun _=>rfl,fun _=>rfl,fun _=>rfl,read W cleared⟩
end IssuedMaxwell.Windows
end
