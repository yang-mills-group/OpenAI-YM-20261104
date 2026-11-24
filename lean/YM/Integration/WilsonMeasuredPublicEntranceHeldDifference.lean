import YM.Integration.WilsonSeparatedPrefixFixedFlatEar
import YM.Integration.WilsonOriginalMicroscopicEntranceFlatEar

/-! The signed withdrawal is taken on the original earlier conditional, with a single denominator. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceHeldDifference
open Function Finset Set MeasureTheory Lattice Wilson RG 
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato 
open WilsonOriginalMicroscopicEntranceDeposits (funded)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){N per K f b:ℕ}
local notation "C" => R.family
local notation "X" j:max => Config G ((C).side j per)
local notation "P" => (C).path.rep N per f

theorem withdraw (live:K≤N)(fk:f≤K)(bf:b≤f)(trueField:X K→ℂ)(head:X f→ℂ)
    (physical:funded trueField)(regular:Integrable (fun U=>((P).eval U:ℂ)*head U) (prior G _))(W:X b):
    actualTransport (C) (N:=N) (fun U=>actualTransport (C) (N:=N) trueField fk U-head U) bf W=
      actualTransport (C) (N:=N) trueField (bf.trans fk) W-actualTransport (C) (N:=N) head bf W:=by
  obtain ⟨M,bounded⟩:=physical.2
  have a:=actualTransport_weighted_integrable (C) R.makes live physical.1.aestronglyMeasurable bounded fk
  have paid:Integrable (fun U=>(P).eval U • head U) (prior G _):=by simpa only [Complex.real_smul] using regular
  have linear:=congrFun (ActualWilsonAbsoluteTransport.sub (C) R.makes (fk.trans live) a paid bf) W
  simpa only [actualTransport_tower (C) R.makes live,Pi.sub_apply] using linear

theorem before (live:K≤N)(fk:f≤K)(bf:b≤f)(raw:X N→ℂ)(guard:X K→ℂ)(entered:X K→ℂ)(x y:X f→ℂ)
    (wholesome:funded raw)(cropped:funded guard)
    (xr:Integrable (fun U=>((P).eval U:ℂ)*x U) (prior G _))
    (yr:Integrable (fun U=>((P).eval U:ℂ)*y U) (prior G _))(W:X b):
    let atN:=actualTransport (C) (N:=N) raw (bf.trans (fk.trans live)) W
    let atK:=actualTransport (C) (N:=N) entered (bf.trans fk) W
    let old:=actualTransport (C) (N:=N) (fun U=>actualTransport (C) (N:=N) raw (fk.trans live) U-x U) bf W
    let exchange:=actualTransport (C) (N:=N) x bf W-actualTransport (C) (N:=N) y bf W
    let trial:=actualTransport (C) (N:=N) (fun U=>actualTransport (C) (N:=N) guard fk U-y U) bf W
    let halo:=atK-actualTransport (C) (N:=N) guard (bf.trans fk) W
    atN-atK=old+exchange-trial-halo:=by
  dsimp only
  rw [withdraw R (le_refl N) (fk.trans live) bf raw x wholesome xr W,
    withdraw R live fk bf guard y cropped yr W]
  ring

end YM.Integration.WilsonMeasuredPublicEntranceHeldDifference
end
