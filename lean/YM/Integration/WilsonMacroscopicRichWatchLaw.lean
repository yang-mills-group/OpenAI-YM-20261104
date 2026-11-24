import YM.Integration.WilsonMacroscopicRichWatchPlot
import YM.Integration.WilsonMacroscopicRichCorrelatedTest

/-! The physical watch subtracts the full finite counterterm within one normalized Wilson integral. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichWatchLaw
open Function Set Filter MeasureTheory Lattice Cells Wilson Next.UVStress
open RG16 RG16.Literal WilsonMacroscopicRichFixedWatchSale
open scoped BigOperators Topology Classical
variable {G:Gauge}(C:Family G){N per:ℕ}{s:ℕ}
local notation "X"=>Config G (C.side N per)

def meter (W:Watch C) : C(X,ℂ)→ₗ[ℂ]ℂ:=
  WilsonMacroscopicRichCorrelatedTest.meter (law G (C.side N per) (C.beta N per)) id
    measurable_id (W.plot N per) (C.integrableR W.q (W.among N per))

theorem same (W:Watch C)(Y:C(X,ℂ)):
    meter C W Y=moment (C.beta N per) (fun U=>Y U*W.plot N per U):=by
  unfold meter WilsonMacroscopicRichCorrelatedTest.meter
  change (∫U,W.plot N per U*Y U ∂law G _ _)=_
  simp only [moment,mul_comm]

theorem sub {a:ℕ}(W:Fin a→Watch C)(Y:C(X,ℂ))(z:C.label s):
    heard W (N,per) ((Y:X→ℂ)-C.O N per z 0)=
      heard W (N,per) (Y:X→ℂ)-heard W (N,per) (C.O N per z 0):=by
  let Z:C(X,ℂ):=⟨C.O N per z 0,C.continuousO N per s z 0⟩
  funext i
  change moment _ (fun U=>(Y U-Z U)*(W i).plot N per U)=
    moment _ (fun U=>Y U*(W i).plot N per U)-
    moment _ (fun U=>Z U*(W i).plot N per U)
  exact (same C (W i) (Y-Z)).symm.trans (((meter C (W i)).map_sub Y Z).trans
    (congrArg₂ (·-·) (same C (W i) Y) (same C (W i) Z)))

theorem decoded {a:ℕ}{V:Type*}[NormedAddCommGroup V][NormedSpace ℂ V]
    (W:Fin a→Watch C)(D:(Fin a→ℂ)→L[ℂ]V)(Y:C(X,ℂ))(z:C.label s):
    D (heard W (N,per) (C.O N per z 0))=
      D (heard W (N,per) (Y:X→ℂ))-D (heard W (N,per) ((Y:X→ℂ)-C.O N per z 0)):=by
  rw [sub C W Y z,map_sub]
  abel

end YM.Integration.WilsonMacroscopicRichWatchLaw
