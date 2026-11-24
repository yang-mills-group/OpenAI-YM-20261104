import YM.Integration.WilsonOriginalPublicTrialPhaseTurn
import YM.Integration.WilsonOriginalPublicTrialPhaseTiles

/-! The centered original tiling moves each compensated word through its actual
predecessor mesh and the same issued gauge door. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseTileInvoice
open Finset Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local RelayDifference.Opening Next.Foundations
open MergeProof MergeProof.Accent PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open OPE.Therm Push.AbsoluteSums.Animals Extra.Multi
open WilsonPositionProgramBlockedTrialAddBack
open RG05Readout RG05Readout.Address Offsets
open Extra.Multi MergeProof.Ribbons
open scoped Classical BigOperators ContDiff
variable {G:Gauge} (R:Run G)
variable {m N per:ℕ}{T:Campaign R}
local notation "C" => R.family
local notation "A" => R.alloy.B.a
local notation "S" => (C).path
local notation "P" => (S).rep N per (m+1)
local notation "Q" => (S).rep N per m
local notation "O" => (S).levels.clock.op m per


open Cells Push.GridApprox
open WilsonOriginalPublicTrialPhaseTiles (motion)

private theorem offset {j:ℕ}(jm : j ≤ m)
    (i:(tilesAt (C).S per (jm.trans m.le_succ)).Cell):
    (tilesAt (C).S per (jm.trans m.le_succ)).translateBy i=
    (O).ratio.embed ((tilesAt (C).S per jm).translateBy i):=by
  rw [tile_translate,tile_translate]
  exact (anchor_next (C).S per jm i).symm

/-- The upper and lower moves use precisely the centers and handedness of this same tile. -/
theorem original (stock:RG05Readout.Many.Storage (C) R.doors)(live:m<N)
    {j:ℕ}(jm : j ≤ m)(v:(tilesAt (C).S per (jm.trans m.le_succ)).Cell)(o:Site ((C).side (m+1) per))
    {P₀:Three G ((C).side (m+1) per)}{P₁:Three G ((C).side m per)}
    (d:ℕ)(fee:ℝ)
    (step:Ride (O) o ((O).ratio.parent o) (R.doors N per m live) ((((C).S.block m).val:ℂ)^d) P₀ P₁ fee):
    let T:=tilesAt (C).S per (jm.trans m.le_succ)
    let U:=tilesAt (C).S per jm
    let s:=motion T v
    ∀ (π:(P).activities.Moves s.1 (T.translateBy v))(μ:(Q).activities.Moves s.1 (U.translateBy v)),
    Ride (O) (T.copyMap v o) ((O).ratio.parent (T.copyMap v o))
      (R.doors N per m live) ((((C).S.block m).val:ℂ)^d) (RG05Readout.View.spin s π P₀)
      (RG05Readout.View.spin s μ P₁) fee:=by
  intro T U s π μ
  have eq:T.translateBy v=(O).ratio.embed (U.translateBy v):=offset R jm v
  have applyAt (x:Site ((C).side (m+1) per))(eq:x=(O).ratio.embed (U.translateBy v))
      (π':(P).activities.Moves s.1 x):Ride (O) (affine s.1 x o) ((O).ratio.parent (affine s.1 x o))
      (R.doors N per m live) ((((C).S.block m).val:ℂ)^d) (RG05Readout.View.spin s π' P₀)
      (RG05Readout.View.spin s μ P₁) fee:=by
    subst x
    exact WilsonOriginalPublicTrialPhaseTurn.original R stock live s (U.translateBy v) o π' μ d fee step
  exact applyAt (T.translateBy v) eq π

end YM.Integration.WilsonOriginalPublicTrialPhaseTileInvoice
end
