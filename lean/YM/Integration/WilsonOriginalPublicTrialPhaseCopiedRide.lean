import YM.Integration.WilsonOriginalPublicTrialPhasePaidBoard
import YM.Integration.WilsonOriginalPublicTrialPhaseTileInvoice

/-! Every physical tile keeps both prescribed invoices through the original door. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseCopiedRide
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Cells
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent Marker
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign MergeProof.Ribbons
open RG05Readout RG05Readout.Address RG05Readout.Many
open WilsonOriginalPublicTrialPhaseCoFiled (copies)
open WilsonOriginalPublicTrialPhaseTiles (motion)
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){N j m per:ℕ}{I:Type}[Fintype I][DecidableEq I]
local notation "C" => R.family
local notation "H" => (C).path
local notation "P" => (H).rep N per (m+1)
local notation "Q" => (H).rep N per m
local notation "O" => (H).levels.clock.op m per

private theorem zero_location {n:Side}(T:Tiling n)(z:Site n):T.copyMap 0 z=z:=by
  simp [Tiling.copyMap,T.omega_zero,T.transport_zero,affine]

set_option maxHeartbeats 480000 in
omit [Fintype I] [DecidableEq I] in
theorem original (stock:RG05Readout.Many.Storage (C) R.doors)(hm:m<N)(jm : j ≤ m)
    (z:I→Site ((C).side (m+1) per))(d:I→ℕ)(l:I→ℝ)
    (X:I→Three G ((C).side (m+1) per))(Y:I→Three G ((C).side m per))
    (step:∀i,Ride (O) (z i) ((O).ratio.parent (z i)) (R.doors N per m hm)
      ((((C).S.block m).val:ℂ)^(d i)) (X i) (Y i) (l i)):
    let T:=tilesAt (C).S per (jm.trans m.le_succ)
    let U:=tilesAt (C).S per jm
    ∀ (π:∀v,(P).activities.Moves (motion T v).1 (T.translateBy v))
      (μ:∀v,(Q).activities.Moves (motion U v).1 (U.translateBy v))(i:T.Cell×I),
      Ride (O) (T.copyMap i.1 (z i.2)) ((O).ratio.parent (T.copyMap i.1 (z i.2)))
        (R.doors N per m hm) ((((C).S.block m).val:ℂ)^(d i.2))
        (copies (P) 0 (motion T) T.translateBy π X i)
        (copies (Q) 0 (motion U) U.translateBy μ Y i) (l i.2):=by
  intro T U π μ i
  rcases i with ⟨v,i⟩
  by_cases atHome:v=0
  · subst v
    have upper:copies (P) 0 (motion T) T.translateBy π X (0,i)=X i:=if_pos rfl
    have lower:copies (Q) 0 (motion U) U.translateBy μ Y (0,i)=Y i:=if_pos rfl
    let S:=fun o X₁ Y₁=>Ride (O) o ((O).ratio.parent o) (R.doors N per m hm)
      ((((C).S.block m).val:ℂ)^(d i)) X₁ Y₁ (l i)
    apply Eq.mpr (congrArg₂ (S (T.copyMap 0 (z i))) upper lower)
    exact (congrArg (fun o=>S o (X i) (Y i)) (zero_location T (z i))).mpr (step i)
  · have paid:=WilsonOriginalPublicTrialPhaseTileInvoice.original R stock hm jm v (z i)
       (d i) (l i) (step i) (π v) (μ v)
    have upper:copies (P) 0 (motion T) T.translateBy π X (v,i)=
        RG05Readout.View.spin (motion T v) (π v) (X i):=if_neg atHome
    have lower:copies (Q) 0 (motion U) U.translateBy μ Y (v,i)=
        RG05Readout.View.spin (motion U v) (μ v) (Y i):=if_neg atHome
    let o:=T.copyMap v (z i)
    let S:=fun X₁ Y₁=>Ride (O) o ((O).ratio.parent o) (R.doors N per m hm)
      ((((C).S.block m).val:ℂ)^(d i)) X₁ Y₁ (l i)
    exact (congrArg₂ S upper lower).mpr paid

end YM.Integration.WilsonOriginalPublicTrialPhaseCopiedRide
end
