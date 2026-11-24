import YM.Integration.WilsonPositionProgramNominatedPhysicalResponse
import YM.Integration.WilsonPositionProgramNominatedMenuInvoice
import Mathlib.Order.Filter.Curry

/-! The original physical UV limit at each period precedes the increasing
period limit.  The same changing published vector occurs on both sides. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramNominatedOrderedReturn
open Function Filter Finset Lattice Wilson Labels RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price WilsonOriginalThermometerPalette WilsonPositionThermometerCapStation
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Fountain
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.PathCost
open WilsonCoeffUV.Winding WilsonCoeffUV.Layout WilsonCoeffUV.Blue WilsonCoeffUV.Shard WilsonCoeffUV.Embroider
open Source Source.Drops WilsonPositionProgramThermometerCoordinates
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramNominatedRoster (selected)
open WilsonPositionProgramNominatedWinding (unitFare)
open WilsonPositionProgramNominatedPublicScalar (finite)
open WilsonPositionProgramNominatedPhysicalProfile (zoomFactor covers)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}{e k u D:ℕ}
variable {I:Type} [Fintype I]


open WilsonPositionProgramNominatedPhysicalResponse (difference)
open WilsonPositionProgramNominatedMenuInvoice (issued)
theorem original (simple:G.Simple)(readout:RG05Preconstruction.ReadoutPurchase R.b)(paid:issued G R.kit)
    (big:0<D)(rails:Rails 0 k u e)(arity:I→ℕ)(child:(s:I)→Fin (arity s+1)→Fin 3)
    (d:(s:I)→Fin (arity s+1)→ℕ)(fit:∀s i,levels (child s i)<d s i)
    (cap:∀s,capP (deck (G:=G) (levels ∘ child s) (d s) (fit s)) ≤ k)
    (φ:(s:I)→Wilt (deck (G:=G) (levels ∘ child s) (d s) (fit s)))
    (apart:∀s i j,i≠j → Disjoint (tsupport (φ s i).ψ.val) (tsupport (φ s j).ψ.val)):
    let L:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,1 ≤ zz L m →
    ∀A:Group R.family 6,A.station.k=m → ∀checked:A.station.checked f H A.horizon,
    ∀(phase:Fin 3→ℂ →L[ℝ] ℝ)(s:ℕ×ℕ→I)(t:ℕ×ℕ→Fin (e+1))(i:ℕ×ℕ→Alma ((primes G).F 0)),
      Tendsto (fun q:ℕ×ℕ=>difference R arity child d fit big φ A checked m q.2 q.1 q.2 q.1 k
        phase (s q) (t q) (i q)) ((atTop:Filter ℕ).curry atTop) (𝓝 0):=by
  intro L
  have income(s:I):WilsonPositionProgramUniformWindingTable.Complete R (levels ∘ child s) (d s) (fit s)
      e unitFare 1:=WilsonPositionProgramNominatedMenuInvoice.original R simple readout paid _ _ _ _ _ zero_lt_one
  have ready:=WilsonPositionProgramNominatedPhysicalResponse.original (f:=f) (H:=H) R arity child d fit
    simple _ paid.1 big rails cap 1 1 zero_lt_one income φ apart
  filter_upwards [ready] with m named
  intro strip A date checked phase s t i
  apply Metric.tendsto_nhds.mpr
  intro ε pos
  obtain ⟨K,floor,hear⟩:=named strip A date checked phase ε pos
  apply eventually_curry_iff.mpr
  filter_upwards [hear] with p estimate
  filter_upwards [eventually_ge_atTop (K+1)] with N top
  rw [dist_zero_right]
  exact estimate N p N (by omega) (by omega) _ _ _

end YM.Integration.WilsonPositionProgramNominatedOrderedReturn
end
