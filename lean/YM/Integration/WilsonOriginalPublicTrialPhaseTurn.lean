import YM.Integration.WilsonOriginalPublicTrialPhaseFirstRide
import YM.RG05Readout.Many.View
import YM.RG05Readout.Many.Tour

/-! The original address grant for one compensated word travels on each actual
blocking-compatible reflection and translation, with its occupied inventory. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseTurn
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


/-- Both inventories on the original signed step are transported by their elected moves. -/
theorem original (stock:RG05Readout.Many.Storage (C) R.doors)(live:m<N)
    (s:Motion)(y:Site ((C).side m per))(o:Site ((C).side (m+1) per))
    (π:(P).activities.Moves s.1 ((O).ratio.embed y))(μ:(Q).activities.Moves s.1 y)
    {P₀:Three G ((C).side (m+1) per)}{P₁:Three G ((C).side m per)}
    (d:ℕ)(fee:ℝ)
    (step:Ride (O) o ((O).ratio.parent o) (R.doors N per m live) ((((C).S.block m).val:ℂ)^d) P₀ P₁ fee):
    let i:=affine s.1 ((O).ratio.embed y) o
    Ride (O) i ((O).ratio.parent i) (R.doors N per m live) ((((C).S.block m).val:ℂ)^d)
      (RG05Readout.View.spin s π P₀) (RG05Readout.View.spin s μ P₁) fee:=by
  intro i
  obtain ⟨a,b,paid⟩:=stock.exactMoon.days N per m live
  have course:RG05Readout.Many.Coursework (S) _ _ _ a b:=⟨paid.2,paid.1⟩
  have fixed:Motion.scalar s ((((C).S.block m).val:ℂ)^d)=(((C).S.block m).val:ℂ)^d:=by
    unfold Motion.scalar
    split
    · simp
    rfl
  have realStep:=RG05Readout.View.paid R.makes live course.publishes.propagate fixed step
    (RG05Readout.View.signpost_use R.makes live s π step.old)
    (RG05Readout.View.signpost_use R.makes live.le s μ step.tomorrow)
    (RG05Readout.View.spin_at s π) (RG05Readout.View.spin_at s μ)
  rw [show (O).ratio.parent i=affine s.1 y ((O).ratio.parent o) from
    Local.parent_affine (O).ratio ((C).S.block_odd m) s.1 y o]
  exact realStep

end YM.Integration.WilsonOriginalPublicTrialPhaseTurn
end
