import YM.Integration.WilsonOlderFreshSoftSocketVane
import YM.Integration.WilsonOlderFreshSoftSocketPublicSlots

/-! The issued station's own cutoff field funds its original guarded experiment. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketStationBook
open Function Filter Finset Lattice Wilson RG Source Labels
open Next.Rank Next.Rank.Price Next.Rank.Atlas Next.Rank.Station Further.CorrectedLift
open Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East PhysicalNext.Repeat.Legato
open WilsonOlderFreshSoftRoseCourse (grade)
open WilsonOlderFreshSoftRoseMesh (filed)
open WilsonOlderFreshSoftSocketVane (quotaFare)
open WilsonOriginalMicroscopicGuardedGridSchool (Finished)
open scoped Topology BigOperators Classical

variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
local notation "C" => R.family

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (wide:∀j,1≤((C).path.levels.budget j).supportExponent)(quote:OPE.Therm.Poetry (C).path.levels)
    (target:ℕ){η:ℝ}(ep:0<η):
    ∃start:ℕ,∀A:WilsonPositionThermometerCapStation.Group C 6,start≤A.station.k→
      A.station.checked f H A.horizon→
        Finished R grade (fun _=>A.station.k) target η (quotaFare R A) (filed R A) ∧
        ∀i,0≤quotaFare R A i:=by
  obtain ⟨first,earned⟩:=eventually_atTop.mp (WilsonOlderFreshSoftSocketVane.original (f:=f) (H:=H) R simple)
  obtain ⟨second,school⟩:=WilsonOriginalMicroscopicGuardedDated.original R simple shop wide quote grade target ep
  refine ⟨max first second,?_⟩
  intro A late checked
  have sold:=earned A.station.k ((le_max_left ..).trans late) A rfl checked
  constructor
  · apply school (fun _=>A.station.k) (fun _=>(le_max_right ..).trans late)
    intro i N per live
    exact sold N per live i
  · intro i
    have q:=sold (A.station.k+1) 0 (Nat.lt_succ_self _) i
    apply le_trans _ q
    unfold Next.UVStress.quota Frame.coeffSize
    exact Finset.sum_nonneg fun _ _=>norm_nonneg _

end YM.Integration.WilsonOlderFreshSoftSocketStationBook
end
