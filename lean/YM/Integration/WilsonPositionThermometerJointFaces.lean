import YM.Integration.WilsonPositionThermometerGradedReading
import YM.Integration.WilsonPositionThermometerStationUnit
import YM.Integration.WilsonPositionThermometerDepositedFaces

/-! Each face is a coordinate of one true three-source density on the selected
Vane, at the literal occupied sites. The same three cutoff fields enter every
face and every conditional step. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionThermometerJointFaces
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec Marker FVA1
open RG12 RG17 Cells OPE OPE.Orbits Climb Trace.Pilot Next.Rank Next.UVStress PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums
open OriginalForcedAddresses Push.GridApprox.Nil XSpace XSpace.Rose
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open scoped Topology Classical BigOperators

variable {G:Gauge} {R:Run G} {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
variable (A:Group R.family 6)
local notation "C" => R.family

def submitted (z:UVIndex) (x:Fin 3→Site (R.family.side z.1 z.2)) (s:Badge) (U:Config G (R.family.side z.1 z.2)) : ℂ :=
  ∏ i, R.family.O z.1 z.2 (A.station.wheel.atCut z (index A (grade i)) (vector A s i)) (x i) U

theorem ensemble (z:UVIndex) (x:Fin 3→Site (R.family.side z.1 z.2)) (s:Badge) :
    row A z x s = R.family.omega z.1 z.2 (submitted A z x s) := rfl

theorem same (checked:A.station.checked f H A.horizon)
    (unit:∀ j, A.change j ((Bel R.family.book).unit j) = (Bel R.family.book).unit j) :
    ∀ᶠ z:UVIndex in f.fuse,∀ (o:Positions (Fin 3) (R.family.side z.1 z.2)) (s:Badge),
    submitted A z o.origin s =
      fun U=>∏ i∈s, WilsonPositionThermometerDepositedFaces.leg R z.1 z.2 A.station
        (fun i=>index A (grade i)) (vector A univ) o i U := by
  have sold:=eventually_all.mpr (fun i:Fin 3=>WilsonPositionThermometerStationUnit.original A.station
     (index A (grade i)) R.makes checked)
  filter_upwards [sold] with z here o s
  funext U
  unfold submitted
  have one (i:Fin 3) :
      R.family.O z.1 z.2 (A.station.wheel.atCut z (index A (grade i)) (vector A s i)) (o.origin i) U =
      if i∈s then WilsonPositionThermometerDepositedFaces.leg R z.1 z.2 A.station
        (fun i=>index A (grade i)) (vector A univ) o i U else 1 := by
    by_cases atSite:i∈s
    · have eq:source C s i=source C univ i := by simp [source,atSite]
      simp only [if_pos atSite,WilsonPositionThermometerDepositedFaces.leg,vector,eq]
    · rw [if_neg atSite,vector,WilsonPositionThermometerGradedSource.unit C s i atSite,unit]
      exact congrFun ((here i).2 (o.origin i)) U
  simp_rw [one]
  simp

def face (s:Badge) : (Replicum.Bud (Fin 3)).Mode := ⟨s,mem_univ _⟩

def density (simple:G.Simple) (z:UVIndex) (o:Positions (Fin 3) (R.family.side z.1 z.2)) :=
    WilsonPositionThermometerDepositedFaces.pages R simple z.1 z.2 A.station
      (fun i=>index A (grade i)) (vector A univ) o

theorem deposited (simple:G.Simple) (checked:A.station.checked f H A.horizon)
    (unit:∀ j, A.change j ((Bel R.family.book).unit j)=(Bel R.family.book).unit j) :
    ∀ᶠ z:UVIndex in f.fuse,∀ (o:Positions (Fin 3) (R.family.side z.1 z.2)) (k:ℕ) (top:k≤z.1),
      Integrable (gust R.family.path z.1 z.2 z.1 (density A simple z o) k top) (prior G _) ∧
      ∀ (s:Badge) (U:Config G (R.family.side k z.2)),
        (gust R.family.path z.1 z.2 z.1 (density A simple z o) k top U).part (face s) =
        (R.family.path.rep z.1 z.2 k).eval U • actualTransport C
          (N:=z.1) (submitted A z o.origin s) top U := by
  have late:=eventually_all.mpr (fun i:Fin 3=>large_mesh f (R.family.ref (index A (grade i))))
  filter_upwards [late,same A checked unit] with z refs full o k top
  refine ⟨WilsonPositionThermometerDepositedFaces.paid R simple z.1 z.2 A.station
    (fun i=>index A (grade i)) (vector A univ) o refs top,?_⟩
  intro s U
  rw [full o s]
  exact WilsonPositionThermometerDepositedFaces.deposited R simple z.1 z.2 A.station
      (fun i=>index A (grade i)) (vector A univ) o refs top (face s) U

end YM.Integration.WilsonPositionThermometerJointFaces
end
