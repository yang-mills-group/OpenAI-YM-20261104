import YM.Integration.WilsonMaxwellThermometerNominatedGroundCredit
import YM.Integration.WilsonMaxwellThermometerNominatedGroundProgram
import YM.Integration.WilsonMaxwellThermometerNominatedCofactor
import YM.Integration.WilsonThermometerCourseIntake

/-! The compensated Maxwell-weighted credit is a fixed physical observable.
Its actual Wilson read is the linear principal term used by the connected
comparison, with the missing unit legs restored before taking the UV limit. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedGroundMoment
open Set Finset Filter MeasureTheory Lattice Wilson Labels RG Source PhysicalNext.Repeat.Legato RG17
open OPE OPE.Orbits Table Spec PhysMS PhysMS.Frame Maxwell Maxwell.Free XSpace XSpace.Rose XSpace.Normalize
open Marker QuadraticLocal Primitives.GCC.Anchor Climb Next.UVStress Trace Trace.Pilot Extraction
open WilsonPositionCapTransport WilsonPositionThermometerGradedSource WilsonPositionThermometerCapStation
open WilsonCenteredPhysicalPanel WilsonMaxwellThermometerNominatedGroundCell
open WilsonThermometerAlignedCells WilsonThermometerCourseIntake
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) (A:Group R.family 6)
local notation "d₀" => fun i:Fin 3=>(grade i).val
local notation "roster" z => WilsonCapturedPrimaryWardThermometer.input R A z (Finset.univ:Badge)
local notation "C" => R.family
local notation "cfg" z => Config G ((C).side (z).1 (z).2)
local notation "site" => WilsonCenteredCompactBooking.site
local notation "W" => WilsonMaxwellThermometerNominatedGroundPurse.policy R
local notation "map!" => WilsonMaxwellThermometerNominatedCofactor.mean R
local notation "J₀" => Stock.census (Fin 3)

def face (z:ℕ×ℕ) (o:Sites R z 3) (s:Badge):C(cfg z,ℂ):=
  let relative:=WilsonCapturedPrimaryPhysicalArray.registered o (some (0:Fin 3))
  ⟨WilsonCapturedPrimaryWardRestoration.filed R d₀ (roster z) s relative,
   continuous_finsetProd _ (fun i _=>(C).continuousO z.1 z.2 ((d₀) i) ((roster z) i) (relative i))⟩

def integrated (r:ℝ) (z:ℕ×ℕ) (φ:Test 3):C(cfg z,ℂ):=
  ∑o:Sites R z 3,∑s:Badge,WilsonMaxwellThermometerNominatedGroundWeights.payment R φ (site R r z) o (mode s) • face R A z o s

theorem field (r:ℝ) (z:ℕ×ℕ) (φ:Test 3) (U:cfg z):
    integrated R A r z φ U=φ.applyTo (fun x=>∑s:Badge,
      WilsonThermometerCenteredAlgebra.weight (W x) (mode s)*face R A z (site R r z x) s U):=by
  have m:Measurable (site R r z:Points 3→Sites R z 3):=WilsonSeparatedOriginalThermometerCells.placed r z
  have eq:=WilsonMaxwellThermometerNominatedGroundCell.taken R φ (site R r z) m (fun o s=>face R A z o s U)
  simpa only [integrated,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul] using eq.symm

theorem read (r:ℝ) (z:ℕ×ℕ) (φ:Test 3):
    (C).omega z.1 z.2 (integrated R A r z φ)=φ.applyTo (fun x=>∑s:Badge,
      WilsonThermometerCenteredAlgebra.weight (W x) (mode s)*(C).omega z.1 z.2 (face R A z (site R r z x) s)):=by
  have m:Measurable (site R r z:Points 3→Sites R z 3):=WilsonSeparatedOriginalThermometerCells.placed r z
  have eq:=WilsonMaxwellThermometerNominatedGroundCell.taken R φ (site R r z) m (fun o s=>(map! z.1 z.2) (face R A z o s))
  change (map! z.1 z.2) (integrated R A r z φ)=φ.applyTo (fun x=>∑s:Badge,
      WilsonThermometerCenteredAlgebra.weight (W x) (mode s)*(map! z.1 z.2) (face R A z (site R r z x) s))
  simpa only [integrated,map_sum,map_smul,smul_eq_mul] using eq.symm

theorem faces {f:Extraction.Order} {H:(Bel (C).book).Hierarchy}
    (checked:A.station.checked f H A.horizon) (unit:∀t:Fin 7,A.change t ((Bel (C).book).unit t)=(Bel (C).book).unit t):
    ∀ᶠz:ℕ×ℕ in f.fuse,∀(o:Sites R z 3) (s:Badge),
      (C).omega z.1 z.2 (face R A z o s)=WilsonPositionThermometerGradedReading.row A z o s:=by
  have dated:∀ᶠz:ℕ×ℕ in f.fuse,∀i:Fin 3,(C).ref ((d₀) i)≤z.1:=eventually_all.mpr fun i=>large_mesh f _
  filter_upwards [dated,WilsonThermometerCourseIntake.subwords R A checked unit] with z ready eligible o s
  let y:=offsets o
  have same:WilsonCapturedPrimaryPhysicalArray.registered o (some (0:Fin 3))=atOrigin y:=by
    funext i;fin_cases i <;> simp [WilsonCapturedPrimaryPhysicalArray.registered,atOrigin,offsets,y]
  have placedAtOrigin:placedAt y (o 0)=o:=by
    funext i;fin_cases i <;> simp [atOrigin,placedAt,offsets,y]
  have credit:(face R A z o s:Config G (R.family.side z.1 z.2)→ℂ)=WilsonThermometerCourseIntake.placed R A z s (atOrigin y):=by
    funext U
    change WilsonCapturedPrimaryWardRestoration.filed R d₀ (roster z) s _ U=_
    rw [same,eligible]
    rfl
  rw [credit]
  change WilsonPositionThermometerGradedReading.row A z (atOrigin y) s=_
  exact (congrFun (WilsonThermometerAlignedCells.translated A z ready y (o 0)) s).symm.trans (congrArg (fun o=>WilsonPositionThermometerGradedReading.row A z o s) placedAtOrigin)

theorem original {f:Extraction.Order} {S:Table (C).book} (F:Final C f S) (J:ℝ→tower S) (V:Store G)
    (A':ℝ→Group (C) 6) {Y:Ultrafilter (ℕ×ℕ)} {H:(Bel (C).book).Hierarchy}
    (prior:(Y:Filter _)≤f.fuse) (book:Book (f:=f) (l:=Y) (H:=H) A' J) (lead:Leading F J) (φ:Test 3):
    ∀ᶠ w:ℝ×(ℕ×ℕ) in trail.curry (Y:Filter _),
      let Z:=WilsonPositionCorrectedCap.adjusted F J V A' w.1
      (C).omega w.2.1 w.2.2 (integrated R Z w.1 w.2 φ)=
        φ.applyTo (fun x=>∑s:Badge,WilsonThermometerCenteredAlgebra.weight (W x) (mode s)*
          WilsonPositionThermometerGradedReading.moment w.1 Z w.2 x s):=by
  have enrolled:=WilsonPositionCorrectedCap.original F J V A' book lead
  apply eventually_curry_iff.mpr
  filter_upwards [enrolled 0] with r qualified
  let Z:=WilsonPositionCorrectedCap.adjusted F J V A' r
  have words:∀ᶠz in f.fuse,∀(o:Sites R z 3)(s:Badge),(C).omega z.1 z.2 (face R Z z o s)=WilsonPositionThermometerGradedReading.row Z z o s:=
    faces R Z qualified.2.1 (fun j=>(qualified.2.2.2.2.1 j).2.1)
  filter_upwards [words.filter_mono prior] with z same
  change (C).omega z.1 z.2 (integrated R Z r z φ)=_
  rw [read R Z r z φ]
  congr 1
  funext x
  exact Finset.sum_congr rfl (fun s _=>congrArg (fun y=>_*y) (same (site R r z x) s))

end YM.Integration.WilsonMaxwellThermometerNominatedGroundMoment
