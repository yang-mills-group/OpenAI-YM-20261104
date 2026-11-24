import YM.Integration.WilsonThermometerFundedWeakCells
import YM.Integration.WilsonPositionThermometerStationUnit
import YM.Integration.WilsonPositionGradedThermometerHearing
import YM.Integration.WilsonPositionPrescribedLeading

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOriginalMeans
open Function Filter Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS XSpace XSpace.Normalize XSpace.Rose
open WilsonPositionThermometerCapStation WilsonPositionCapTransport WilsonPositionThermometerGradedSource
open WilsonPositionThermometerGradedReading WilsonPositionCorrectedCap WilsonSeparatedOriginalThermometerCells
open WilsonThermometerMarchProduct (field)
open scoped Topology BigOperators Classical
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}

def one (C : Family G) {d : ℕ} (z : ℕ×ℕ) (v:C.label d) (o:Site (C.side z.1 z.2)) : ℂ :=
  Wilson.moment (C.beta z.1 z.2) (C.O z.1 z.2 v o)

theorem location (C : Family G) {d : ℕ} (z : ℕ×ℕ) (v:C.label d) (o u:Site (C.side z.1 z.2)) :
    one C z v o = one C z v u := by
  have shifted : C.O z.1 z.2 v o = C.O z.1 z.2 v u ∘ pull 1 (o-u) := by
    funext U
    simp only [Function.comp_apply,pull_one,C.translation]
    rw [show u+(o-u)=o by abel]
  have cont : Continuous (C.O z.1 z.2 v u) := C.continuousO ..
  have paid : Integrable (C.O z.1 z.2 v u) (law G _ (C.beta z.1 z.2)) :=
    cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold one
  rw [shifted,moment_pull _ _ _ _ paid]

variable {H : (Bel R.family.book).Hierarchy} {Y:Ultrafilter (ℕ×ℕ)}

theorem occupied (Z:Group R.family 6) (checked:Z.station.checked f H Z.horizon)
    (fixes:∀j : Fin 7,Z.change j ((Bel R.family.book).unit j)=(Bel R.family.book).unit j) :
    ∀ᶠ z:(ℕ×ℕ) in f.fuse, ∀ s:Badge,∀ o:Fin 3→Site (R.family.side z.1 z.2),
      row Z z o s =
       Wilson.moment (R.family.beta z.1 z.2) (fun U=>∏ i∈s,R.family.O z.1 z.2 (field Z z.1 z.2 Finset.univ i) (o i) U) := by
  filter_upwards [eventually_all.mpr (fun i:Fin 3=>
    WilsonPositionThermometerStationUnit.original Z.station (index Z (grade i)) R.makes checked)] with z bank s o
  change (∫ U, ∏ i, R.family.O z.1 z.2 (field Z z.1 z.2 s i) (o i) U ∂_) = _
  congr 1
  funext U
  have per (i:Fin 3) : R.family.O z.1 z.2 (field Z z.1 z.2 s i) (o i) U =
      if i∈s then R.family.O z.1 z.2 (field Z z.1 z.2 Finset.univ i) (o i) U else 1 := by
    by_cases hi:i∈s
    · rw [if_pos hi,WilsonThermometerFundedWeakCells.occupied Z z.1 z.2 s i hi]
    · rw [if_neg hi]
      change R.family.O z.1 z.2 (Z.station.wheel.atCut z (index Z (grade i)) (Z.change (grade i) (source R.family s i))) (o i) U = 1
      rw [WilsonPositionThermometerGradedSource.unit R.family s i hi,fixes]
      exact congrFun ((bank i).2 (o i)) U
  simp_rw [per]
  simp

variable (F : Final R.family f S) (J : ℝ→PhysMS.tower S) (V : Store G) (A : ℝ→Group R.family 6)
local notation "Pθ" => WilsonPositionPrescribedFrame.positioned F J V

theorem original (simple:G.Simple) (lead:Leading F J)
    (obeys:∀d,∀ᶠ r in trail,PhysMS.Frame.obedient F H (J r) d)
    (book : Book (f:=f) (l:=Y) (H:=H) A J) (prior:(Y:Filter _)≤f.fuse) {δ:ℝ} (hp:0<δ) :
    ∀ᶠ rz in trail.curry (Y:Filter _), let Z:=adjusted F J V A rz.1
      ∀ i:Fin 3,∀ o:Site (R.family.side rz.2.1 rz.2.2),
       ‖one R.family rz.2 (field Z rz.2.1 rz.2.2 Finset.univ i) o‖<δ := by
  let x : Points 3 := points (fun i=>position 0 (i.val:ℝ))
  have sep : x∈conf 3 := by
    intro i j eq
    have tt:=congrArg time eq
    change time (position 0 (i.val:ℝ))=time (position 0 (j.val:ℝ)) at tt
    simp only [time_position] at tt
    apply Fin.ext
    exact_mod_cast tt
  have inside : ({x}:Set (Points 3))⊆conf 3 := by simpa only [singleton_subset_iff]
  have priced:=WilsonPositionPrescribedLeading.rose F J V lead obeys simple (isCompact_singleton (x:=x)) inside (half_pos hp)
  apply eventually_curry_iff.mpr
  filter_upwards [priced,WilsonPositionCorrectedCap.original F J V A book lead 0,
    WilsonPositionGradedThermometerHearing.measured F J V lead,RG17.positiveLength] with r small filed lands rp
  let Z:=adjusted F J V A r
  have rows:=WilsonPositionThermometerGradedReading.cut F Pθ r Z simple prior filed.2.2.2.1
    (fun s i=>((filed.2.2.2.2.1 (grade i)).2.2 _).symm) lands rp (isCompact_singleton (x:=x)) inside (half_pos hp)
  filter_upwards [rows,prior (occupied Z filed.2.1 (fun j=>(filed.2.2.2.2.1 j).2.1))] with z atSite same
  dsimp only
  intro i o
  let places := positions (R:=R) r z x
  have reach := atSite {i} x (mem_singleton x)
  have unitFace := same {i} places
  have sing : WilsonPositionThermometerGradedReading.moment r Z z x {i} =
    one R.family z (field Z z.1 z.2 Finset.univ i) o := by
    change row Z z places {i}=_
    rw [unitFace]
    simp only [Finset.prod_singleton]
    exact location R.family z (field Z z.1 z.2 Finset.univ i) (places i) o
  rw [←sing]
  have zero:=small {i} x (mem_singleton x) (Finset.singleton_nonempty i)
  calc _ ≤ ‖WilsonPositionThermometerGradedReading.moment r Z z x {i} -
        WilsonPositionThermometerReading.sample F Pθ r x {i}‖ +
        ‖WilsonPositionThermometerReading.sample F Pθ r x {i}‖ := norm_le_norm_sub_add _ _
    _ < δ := by linarith

end YM.Integration.WilsonThermometerOriginalMeans
end

