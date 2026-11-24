import YM.Integration.WilsonPositionThermometerStationBasis
import YM.Integration.WilsonPositionPrescribedLeading
import YM.Integration.WilsonPositionThermometerStationFaces
import YM.Integration.WilsonPositionThermometerCorrectedUnit

/-! Keep the original extraction's four-dimensional field normalization
and its signed microscopic lifts on one all-radii tower. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionOriginalOrientedFrame

open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE OPE.Orbits Climb
open PhysicalNext.Repeat.Legato RG17 Trace Trace.Pilot Next.UVStress PhysMS PhysMS.Frame
open XSpace XSpace.Normalize WilsonPositionThermometerOrientedStation
open scoped Topology Classical BigOperators

open private fitted_lead angles_staff from YM.PhysMS.Frame.Stage
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ → tower S) (V : Store G)
    {I : Type} [Fintype I] (b : Module.Basis I ℂ ((Bel R.family.book).Field 6))

def points (A : ℝ → Filing R.family 6 I) (r : ℝ) : Filing R.family 6 (Fin 3) :=
  WilsonPositionThermometerStationBasis.onBasis b (A r) (fun i =>
    WilsonPositionPrescribedLift.field F J V 6 r (WilsonPositionThermometerReading.leg R.family Finset.univ i))

def lamps (A : ℝ → Filing R.family 6 I) (r : ℝ) : Filing R.family 6 (Rose.Badge × Fin 3) :=
  WilsonPositionThermometerStationFaces.roster (points F J V b A r)

private theorem occupied {Y : (Bel R.family.book).Hierarchy} {l : Ultrafilter (ℕ × ℕ)}
    (A : ℝ → Filing R.family 6 I) (paid : ∀ m : ℕ,
      ∀ᶠ r in trail, Filed (f:=f) (Y:=l) Y b r (J r) m (A r))
    (lead : Leading F J) (m : ℕ) :
    ∀ᶠ r in trail, Filed (f:=f) (Y:=l) Y (WilsonPositionThermometerReading.leg R.family Finset.univ)
      r (WilsonPositionPrescribedFrame.positioned F J V r) m (points F J V b A r) := by
  let u (i : Fin 3) := WilsonPositionThermometerReading.leg R.family Finset.univ i
  let w (r : ℝ) (i : Fin 3) := WilsonPositionPrescribedLift.field F J V 6 r (u i)
  let P := WilsonPositionPrescribedFrame.positioned F J V
  have converges (i : Fin 3) : Tendsto (fun r => w r i) trail (𝓝 (u i)) :=
    WilsonPositionPrescribedLeading.applied F J V lead 6 (u i)
  have identity : ∀ᶠ r in trail, ∀ i, P r 6 (u i) = J r 6 (w r i) := Eventually.of_forall fun _ _ => rfl
  exact WilsonPositionThermometerStationBasis.moving (f:=f) (Y:=l) (H:=Y) b J P A paid w u converges identity m

private theorem literal (C : Family G) :
    (fun i : Rose.Badge × Fin 3 => WilsonPositionThermometerReading.leg C i.1 i.2) =
      WilsonPositionThermometerStationFaces.masked (WilsonPositionThermometerReading.leg C Finset.univ) :=
  funext fun i => WilsonPositionThermometerStationFaces.original_leg (C:=C) i.1 i.2

private theorem unit_on (lead : Leading F J) :
    ∀ᶠ r in trail, WilsonPositionPrescribedFrame.positioned F J V r 6 ((Bel R.family.book).unit 6) = S.unit 6 :=
  (lead.unit 6).mono fun r h =>
    (congrArg (fun x => J r 6 x) (WilsonPositionThermometerCorrectedUnit.corrected_unit F J V 6 r)).trans h

theorem positioned {Y : (Bel R.family.book).Hierarchy} {l : Ultrafilter (ℕ × ℕ)}
    (A : ℝ → Filing R.family 6 I) (paid : ∀ m : ℕ,
      ∀ᶠ r in trail, Filed (f:=f) (Y:=l) Y b r (J r) m (A r))
    (lead : Leading F J) (prior : (l : Filter _) ≤ f.fuse) (m : ℕ) :
    ∀ᶠ r in trail, Filed (f:=f) (Y:=l) Y (fun i : Rose.Badge × Fin 3 =>
      WilsonPositionThermometerReading.leg R.family i.1 i.2) r (WilsonPositionPrescribedFrame.positioned F J V r) m
        (lamps F J V b A r) := by
  let P := WilsonPositionPrescribedFrame.positioned F J V
  let u := WilsonPositionThermometerReading.leg R.family (Finset.univ : Rose.Badge)
  filter_upwards [occupied F J V b A paid lead m, unit_on F J V lead] with r hr hu
  have h := WilsonPositionThermometerStationFaces.filed (f:=f) (Y:=l) (H:=Y) (P:=P r) (m:=m) (u:=u) (r:=r)
    (points F J V b A r) R.makes prior hr hu
  exact (congrArg (fun v => Filed (f:=f) (Y:=l) Y v r (P r) m (lamps F J V b A r)) (literal R.family)).mpr h

/-- The finite basis and original station are issued before any requested
position prescription, radius or perturbative order. -/
theorem selected (simple : G.Simple) {Y : (Bel R.family.book).Hierarchy} {l : Ultrafilter (ℕ × ℕ)}
    {arch : Terrace.Arch R.family} (bliss : Bliss F l arch Y) :
    ∃ (P : ℝ → tower S) (A : ℝ → Filing R.family 6 I),
      PlotX F Y l simple (fun r => P r 4) ∧ (∀ m : ℕ, ∀ᶠ r in trail, chores r (P r 4) m) ∧
      Leading F P ∧ (∀ d, ∀ᶠ r in trail, Frame.obedient F Y (P r) d) ∧
      (∀ m : ℕ, ∀ᶠ r in trail, Filed (f:=f) (Y:=l) Y b r (P r) m (A r)) ∧
      ∀ (V : Store G) (m : ℕ), ∀ᶠ r in trail, Filed (f:=f) (Y:=l) Y
        (fun i : Rose.Badge × Fin 3 => WilsonPositionThermometerReading.leg R.family i.1 i.2)
        r (WilsonPositionPrescribedFrame.positioned F P V r) m (lamps F P V b A r) := by
  obtain ⟨P,A,book⟩ := WilsonPositionThermometerOrientedStation.simultaneous simple F Y bliss b
  have staff (m : ℕ) := (book m).mono fun _ h => h.1
  have basis (m : ℕ) := (book m).mono fun _ h => h.2
  have lead := fitted_lead simple F Y P staff
  exact ⟨P,A,(staff 4).mono fun _ h => h.angle, leading_chores F P lead, lead, angles_staff simple F Y P staff,
    basis, fun V => positioned F P V b A basis lead bliss.lies⟩

end YM.Integration.WilsonPositionOriginalOrientedFrame
