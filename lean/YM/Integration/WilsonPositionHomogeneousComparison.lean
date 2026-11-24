import YM.Integration.WilsonPositionHomogeneousLeading

/-! The original manuscript's numerical qexactcorr target on the actual
homogeneous measuring frame. Its coefficients are the full substituted MS
hierarchy, with both the coupling inverse and all field columns applied.
We establish its free order uniformly for every finite family here. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionHomogeneousComparison
open Function Filter Set Finset MeasureTheory Extraction Table Spec Lattice Wilson RG Source
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet FVA2 FVA2.Register FVA2.Scale
open scoped Topology ContDiff BigOperators Classical
variable {G : Gauge} (Z : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))

def coefficient (ν : ℝ) (d : ℕ) {n : ℕ} (x : Scale.Stage n) (v: Fin n→Sec G d) (i:ℕ) : ℂ :=
  Facets.actMark (Measure.Z Z.scheme Z.criterion ν M d)
    (Facets.couple (Measure.f Z.criterion ν M) (Equator.wave ν M d)) n x i v
def polynomial (ν : ℝ) (d : ℕ) {n : ℕ} (x : Scale.Stage n) (v : Fin n→Sec G d) (q:ℕ) (g:ℝ) : ℂ :=
  ∑i∈range (q+1),(g:ℂ)^i * coefficient Z M ν d x v i

theorem filed {hG : G.Simple} {σ : Prescription (Press.portDeck G)} {b : Bool}
    (H : Main.Match Z hG M σ b) (ν:ℝ) (d:ℕ) {n:ℕ} (x:Scale.Stage n) (v:Fin n→Sec G d) (i:ℕ) :
    coefficient Z M ν d x v i=Measure.outlook Z.scheme Z.criterion d n x i v := by
  unfold coefficient
  rw [H.eqconv ν d]

theorem ground {hG : G.Simple} {σ : Prescription (Press.portDeck G)} {b : Bool}
    (H : Main.Match Z hG M σ b) (ν:ℝ) (d:ℕ) {n:ℕ} (x:Scale.Stage n) (v:Fin n→Sec G d) :
    coefficient Z M ν d x v 0=XSpace.Normalize.scene x.val d v := by
  rw [filed Z M H]
  let B:=H.details.toServed.toPosted.toQuoted.toContract.toMission.born
  have c:=Measure.scaled_sigma Z.scheme Z.criterion ν M σ (d:=d) hG B.Taylor B.still B.base n x
  exact congrArg (fun T=>T v) c

variable {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S) (J : ℝ→PhysMS.tower S)

def observed (d : ℕ) {n:ℕ} (v:Fin n→Sec G d) (r:ℝ) (x:Points n) : ℂ :=
  S.classMoment S (fun _ : Fin n=>d) (r • x)
    (fun i=>WilsonPositionHomogeneousFrame.homogeneous F J Z r d ((Maxwell.Free.fields R.family.labels d).symm (v i)))

/-- A fixed original extracted solution, one numerical field and physical
coupling before q, every separated configuration in the requested compact.
All positive orders of this statement are the physical comparison target. -/
def matchesThrough (ν:ℝ) (d : ℕ) {n:ℕ} (v:Fin n→Sec G d) (K:Set (Points n)) (q:ℕ) : Prop :=
  ∀ ε : ℝ,0<ε → ∀ᶠ r in Trace.Pilot.trail,∀ (x:Scale.Stage n),x.val∈K →
    ‖observed Z F J d v r x.val-polynomial Z M ν d x v q (WilsonPositionHomogeneousFrame.reading F J Z r)‖≤
      ε*|WilsonPositionHomogeneousFrame.reading F J Z r|^q

theorem zero {hG:G.Simple} {σ:Prescription (Press.portDeck G)} {b:Bool} (H:Main.Match Z hG M σ b)
    (lead:PhysMS.Leading F J) {Y : (Bel R.family.book).Hierarchy}
    (paid : ∀d : ℕ,∀ᶠ r in Trace.Pilot.trail,PhysMS.Frame.obedient F Y (J r) d)
    (ν:ℝ) (d:ℕ) {n:ℕ} (v:Fin n→Sec G d) {K:Set (Points n)} (hk:IsCompact K) (hs:K⊆conf n) :
    matchesThrough Z M F J ν d v K 0 := by
  intro ε he
  let V:=fun i=>(Maxwell.Free.fields R.family.labels d).symm (v i)
  let T:=fun r i=>WilsonPositionPrescribedLift.field F J Z.store d r (WilsonPositionHomogeneousFrame.change F J Z d r (V i))
  have earn:= (WilsonReportingMeasuredAdmission.present F J lead paid).runs F J (t:=fun _ : Fin n=>d) T V
    (fun i=>WilsonPositionHomogeneousLeading.field F J Z lead paid hG d (V i)) K hk hs ε he
  filter_upwards [earn] with r price x hx
  have z : PhysMS.WickGoal (C:=R.family) (d:=fun _ : Fin n=>d) V x.val=XSpace.Normalize.scene x.val d v :=
    WilsonPositionPrescribedScreen.zero d n v x.val
  have raw:=price x.val hx
  change ‖observed Z F J d v r x.val-PhysMS.WickGoal (C:=R.family) (d:=fun _ : Fin n=>d) V x.val‖≤ε at raw
  rw [z] at raw
  simpa only [polynomial,zero_add,range_one,sum_singleton,pow_zero,one_mul,ground Z M H,mul_one] using raw

end YM.Integration.WilsonPositionHomogeneousComparison

