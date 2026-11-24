import YM.Integration.WilsonPositionPhaseProfileTest

/-! The signed compact-profile form of the original all-orders correlation comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileMatching
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec OPE OPE.Orbits
open PhysicalNext.Repeat.Legato RG17 FullVolume Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet FVA2 FVA2.Register FVA2.Scale
open scoped Topology ContDiff Classical BigOperators
variable {G : Gauge} (Z : WilsonPrescription G) (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
  {n : ℕ}

def extended (A : Scale.Stage n → ℂ) (x : Points n) : ℂ := if h : x ∈ conf n then A ⟨x,h⟩ else 0

def coefficient (ν : ℝ) (d : ℕ) (φ : Test n) (v : Fin n → Sec G d) (i : ℕ) : ℂ :=
  φ.applyTo (extended (fun x => WilsonPositionHomogeneousComparison.coefficient Z M ν d x v i))

def polynomial (ν : ℝ) (d : ℕ) (φ : Test n) (v : Fin n → Sec G d) (q : ℕ) (θ : ℝ) : ℂ :=
  ∑ i ∈ range (q+1), (θ : ℂ)^i * coefficient Z M ν d φ v i

theorem filed {hG : G.Simple} {σ : Prescription (Press.portDeck G)} {b : Bool}
    (H : Main.Match Z hG M σ b) (ν : ℝ) (d : ℕ) (φ : Test n) (v : Fin n → Sec G d) (i : ℕ) :
    coefficient Z M ν d φ v i =
      φ.applyTo (extended (fun x => Measure.outlook Z.scheme Z.criterion d n x i v)) := by
  apply φ.apply_eq
  intro x hx
  simp only [extended, dif_pos hx]
  exact WilsonPositionHomogeneousComparison.filed Z M H ν d _ v i

variable {R : Run G} {f : Extraction.Order} {S : Table R.family.book} (F : Final R.family f S) (J : ℝ → PhysMS.tower S)

def observed (p : Viewers F) (d : ℕ) (φ : Test n) (v : Fin n → Sec G d) (r : ℝ) : ℂ :=
  WilsonPositionPhaseProfileTest.reading F J Z p φ (d:=fun _ => d)
    (fun i => (Maxwell.Free.fields R.family.labels d).symm (v i)) r

def matchesThrough (ν : ℝ) (d : ℕ) (φ : Test n) (v : Fin n → Sec G d) (q : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ r in trail, ∀ p : Viewers F,
    ‖observed Z F J p d φ v r -
      polynomial Z M ν d φ v q (WilsonPositionHomogeneousFrame.reading F J Z r)‖ ≤
        ε * |WilsonPositionHomogeneousFrame.reading F J Z r|^q

variable (reader : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
  (lead : Leading F J) {Y : (Bel R.family.book).Hierarchy}
  (paid : ∀ d : ℕ, ∀ᶠ r in trail, PhysMS.Frame.obedient F Y (J r) d)
  (hG : G.Simple) (X : Scaling S) (foundation : Foundation F reader)

include reader lead paid hG X foundation in
theorem phases (d : ℕ) (φ : Test n) (v : Fin n → Sec G d) (g : ℝ → ℝ) (hg : Coupling G g)
    {ε : ℝ} (he : 0 < ε) (N : ℕ) :
    ∀ᶠ r in trail, ∀ p : Viewers F,
      ‖observed Z F J p d φ v r-observed Z F J none d φ v r‖ ≤ ε * g r ^ N := by
  filter_upwards [WilsonPositionPhaseProfileTest.phases F J Z reader lead paid hG X foundation φ
    (d:=fun _ => d) (fun i => (Maxwell.Free.fields R.family.labels d).symm (v i)) g hg he N]
    with r bank p using bank p none

theorem free {hG : G.Simple} {σ : Prescription (Press.portDeck G)} {b : Bool}
    (H : Main.Match Z hG M σ b) (lead : Leading F J) {Y : (Bel R.family.book).Hierarchy}
    (paid : ∀ d : ℕ, ∀ᶠ r in trail, PhysMS.Frame.obedient F Y (J r) d)
    (ν : ℝ) (d : ℕ) (φ : Test n) (v : Fin n → Sec G d) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ r in trail, ‖observed Z F J none d φ v r - coefficient Z M ν d φ v 0‖ ≤ ε := by
  let V (i : Fin n) := (Maxwell.Free.fields R.family.labels d).symm (v i)
  let free := WickGoal (C:=R.family) (d:=fun _ : Fin n => d) V
  have agrees (x : Points n) : free x = XSpace.Normalize.scene x d v :=
    WilsonPositionPrescribedScreen.zero d n v x
  have physical : coefficient Z M ν d φ v 0 = φ.applyTo free := by
    apply φ.apply_eq
    intro x hx
    simp only [extended, dif_pos hx]
    exact (WilsonPositionHomogeneousComparison.ground Z M H ν d _ v).trans (agrees x).symm
  have smooth_free : ContinuousOn free (conf n) := fun x hx =>
    (PhysMS.WickGoal_tied (C:=R.family) V hx).continuousAt.continuousWithinAt
  let A := WilsonPositionPhaseProfileTest.mass φ + 1
  have positive : 0 < A := add_pos_of_nonneg_of_pos (integral_nonneg fun _ => norm_nonneg _) one_pos
  have check := WilsonPositionHomogeneousComparison.zero Z M F J H lead paid ν d v φ.hasCompactSupport φ.tsupport_subset
  filter_upwards [check (ε/A) (div_pos he positive),RG17.positiveLength] with r bank rp
  have bound := WilsonPositionPhaseProfileTest.price φ
    (φ.smearing (WilsonPositionPhaseProfileTest.smooth F J Z none V rp)) (φ.smearing smooth_free)
    (a:=ε/A) (fun x hx => by
      change ‖WilsonPositionHomogeneousComparison.observed Z F J d v r x-free x‖ ≤ ε/A
      have sx : x ∈ conf n := φ.tsupport_subset hx
      have c := bank (⟨x,sx⟩ : Stage n) hx
      simpa only [WilsonPositionHomogeneousComparison.polynomial,zero_add,range_one,sum_singleton,
        pow_zero,one_mul,mul_one,WilsonPositionHomogeneousComparison.ground Z M H,← agrees] using c)
  rw [physical]
  calc
    _ ≤ WilsonPositionPhaseProfileTest.mass φ * (ε/A) := bound
    _ ≤ A * (ε/A) := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (div_pos he positive).le
    _ = _ := by field_simp [positive.ne']

include reader lead paid hG X foundation in
theorem zero {σ : Prescription (Press.portDeck G)} {b : Bool} (H : Main.Match Z hG M σ b)
    (g : ℝ → ℝ) (hg : Coupling G g) (ν : ℝ) (d : ℕ) (φ : Test n) (v : Fin n → Sec G d) :
    matchesThrough Z M F J ν d φ v 0 := by
  intro ε he
  filter_upwards [phases Z F J reader lead paid hG X foundation d φ v g hg (half_pos he) 0,
    free Z M F J H lead paid ν d φ v (half_pos he)] with r phase price p
  simp only [polynomial,zero_add,range_one,sum_singleton,pow_zero,one_mul,mul_one] at *
  exact (norm_sub_le_norm_sub_add_norm_sub _ (observed Z F J none d φ v r) _).trans
    ((add_le_add (phase p) price).trans_eq (add_halves ε))

end YM.Integration.WilsonPositionSeparatedProfileMatching

