import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.StandaloneCorrelation
import YM.Integration.WilsonGraphCompactCoordinateJets

noncomputable section
namespace YM.Integration.WilsonGraphAppointedStationaryPrices

open Function Filter Set Asymptotics PowerSeries
open Lattice RG MeasureTheory Wilson Extraction Climb Trace.Pilot
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato FullVolume Spec Table
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1
open MS MS.Land MS.Fleet PhysMS PhysMS.Frame Next.UVStress OPE OPE.Orbits
open FVA2 FVA2.Register FVA2.Scale FVA2.Scale.Level
open SignedWilsonExpansion SignedWilsonExpansion.Belle SignedWilsonExpansion.Belle.Path SignedWilsonExpansion.Museum SignedWilsonExpansion.Kane
open SignedWilsonExpansion.Kane.Tilted SignedWilsonExpansion.Camera
open Integration.Election Integration.Election.Frames
open Order Spin SignedWilsonExpansion.StageG XSpace.Cirrus Entree Future
open Belfry Belle Dancer Belfry.ScaleFits Belfry.Classroom Scale Level GroupS
open Answer.ContinuumLimit Answer.ContinuumLimit.Vision
open Integration.GradedFar Integration.GradedFar.Tariff
open Integration.GradedFar.Tariff.Sunshine
open WilsonPositionHomogeneousComparison
open scoped Topology BigOperators Classical ContDiff

universe u
variable {G : Gauge} {H : G.Simple} {ε : ℝ} {e : Axis} {O : OrderS G}
variable {E : Construction.{u} H ε e O} {ξ : Extraction.Order}
variable (Z : WilsonPrescription G) (V : Vision E ξ) (Q : Perspective H Z true)
local notation "t" => V.T Z
local notation "X" => FVA2.Scale.Measure.outlook Z.scheme Z.criterion

/-- The homogeneous #140 moment uses the very same measured frame and viewer as the
post-conversion Wilson correlation in the elected #383 vision. -/
theorem frame {n : ℕ} (h : ℕ) (v : Fin n → Sec G h) (r : ℝ)
    (x : Points n) (peer : Peers V) :
    Life Z V true r (fun _ : Fin n => h) v x peer =
      frank V.pupil.last (V.Post Z) peer h r x v := by rfl

/-- The matched, finite, common-grade polynomial equals the stationary formal crop
at every separated tuple, with the same coefficient in each power. -/
theorem polynomialAt {n : ℕ} (h : ℕ) (v : Fin n → Sec G h) (ν : ℝ)
    (x : Scale.Stage n) (p : ℕ) (s : ℝ) :
    polynomial Z Q.MS ν h x v p s = FVA2.GradedFar.crop p s (sent X h x.val v) := by
  rw [polynomial, FVA2.GradedFar.crop_eq]
  apply Finset.sum_congr rfl
  intro j hj
  rw [filed Z Q.MS Q.matching, cashed X v x.property]

include Q

theorem adjacent (h : ℕ) :
    Integration.GradedFar.Neighbor.Included V.pupil.last (V.Post Z) h (h+1) (Nat.le_succ h) := by
  have inc := WilsonPositionHomogeneousFrame.adjacent V.pupil.last V.pupil.J Z
    V.pupil.VFrame.2 V.pupil.VFrame.1 H
    (WilsonPositionHomogeneousCoefficients.purchased Z Q.matching) h
  filter_upwards [inc] with r hr v
  change V.Post Z r (h+1) ((Maxwell.Free.fields E.paths.family.labels (h+1)).symm
    (Normalize.up (Nat.le_succ h) v)) =
    V.pupil.last.sector.derivatives.rise (Nat.le_succ h)
      (V.Post Z r h ((Maxwell.Free.fields E.paths.family.labels h).symm v))
  rw [WilsonPositionPrescribedNested.included]
  exact hr _

theorem timeNonzero : ∀ᶠ r in trail, t r ≠ 0 := by
  exact (V.certificate Q).calendar.clock.positive.mono fun _ hr => ne_of_gt hr

/-- Each original compact price is uniform in all the genuine viewers and separated
positions on this compact set. All marks in the estimate are the original fixed fields. -/
theorem value {ι : Type} (l : Filter ι) (r : ι → ℝ) (scale : Tendsto r l trail)
    {n : ℕ} (K : Set (Points n)) (hK : IsCompact K) (separated : K ⊆ conf n)
    (ν : ℝ) (h p : ℕ) (v : Fin n → Sec G h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in l, ∀ (peer : Peers V) (x : Points n), x ∈ K →
      ‖frank V.pupil.last (V.Post Z) peer h (r i) x v -
        FVA2.GradedFar.crop p (t (r i)) (sent X h x v)‖ ≤ C * |t (r i)|^(p+1) := by
  let inside : ∀ j : Fin n, (fun _ : Fin n => h) j ≤ h := fun _ => le_rfl
  have salary : ∀ j : Fin n, SeatsW.Salary ℂ l 1 (fun _ : ι => v j) :=
    fun j => SeatsW.income (SeatsW.constant (l := l) (v j))
  obtain ⟨C, hC, current⟩ := ((pricedLines V Q).trueLetters p l r scale K
    ⟨hK, separated⟩ ν (fun _ : Fin n => h) inside (fun _ => v) salary).2
  refine ⟨C, hC.le, ?_⟩
  filter_upwards [current] with i hi
  intro peer x hx
  let placed : Scale.Stage n := ⟨x, separated hx⟩
  have paid := hi peer placed hx
  have lifted : toView (fun _ : Fin n => h) h inside G v = v := by
    funext j
    change Normalize.up (inside j) (v j) = v j
    exact Subtype.ext rfl
  rw [lifted, polynomialAt Z Q h v ν placed p (t (r i))] at paid
  exact paid

/-- Both arities needed by the derivative recursion receive their entire true stationary
series from this single appointed physical correlation, on each compact set. -/
theorem stationary (n h : ℕ) :
    ClassExpansion V.pupil.last (V.Post Z) X t n h := by
  apply WilsonGraphCompactCoordinateJets.stationaryFromValues V.pupil.last (V.Post Z) Z h
    (timeNonzero Z V Q)
  intro K hK separated v p
  obtain ⟨C, hC, paid⟩ := value Z V Q trail id tendsto_id K hK separated
    (FVA2.Teller.logNu 1) h p v
  exact ⟨C, hC, paid.mono fun _ hr x => hr none x.val x.property⟩

/-- Every finite Cartesian derivative word of the actual physical crop is charged
at the same compact family, through the same positive-radius filter and appointed frame. -/
theorem original {ι I : Type} (l : Filter ι) (r : ι → ℝ) (scale : Tendsto r l trail)
    {n : ℕ} (K : Set (Points n)) (hK : IsCompact K) (separated : K ⊆ conf n)
    (active : ι → I → Prop) (point : ι → I → Points n)
    (placed : ∀ s i, active s i → point s i ∈ K) (peer : ι → I → Peers V)
    (p h : ℕ) (word : TraceOrder n) (v : Fin n → Sec G h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in l, ∀ i, active s i →
      ‖δ word (fun y => frank V.pupil.last (V.Post Z) (peer s i) h (r s) y v) (point s i) -
        δ word (fun y => FVA2.GradedFar.crop p (t (r s)) (sent X h y v)) (point s i)‖ ≤
        C * |t (r s)|^(p+1) := by
  apply WilsonGraphCompactCoordinateJets.compact V.pupil.last (V.Post Z) Z Q.MS Q.matching
    l r scale point peer (marks_the_data Z V Q).clock (adjacent Z V Q) hK separated placed
    (stationary Z V Q 2) (stationary Z V Q n) _ h word v
  intro cap u
  obtain ⟨C, hC, paid⟩ := value Z V Q l r scale K hK separated
    (FVA2.Teller.logNu 1) cap p u
  exact ⟨C, hC, paid.mono fun s hs i hi => hs (peer s i) (point s i) (placed s i hi)⟩

end YM.Integration.WilsonGraphAppointedStationaryPrices

