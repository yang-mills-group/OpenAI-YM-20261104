import YM.Integration.WilsonPositionPrescribedFrame
import YangMills.WilsonProof.NativeSupport.Commissioned259.Application.Growth
import YangMills.WilsonProof.NativeSupport.Commissioned259.Core
import YM.Integration.WilsonPositionHomogeneousFrame
/-!
# The second inequality of (M.2), at this reading t(r)

For provenance check precisely the **real calibration** inputs being consumed; these are results
from *previous* hypotheses in bbcb's proof, not consequences of formation of the formal book,
and are not assertions of well-foundedness or of matched physical inputs in this project. `Pose.C5`
details the exact buy (one compact task at d at least 6, one exponent at least 2, including
posed screen & thermometer supports, see `requests`). From that earlier PoseFit result as a hypothesis (NOT showing existence), without taking
an estimate directly on the true t(r) or its homogeneous-frame relative conversion,
recover the analytic cost. This proof actually takes less than §M requires upstream via G.1/G.9. See
`Core` for options, and README for status of physical inputs, costs, and limitations. `Pose`
is for proving F.3/F.4 upgrades for needed continuum contributions.

The viewer/phase will enter (M.2)(first inequality); forecasts same for every Viewer! See
`Assay.profile` for costs in compact centre, x, y measure (total variation always retained).
No carrying out change-of-variables taking y to Ty. No need impose upper cutoff on T for this
inequality. Take unit balls L=1 (sup of absolute coordinates in this orientation) or more general
cap L. Theorems also apply at all allowed proper subarrays; see README and unit coherence
readers. Inputs need not have the exact top weight.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalGradedFar
open Function Filter Set MeasureTheory Lattice Wilson RG Source Extraction Table Spec PhysicalNext.Repeat.Legato RG17 FullVolume OPE OPE.Orbits Climb Next.UVStress Trace.Pilot PhysMS
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open FVA2 FVA2.Register FVA2.GradedFar259 FVA2.Scale FVA2.O.Score FVA2.O.Enh FVA2.O.Canon Dframe
open MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land GradedFar259.Application Pose
open YM.Integration.WilsonPositionPrescribedFrame
open YM.Integration.WilsonPositionHomogeneousFrame
open scoped Topology BigOperators Classical
-- Original frame & horizon. Main.Match authentically; no relative choices. Even ν arbitrary.
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book}
    (F : Final R.family f S) (J : ℝ→PhysMS.tower S) (N : WilsonPrescription G)
    (base : Leading F J) {sim : G.Simple} (ν : ℝ)
    (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "W" => WilsonPositionPrescribedFrame.positioned F J N.store
local notation "B" => GroupS.gaugeN N.scheme N.criterion M ν
local notation "V" => Scale.Measure.outlook N.scheme N.criterion
local notation "t" => WilsonPositionHomogeneousFrame.reading F J N

lemma actual_thermometer : t = GradedFar259.Pose.Paper.meter F W N.criterion := rfl
include base
lemma realized : Charges J W (WilsonPositionPrescribedScreen.correction F J N.store) := by
  refine ⟨ fun d=>?_, fun d=>(WilsonPositionPrescribedScreen.original F J base N.store d).1,
    fun d=>WilsonPositionPrescribedNested.fields F J base N.store d⟩
  filter_upwards [(WilsonPositionPrescribedScreen.original F J base N.store d).2] with r h v
  exact congrArg (J r d) (WilsonPositionPrescribedFrame.leg F J N.store h.2.1 v)
lemma true_w : Leading F W := Application.growing F J W (realized F J N base) base
lemma true_normal : Pose.normal F W N.store := by
  intro d; exact WilsonPositionPrescribedFrame.original F J N.store base d

/-- One finite §PoseFit task that suffices, exposure point. Strong previous physical hypothesis,
see `GradedFar259.Pose.C5` also stores the near-identity adjustment and `t'_ℓ(r)~g`. -/
abbrev Receipt : Prop := ∃ (k m : ℕ), (6 ≤ k) ∧ (2 ≤ m) ∧ ∃ (s : ℝ → ℝ) (A : ℝ → Normalize.Change G k) (q : ℕ), C5 F (WilsonPositionPrescribedFrame.positioned F J N.store) N A s (requests N k) m q
variable (P: Receipt F J N)
include H P
-- cost of powers of actual t in retained and excess terms. Never use a different δ for the Far
lemma calibration : GradedFar259.Calibrated G t := by
  rw [actual_thermometer]
  obtain ⟨d,m,hd,hm,s,A,q,E⟩:= P
  exact Pose.calibration F W (true_w F J N base) N A s E subset_rfl (true_normal F J N base) M H hd hm
lemma true_cost : ∀ᶠ r in late, 0 < t r ∧ |t r| ≤ 1 ∧ |t r| ≤ 2*g0 G r := coupling_payment sim (calibration F J N base M H P)
variable {n m h z : ℕ} {d : Fin n → ℕ} {e : Fin m → ℕ} (hd : ∀ i, d i ≤ z)
    (he : ∀ i, e i ≤ z) (hh : h ≤ z)
    {L : ℝ} {K : Set (Points n)} {E' : Set (Points m)}
    (hl : 0 ≤ L) (hK : IsCompact K) (hc : K ⊆ conf n) (hS : IsCompact E') (hy : E' ⊆ Outside m)
    {T0 : ℝ} (hT0 : 1 ≤ T0) (ha : clears T0 K E') (p : ℕ)
include hl hK hc hS hy hT0 ha

/-- The quantitative Graded-Far formal remainder. -/
theorem M2 : ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
    ∀ᶠ r in late, ∀ T ≥ T0, ∀ x ∈ K, ∀ y ∈ E',
    ∀ u ∈ Balls L G d, ∀ v ∈ Balls L G e,
      ‖crop p (t r) (measurement V B hd he x (T • y) (-Real.log T) u v) -
         crop p (t r) (center V B he (T • y) hh (-Real.log T) (purchased V u x h p (t r)) v)‖ ≤ C*((T⁻¹)^(h+1)+(g0 G r)^(p+1))*(1+Real.log T)^a :=
  GradedFar259.M2 N ν M H hd he hh hl hK hc hS hy hT0 ha (calibration F J N base M H P) p

/-- Pair with a joint test. -/
theorem M2test {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : ℂ→L[ℝ] E→L[ℝ] ℂ) (hR: ‖R‖ ≤ 1) : ∃ C:ℝ,0<C ∧ ∃ a:ℕ,
    ∀ᶠ r in late, ∀ T≥T0, ∀ u∈Balls L G d, ∀ v∈ Balls L G e,
    ∀ A:Set E4, IsCompact A → ∀ μ: VectorMeasure (↥A × ↥K × ↥E') E, IsFiniteMeasure μ.variation →
      GradedFar259.Assay.compares μ R (fun i=> crop p (t r) (measurement V B hd he i.2.1.val (T • i.2.2.val) (-Real.log T) u v))
        (fun i=> crop p (t r) (center V B he (T • i.2.2.val) hh (-Real.log T) (purchased V u i.2.1.val h p (t r)) v))
        (C*((T⁻¹)^(h+1)+g0 G r^(p+1))*(1+Real.log T)^a) :=
  GradedFar259.Assay.profile hd he hh R hR N ν M H hT0 hK hc hS hy ha hl p (calibration F J N base M H P)
end YM.Integration.OriginalGradedFar
