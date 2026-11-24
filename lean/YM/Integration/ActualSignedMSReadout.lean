import YM.Integration.ActualFoundryFiniteDetector
import YM.Integration.WilsonMSResidualLimit
import YM.Integration.WilsonWholeLimitRoom
import YM.Integration.MSOPEPhysicalTransfer

/-! The original grouped signed numerator feeds the complete detector
inverse at any actual intermediate level.  Its regulator limit is the
literal candidate residual on the same Final, Reader and frame.
The last theorem exposes the remaining estimate on that exact numerator;
it does not postulate an independent MS matching contract or assert that
the full manuscript local comparison has already been applied. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualSignedMSReadout
open Function Filter Set MeasureTheory Spec OPE OPE.Orbits PhysMS Asymptotics
open Pert.Position RG11.Fields RG11.Grove RG11.Neighborhood
open Lattice Wilson RG Marker
open MergeProof MergeProof.Accent Extra.Histories Extra.Trajectories
open EngineeringWeightedReadout PhysicalMSOPECandidate ActualFoundryDetectorSource
open scoped Topology Classical BigOperators

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
  {n i D : ℕ}

/-- The complete actual signed source, with its original normalized
coarse law and every detector row's own exterior, followed by the full
output-frame inverse.  The two padding labels are the actual degree-zero
unit and zero labels of the same Family. -/
def finiteReadout (J : ℝ → PhysMS.tower S) (U : Detector S D)
    (v : Fin n → E C.labels i) (r : ℝ) (x : Fin n → E4)
    (z : S.Field D) (N period m : ℕ) (hm : m ≤ N) : E C.labels D :=
  wholeReadout U J r (fun a =>
    ∫ W, (actualSignedTransport C (N := N)
      (detectorNumerator J U v r x z N period 0 0 a) hm W).part
        (Stock.final (Region (Fin (U.listen a).length))) ∂OPE.Therm.scene C.path N period m)

/-- The finite readout uses the original Wilson law exactly, at every
legal intermediate level; no product of conditional means occurs. -/
theorem finiteReadout_eq (hC : C.Makes) (J : ℝ → PhysMS.tower S)
    (U : Detector S D) (v : Fin n → E C.labels i) (r : ℝ)
    (x : Fin n → E4) (z : S.Field D) (N period m : ℕ) (hm : m ≤ N)
    (hUnit : C.ref 0 ≤ N) :
    finiteReadout J U v r x z N period m hm =
      wholeReadout U J r (fun a => Wilson.moment (C.beta N period)
        (WilsonWholeLimit.detectorDiscrepancy J U v r x z N period a)) := by
  unfold finiteReadout
  apply congrArg (wholeReadout U J r)
  funext a
  exact normalized_detector hC 0 0 hUnit J U v r x z a hm

/-- The comparison level may depend on the cutoff and the radius.
Its choice does not alter the limit of the actual grouped numerator. -/
theorem candidate_tendsto (F : Final C f S) (hS : Services C f S)
    (J : ℝ → PhysMS.tower S) (U : Detector S D)
    (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : Blocks C.labels n i D) (v : Fin n → E C.labels i)
    (N : ℕ) (t r : ℝ) (x : Fin n → E4)
    (hx : ∀ a, Injective (beside x (OPE.positions S (U.listen a)).ofLp))
    (level : (w : ℕ × ℕ) → Fin (w.1 + 1)) :
    Tendsto (fun w : ℕ × ℕ =>
      finiteReadout J U v r x (candidate J p Z B v N t r)
        w.1 w.2 (level w).val (Nat.le_of_lt_succ (level w).isLt))
      f.fuse (𝓝 (weightedMSResidual J U p Z B v N t r x)) := by
  have hUnit : ∀ᶠ w : ℕ × ℕ in f.fuse, C.ref 0 ≤ w.1 := by
    rw [Extraction.Order.fused, Extraction.Order.late]
    exact Eventually.of_forall fun _ => f.mesh.cofinal.eventually_ge_atTop _
  apply (WilsonMSResidualLimit.candidate_tendsto F hS J U p Z B v N t r x hx).congr'
  filter_upwards [hUnit] with w hw
  exact (finiteReadout_eq F.room.cutoff J U v r x
    (candidate J p Z B v N t r) w.1 w.2 (level w).val
    (Nat.le_of_lt_succ (level w).isLt) hw).symm

/-- A bound on the actual transported signed numerator passes directly
to the retained full-horizon residual. -/
theorem candidate_le (F : Final C f S) (hS : Services C f S)
    (J : ℝ → PhysMS.tower S) (U : Detector S D)
    (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : Blocks C.labels n i D) (v : Fin n → E C.labels i)
    (N : ℕ) (t r : ℝ) (x : Fin n → E4)
    (hx : ∀ a, Injective (beside x (OPE.positions S (U.listen a)).ofLp))
    (level : (w : ℕ × ℕ) → Fin (w.1 + 1)) (b : ℝ)
    (hb : ∀ᶠ w : ℕ × ℕ in f.fuse,
      ‖finiteReadout J U v r x (candidate J p Z B v N t r)
        w.1 w.2 (level w).val (Nat.le_of_lt_succ (level w).isLt)‖ ≤ b) :
    ‖weightedMSResidual J U p Z B v N t r x‖ ≤ b :=
  le_of_tendsto (candidate_tendsto F hS J U p Z B v N t r x hx level).norm hb

/-- The ordinary OPE error is already paid by the original physical
suppliers.  The sole remaining estimate displayed here is on the complete
actual grouped numerator, including its full inverse-frame weights.
No assertion is made that a generic scalar local estimate supplies it. -/
theorem remainder_of_finite_bound (F : Final C f S) (hS : Services C f S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J : ℝ → PhysMS.tower S) (hJ : Leading F J) (hQ : Foundation F Q)
    (U : Detector S D) (v : Fin n → E C.labels i)
    (M η : ℝ) (hM : 0 ≤ M) (hη : 0 < η)
    (g : ℝ → ℝ) (hg : Trace.Pilot.Coupling G g) (hG : G.Simple)
    {A : Type*} {l : Filter A} (r : A → ℝ)
    (hr : Tendsto r l Trace.Pilot.trail) (x : A → Fin n → E4)
    (hx : ∀ᶠ a in l, WithinRoom (r a) M η (x a) 0)
    (p : PowerSeries ℝ) (Z : ∀ d, RG11.Window.SquareAt C.labels d)
    (B : A → Blocks C.labels n i D) (N : ℕ)
    (level : (a : A) → (w : ℕ × ℕ) → Fin (w.1 + 1))
    (hb : ∀ ε : ℝ, 0 < ε → ∀ᶠ a in l, ∀ᶠ w : ℕ × ℕ in f.fuse,
      ‖finiteReadout J U v (r a) (x a)
        (candidate J p Z (B a) v N (g (r a)) (r a))
        w.1 w.2 (level a w).val (Nat.le_of_lt_succ (level a w).isLt)‖ ≤
          ε * ‖g (r a) ^ N‖) :
    (fun a => actualOutput F Q J v (r a) (x a) -
      composedTruncation p Z (B a) v N (g (r a))) =o[l]
        (fun a => g (r a) ^ N) := by
  apply (MSOPEPhysicalTransfer.remainder_isLittleO_iff F Q J hJ hQ U v
    M η hM hη g hg hG r hr x hx p Z B N).mpr
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [hb ε hε, hx,
    hr.eventually (WilsonWholeLimit.detector_separated_in_room
      (I := Fin n) U M η hη)] with a ha hxa hsep
  exact candidate_le F hS J U p Z (B a) v N (g (r a)) (r a) (x a)
    (hsep _ hxa) (level a) (ε * ‖g (r a) ^ N‖) ha

end YM.Integration.ActualSignedMSReadout
