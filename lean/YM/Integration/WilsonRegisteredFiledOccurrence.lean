import YM.Integration.WilsonPhysicalHistoryRetainedSpringIncoming
import YM.Integration.WilsonInvariantActionRegisteredHearing

/-! Insert a whole filed vacuum vertex with its action sign into the original
positive density. The same actual prior begets both lower connected terms. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonRegisteredFiledOccurrence
open Function Filter Lattice Laurent Bloch Wilson RG Precision Exterior Tree PowerSeries Marker MeasureTheory
open IterationFour IterationFour.Vacuum Comparison.RG02 Comparison.RG02.Assembly
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank Stationary
open WilsonCoeffUV.Bank.Mosaic FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open WilsonLimitConstruction OriginalMarkedRunAction WilsonInvariantActionPriorHearing
open WilsonInvariantActionRegisteredHearing
open scoped Topology BigOperators Classical
variable {G : Gauge} (R : Run G) {N p m : ℕ}
local notation "fine" => Config G (R.family.side (m+1) p)
local notation "coarse" => Config G (R.family.side m p)
local notation "Ω" => (coarse × fine)
local notation "P" => R.family.path.rep N p (m+1)

def prior (interior : m+1<N) : readings Ω := by
  have e : Envelope (P).eval := (P).envelope (R.makes.wilson.represents N p (m+1) interior.le).good
  exact ⟨fun q => (P).eval q.2, e.meas.comp measurable_snd, e.cost.choose,
    fun q => e.cost.choose_spec q.2⟩

def vertex (interior : m+1<N) (r : ℕ) (Z : SeriesA G) {σ b : ℝ} (hs : 0<σ)
    (paid : Draw Z σ b) (g : ℝ) (x : Site (R.family.side (m+1) p)) : readings Ω := by
  refine ⟨fun q => -springAt R N p (m+1) r Z g x q.2, ?_⟩
  obtain ⟨hm, hb⟩ := filed_site_price R N p (m+1) r interior.le Z hs paid g x
  exact ⟨(hm.comp measurable_snd).neg, springSiteBill R N (m+1) r Z g b,
    fun q => (norm_neg _).trans_le (hb q.2)⟩

theorem density (interior : m+1<N) (r : ℕ) (Z : SeriesA G) {σ b : ℝ}
    (hs : 0<σ) (paid : Draw Z σ b) (g : ℝ) (x : Site (R.family.side (m+1) p)) (q : Ω) :
    let W := vertex R interior r Z hs paid g x
    HasDerivAt (fun t : ℝ => Real.exp ((P).exponent q.2) *
      (P).activities.gas (P).p q.2 * (1 - t * springAt R N p (m+1) r Z g x q.2))
      ((prior R interior * W).val q) 0 ∧
    score R interior (prior R interior * W) = W ∧
    ‖W.val q‖ ≤ springSiteBill R N (m+1) r Z g b := by
  intro W
  refine ⟨?_, ?_, ?_⟩
  · change HasDerivAt (fun t : ℝ => (P).eval q.2 *
        (1 - t * springAt R N p (m+1) r Z g x q.2))
        ((P).eval q.2 * -springAt R N p (m+1) r Z g x q.2) 0
    simpa using (((hasDerivAt_const (0:ℝ) 1).sub
      ((hasDerivAt_id (0:ℝ)).mul_const (springAt R N p (m+1) r Z g x q.2))).const_mul ((P).eval q.2))
  · apply Subtype.ext
    funext q
    change (P).eval q.2 * W.val q / (P).eval q.2 = W.val q
    have hp : (P).eval q.2 ≠ 0 := (Multi.AxisShift.chosen_positive R.makes.wilson (p := p) interior.le q.2).ne'
    exact (div_eq_iff hp).2 (mul_comm _ _)
  · exact (norm_neg _).trans_le ((filed_site_price R N p (m+1) r interior.le Z hs paid g x).2 q.2)

theorem original (interior : m+1<N) (birth : R.family.ref 4 ≤ m+1)
    (v w : R.family.label 4) (o z x : Site (R.family.side (m+1) p)) (η χ : ℂ →L[ℝ] ℝ)
    (r : ℕ) (Z : SeriesA G) {σ b : ℝ} (hs : 0<σ) (paid : Draw Z σ b) (g : ℝ) :
    let live : m<N := Nat.lt_trans (Nat.lt_succ_self m) interior
    let A := filed R live birth v o η
    let B := filed R live birth w z χ
    let W := vertex R interior r Z hs paid g x
    HasDerivAt (fun t : ℝ => covariance (reweighted (joint R (p:=p) live) W t) A B)
      (receipts R live A B W) 0 := by
  intro live A B W
  have eqn := (density R interior r Z hs paid g x (1,1)).2.1
  have paidPair := registered R interior birth v w o z η χ (prior R interior * W)
  change HasDerivAt (fun t : ℝ => covariance (reweighted (joint R (p:=p) live)
    (score R interior (prior R interior * W)) t) A B) (receipts R live A B
    (score R interior (prior R interior * W))) 0 at paidPair
  rwa [show score R interior (prior R interior * W) = W from eqn] at paidPair

end YM.Integration.WilsonRegisteredFiledOccurrence
