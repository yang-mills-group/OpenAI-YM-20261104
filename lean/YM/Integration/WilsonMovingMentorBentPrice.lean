import YM.Integration.WilsonMovingMentorBentHistory
import YM.Integration.WilsonMovingMentorBentWallet

/-! Dated control of the bent regular Wilson action through the complete retained physical cutoff history. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingMentorBentPrice
open LocalTaylorR2
open Exponent
open King (overD capping SupplyF)
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Captain
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Ovens Time UVNext UVNext.CouplingReset Daisy.Charity.RG12 Tail
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open CalendarStep
open Reel Recoil Capstone Strand Rain Roost Mallow PhysicalNext.Repeat.Legato UVExtension Spire Orchard Mast Oasis LocalTaylorR2.Marker
open MergeProof Marker Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF
open WilsonMovingMentorBentHistory WilsonMovingMentorBentWallet
variable {G : Gauge} (R : Run G) (paid : Paid R.kit) (simple : G.Simple)
variable (p : ℕ) (hp : 3 ≤ p) (ε : ℝ) (hε : ε ≤ 1)
local notation "A" => R.alloy.B.a
local notation "rate" => fun i => Reel.upfront (R.alloy.B.a.clock.hatBeta i) p ε

include paid hp hε in
theorem cutoff (N per : ℕ) (grade : p ≤ R.alloy.B.a.clock.J (N+1)) :
    Reel.Affords (R.family.path.rep N per N) A N (scroll R p N per N) (rate N) := by
  rw [terminal]
  have paidDate := (Reel.trust R.kit paid.2.1 p grade hp).2.2 ε hε
  have positive := Reel.ipos A N p ε
  refine ⟨positive, by linarith only [paidDate.1, positive], fun i => ?_⟩
  unfold Reel.curve
  rw [sub_self, smul_zero, smul_zero, add_zero, Reel.bend]
  exact ((R.T.sticks N per).prices N (Nat.zero_le _) le_rfl).1.valid

include paid simple hp hε in
theorem follows {N per m : ℕ} (hm : m < N) (grade : p ≤ R.alloy.B.a.clock.J (m+1))
    (margin : 3*CalendarStep.loss (R.alloy.B.a.clock.J (m+1)) ≤ ε)
    (enter : Reel.Affords (R.family.path.rep N per (m+1)) A (m+1)
      (scroll R p N per (m+1)) (rate (m+1))) :
    let D := appointment R N per m hm
    Strange.Inland (Strange.jetEngine G) R.kit D.spring D.point.val
        (scroll R p N per (m+1)) p (rate m) ∧
      Reel.Affords (R.family.path.rep N per m) A m (scroll R p N per m) (rate m) := by
  let D := appointment R N per m hm
  rw [D.upper] at enter
  have raw := Strange.leaseArg (Strange.jetEngine G) R.kit D.spring D.point.val D.point.property
    (scroll R p N per (m+1)) p paid.1 paid.2.1 paid.2.2.1 hm grade hp enter simple paid.2.2.2 ε margin
  have eco := (Reel.trust R.kit paid.2.1 p grade hp).2.2 ε hε
  have pos := Reel.ipos A m p ε
  have fine := Reel.ipos A (m+1) p ε
  have refund : R.alloy.B.a.clock.hatBeta (m+1)^requested (p+1) ε + rate (m+1)/8 ≤ rate m := by
    unfold Reel.upfront at *
    linarith only [fine,eco.2]
  have out : Strange.Inland (Strange.jetEngine G) R.kit D.spring D.point.val
      (scroll R p N per (m+1)) p (rate m) :=
    ⟨⟨book_up raw.estate.1 refund, book_up raw.estate.2 (add_le_add_right refund _)⟩,
      fun c => book_up (raw.stakes c) (add_le_add_right (mul_le_mul_of_nonneg_left refund (abs_nonneg _)) _),
      raw.price, raw.rooms, raw.scalar.trans refund, raw.beta.trans refund⟩
  refine ⟨out,?_⟩
  rw [step R p N per m hm, D.lower]
  apply Reel.orient pos (le_refl _) ?_ out.stakes
  linarith only [eco.1,pos]

include paid simple hp hε in
theorem chain {start : ℕ} (admitted : ∀ i ≥ start, p ≤ R.alloy.B.a.clock.J (i+1) ∧
    3*CalendarStep.loss (R.alloy.B.a.clock.J (i+1)) ≤ ε) {m N per : ℕ} (late : start ≤ m) (bound : m ≤ N) :
    Reel.Affords (R.family.path.rep N per m) A m (scroll R p N per m) (rate m) := by
  by_cases hm : m < N
  · exact (follows R paid simple p hp ε hε hm (admitted m late).1 (admitted m late).2
        (chain admitted (m:=m+1) (per:=per) (Nat.le_succ_of_le late) hm)).2
  · obtain rfl : m = N := by omega
    exact cutoff R paid p hp ε hε m per (admitted m late).1
termination_by N-m

include paid simple hp hε in
theorem original (positive : 0 < ε) :
    ∀ᶠ start : ℕ in atTop, ∀ m ≥ start, ∀ N per (hm : m < N),
      let D := appointment R N per m hm
      Strange.Inland (Strange.jetEngine G) R.kit D.spring D.point.val
          (scroll R p N per (m+1)) p (rate m) ∧
        Reel.Affords (R.family.path.rep N per m) A m (scroll R p N per m) (rate m) := by
  obtain ⟨k,high⟩ := exists_nat_ge (3/ε)
  have date : ∀ᶠ i : ℕ in atTop, p ≤ R.alloy.B.a.clock.J i ∧ 3*CalendarStep.loss (R.alloy.B.a.clock.J i) ≤ ε := by
    filter_upwards [R.alloy.B.a.fits.deep.eventually_ge_atTop p, R.alloy.B.a.fits.deep.eventually_ge_atTop k] with i g t
    refine ⟨g,?_⟩
    have tk : (k:ℝ) ≤ (R.alloy.B.a.clock.J i:ℝ) := by exact_mod_cast t
    have bound : 3 ≤ (k:ℝ)*ε := (div_le_iff₀ positive).1 high
    unfold CalendarStep.loss
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    nlinarith only [bound, mul_le_mul_of_nonneg_right tk positive.le, positive]
  obtain ⟨t,ht⟩:=eventually_atTop.mp date
  refine eventually_atTop.mpr ⟨t,fun start before m late N per hm => ?_⟩
  have gates : ∀ i ≥ start, p ≤ R.alloy.B.a.clock.J (i+1) ∧ 3*CalendarStep.loss (R.alloy.B.a.clock.J (i+1)) ≤ ε :=
    fun i hi => ht (i+1) (by omega)
  apply follows R paid simple p hp ε hε hm (gates m late).1 (gates m late).2
  exact chain R paid simple p hp ε hε gates (Nat.le_succ_of_le late) hm

end YM.Integration.WilsonMovingMentorBentPrice
end
