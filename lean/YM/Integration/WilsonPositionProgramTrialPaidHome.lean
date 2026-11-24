import YM.Integration.WilsonPositionProgramTrialStationHome
import YM.Integration.WilsonIndependentMatchedRosterNativeDose

/-! The actual optical inverse, with its original phase and print, on the inherited vacuum. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialPaidHome
open Function Filter Finset Matrix Lattice Wilson RG RG.Supply Precision Source Labels Next.Foundations
open Extra.Histories Motion PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Power WilsonCoeffUV.Embroider
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Bank.PathCost
open WilsonPositionProgramTrialHomeDose (publicDose)
open WilsonPositionProgramTrialNativeHome (reporter)
open WilsonPositionProgramTrialStationHome (chargeAt mass Seated)
open WilsonIndependentMatchedFiledIncome (charge plate)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentMatchedRosterNativeDose (gross)
open WilsonOriginalPhysicalFruitDose (amounts)
open WilsonOriginalPhysicalFruitVerse (written)
open WilsonReflectedMixedSharpAxis (Cash)
open WilsonReflectedFundedHearing (Arm)
open WilsonReflectedPublicGuardedMotion (coords)
open WilsonMeasuredPublicEntranceGridDebit (fitted)
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k u e d:ℕ}(R:Run G)(W:Initialize G)
local notation "C" => Credit.leanC
local notation "L" => R.family.path.levels
local notation "F" => R.family.labels.level d
local notation "a" => R.family.S.a
local notation "β" => R.family.path.levels.clock.hatBeta

def source {K N per f:ℕ}(arm:Arm R d N per f K)(r:ℝ)(t:ℂ)(φ:ℂ→L[ℝ]ℝ):Verse F:=
  written F (amounts R d K N per r t (coords R arm)) φ

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (fit:h<D)(rails:Rails h k u e)(kind:Bool)(dim:d<D)(cap:d≤k):
    let Q:=reporter (G:=G) fit
    ∃α:Alma F→ℝ,(∀i,0≤α i) ∧ ∃Z B:Credit,
    ∀ᶠ floor:ℕ in atTop,∀m j f K N per target E,floor ≤ m → m ≤ K →
    ∀(before:j ≤ f)(up:f ≤ K)(live:K ≤ N){η:ℝ},0≤η → η≤1 →
    ∀(A:R.family.label d≃ₗ[ℂ]R.family.label d)(Y:R.family.label d){W₀:ℝ},
    Cash (R:=R) d j f K N per target before up live η A Y W₀ →
    ∀arm:Arm R d N per f K,arm.w=A.symm (fitted R d j N per Y) →
    ∀(r g:ℝ),0<r → 0<g → a f ≤ r → ∀(t:ℂ)(φ:ℂ→L[ℝ]ℝ)(M roof:ℝ),
    0≤M → 1≤roof → 0≤W₀ → max 1 (2*(a j/a f)^(d+1)*W₀) ≤ M*(β f)^E →
    β K*g^2≤roof →
    let c:=source R arm r t φ
    let salary:=gross F e α*‖φ‖*(WilsonOriginalPhysicalFruitClock.salary R d E t M roof*
      (g⁻¹)^WilsonOriginalPhysicalFruitClock.power R d E*(r/a K)^η)
    ∃X:CutsP (hol G) Q.ans Q.path rails C C C C,
      Seated R Q rails m K N (Shrine (plate (sectionAt R W kind d) dim) c) (charge e c α) X ∧
      charge e c α ≤ salary ∧
      ∀x:ℝ,(x • X.pt=centralL L R.metals.O N m K Q (PermuteLens L R.metals.O Q N m
        (publicDose Q X x))+x • X.springP X.i) ∧
      mass Q e (publicDose Q X x) ≤ |chargeAt L Q e B Z m K| * (|x| * salary):=by
  intro Q
  obtain ⟨α,paid,Z,B,homes⟩:=WilsonPositionProgramTrialStationHome.original R W simple v funded fit rails
    d kind dim cap
  refine ⟨α,paid,Z,B,?_⟩
  filter_upwards [homes] with floor enrolled
  intro m j f K N per target E fm mk before up live η ηp ηs A Y W₀ cash arm exactArm
    r g rp gp ar t φ M roof mp one nn card optical
  dsimp only
  let c:=source R arm r t φ
  obtain ⟨X,haveX,payout⟩:=enrolled m K N fm mk live c 1
  have earned:=WilsonIndependentMatchedRosterNativeDose.original R simple α paid e φ
    before up live ηp ηs A Y cash arm exactArm r g rp gp ar t M roof mp one nn card optical
  have nonneg:0≤charge e c α:=Finset.sum_nonneg fun i _=>WilsonIndependentMatchedFiledIncome.nonneg (paid i) _ _
  refine ⟨X,by simpa only [one_smul,abs_one,one_mul] using haveX,earned,?_⟩
  intro x
  obtain ⟨read,price⟩:=payout x
  refine ⟨read,?_⟩
  simp only [abs_one,one_mul] at price
  exact price.trans ((mul_le_mul_of_nonneg_right (le_abs_self _)
    (mul_nonneg (abs_nonneg _) nonneg)).trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left earned (abs_nonneg _)) (abs_nonneg _)))

end YM.Integration.WilsonPositionProgramTrialPaidHome
end
