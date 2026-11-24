import YM.QuadraticLocal.Campaign.Elixir
import YM.Integration.WilsonOriginalProjectedCurvatureReceivedSeal

/-! The measured registered input at a purchased Semester price. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvatureSemesterSeal
open Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn
open Next.Scheduling PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6 LocalComparison
open scoped Classical

variable {V α ι:Type} [DecidableEq V] [Countable ι] {G:Gauge} {n:Side}
  {D:Passport n V} {ρ:Census V} {P:Rep G n} (X:ι→Row D ρ G α)
  (incoming:Tint.Incoming D P α Empty ρ) {w:V→ℝ} (t:V→ℕ)
  (E:Earnings) {L:Side} {lower:BudgetPoint} {Ω W:ℝ} {j k v:ℕ}

theorem paid (fees:E.Cashier G L P.p lower Ω W (Coat.gStep P.beta))
    (roster:Scene.Armada X w t E.before Ω⁻¹ j k v)
    (jet:j ≤ E.cause) (width:k ≤ E.count) (crew:v ≤ E.rank)
    (R:Run G) (i q:ℕ)
    (retained:incoming.hard.Paid w P.p.B P.p.supportExponent
      ((R.alloy.B.a.clock.hatBeta i)^(-(q:ℝ))*forcedDivisor R.family i)) :
    ∃ certificate:Travel.Seal (Tint.Patrol.picture X incoming) w 2 1,
      Tint.Campus.Investor.Medal X incoming w certificate 0 ((Coat.gStep P.beta)^E.stage) := by
  have raised : Scene.Armada X w t E.before Ω⁻¹ E.cause E.count E.rank :=
    ⟨⟨fun s=>(roster.quota s).trans width,fun s=>(roster.crew s).trans crew⟩,
      roster.positive,roster.suggests,⟨roster.purchases.spend,fun a=>
        ⟨((roster.purchases.usable a).1).trans jet,(roster.purchases.usable a).2⟩⟩,roster.honor⟩
  have pos:0<Ω := lt_of_lt_of_le (by norm_num) fees.strong
  have total:E.inFee G P.p*Ω⁻¹ ≤ 1 := by
    rw [←div_eq_mul_inv,div_le_one pos]
    exact fees.wage
  have localFee:E.inFee G P.p*Ω⁻¹*Real.exp (-E.limitF)^P.p.B ≤ (Coat.gStep P.beta)^E.stage :=
    calc
      _ ≤ 1*Real.exp (-E.limitF)^P.p.B := mul_le_mul_of_nonneg_right total (pow_nonneg (Real.exp_nonneg _) _)
      _ ≤ (Coat.gStep P.beta)^E.stage := (one_mul _).le.trans fees.past_small
  exact WilsonOriginalProjectedCurvatureReceivedSeal.original X incoming t raised fees.breeze R i q retained total localFee

end YM.Integration.WilsonOriginalProjectedCurvatureSemesterSeal
