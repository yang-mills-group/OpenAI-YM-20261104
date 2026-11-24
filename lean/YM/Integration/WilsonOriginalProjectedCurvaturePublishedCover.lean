import YM.Integration.WilsonOriginalProjectedCurvatureCourseNotice

/-! The same dated publication retains every root and pays its long registered paths on the torus. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalProjectedCurvaturePublishedCover
open Function Finset Filter Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn
open Org Push.PriceCompiler AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP PhysicalNext.Repeat.Boulevard
open AnalyticBridge VerifiedReset
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (simple:G.Simple)
  {V α ι KU:Type} [DecidableEq V] [Fintype V] [Countable ι] [Countable KU]
  (root:PlanV.Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (table:root.Tab R.rolls) (ψ:ℕ→ℕ) (books:Mentor.Offices.Books root R.rolls table ψ)
  (pass:Pass root table R.alloy R.kit)
  (education:Mentor.Educated root R.rolls table R.kit.shape R.kit.scout ψ books R.alloy.delay)
  {first m N per order:ℕ} {π:ℕ→Layout G} {Γ:ℕ→Pace.Coin}
  {H:(s:ℕ)→Rep G (R.family.side s per)}
local notation "J" => R.alloy.B.a.clock.J
variable (op:Mentor.Opportunity (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m))
  (epoch:Mentor.Epoch root R.rolls (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m) op)
  (card:WilsonMovingMentorItinerary.CardAt R root epoch.vac m)
  (journey:PlanV.Journey root R.alloy (N:=N) (m:=m) card) (upper:π (m+1)=card.extra)
  (course:Concourse R.alloy R.kit R.T π Γ first N per epoch.vac H)
  (start:first ≤ m) (before:m < N)
  {D:Passport (R.family.side (m+1) per) V} {ρ:Census V}
  (M:ι→Row D ρ G α) (w:V→ℝ) (positive:∀j,0<w j)
  (voter:Mentor.Cruise.Voter M (Poetry.Agenda.seed root ψ (Burn.horizon epoch.vac) (R.alloy.B.a.clock.J (m+1)))
    order op.count op.stage epoch.vac (R.alloy.B.a.clock.J m))
  (input:Tint.Incoming D (H (m+1)) α KU ρ) {b b':ℝ}
  (sealed:Travel.Seal (Tint.Patrol.picture M input) w b b') (y:α)


local notation "u" => (R.alloy.B.a.S.oneStep m per).exact_size
local notation "published" => (Mentor.Cruise.publish root R.rolls table R.alloy ψ books op epoch u M order voter card)
local notation "waist" => (Poetry.Agenda.waist root (Burn.horizon epoch.vac) (R.alloy.B.a.clock.J (m+1)))

private theorem long_paths {S:Type} [Fintype S] [DecidableEq S] {T:Poetry.Roll G S} {a c:ℝ}
    (positive:0 ≤ a) (funded:SumBudget (T.price a) c) (n:ℕ) :
    SumBudget (fun i=>if n ≤ (T.leg i).length then (T.leg i).money (a/2) else 0)
      (Real.exp (-(a/2)*(n:ℝ))*c) := by
  refine Push.Local.sumBudget_mono (Push.Local.sumBudget_mul_left funded (Real.exp_nonneg (-(a/2)*(n:ℝ)))) ?_ ?_ le_rfl
  · intro i
    split_ifs <;> first | exact (T.leg i).fee_nn _ | norm_num
  · intro i
    change (if n ≤ (T.leg i).length then (T.leg i).money (a/2) else 0) ≤
      Real.exp (-(a/2)*(n:ℝ)) * T.price a i
    by_cases hi:n ≤ (T.leg i).length
    · rw [if_pos hi,Poetry.Roll.price,Poetry.Lantern.money,Poetry.Lantern.money,
        mul_left_comm (Real.exp _),←Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (by simpa [Poetry.Lantern.money] using (T.leg i).fee_nn 0)
      apply Real.exp_le_exp.mpr
      have scale:0 ≤ a/2 := by positivity
      have hl: (n:ℝ) ≤ ((T.leg i).length:ℝ) := by exact_mod_cast hi
      nlinarith [mul_nonneg scale (sub_nonneg.mpr hl)]
    · rw [if_neg hi]
      exact mul_nonneg (Real.exp_nonneg _) ((T.leg i).fee_nn _)

omit [Countable ι] in
include journey in
/-- The cover supplier is the same independent book as the earlier physical chart comparison. -/
theorem original (forecast:Mentor.Forecast root R.rolls table ψ books) :
    Earn.Press.Receipt M published waist (forecast.cost (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m)
      (R.alloy.B.a.clock.hatBeta m)) ∧
    ∀ (C:Club M) (k:Fin (order+1)), let T:=(published).news C k
      let n:ℕ:=(R.family.side m per).val
      SumBudget (fun i=>if n ≤ (T.leg i).length then (T.leg i).money (waist/2) else 0)
        (Real.exp (-(waist/2)*(n:ℝ))*
          (forecast.cost (R.alloy.B.a.clock.J (m+1)) (R.alloy.B.a.clock.J m) (R.alloy.B.a.clock.hatBeta m))) := by
  have paid:=Mentor.Cruise.funded root R.rolls table R.alloy ψ books op epoch u M order voter card journey forecast
  refine ⟨paid, fun C k=>?_⟩
  exact long_paths (Poetry.Agenda.belt_p _ _ _).le (paid.care C k).price _

end YM.Integration.WilsonOriginalProjectedCurvaturePublishedCover
