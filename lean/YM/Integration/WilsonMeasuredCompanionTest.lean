import YM.Integration.WilsonMeasuredCompanionSoft
import YM.Integration.WilsonMeasuredCompanionTransport

/-! The signed full marked source with its actual ordinary companions is integrable
on the same Wilson prior. This allows addition before any earlier physical read. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredCompanionTest
open Function Finset MeasureTheory Lattice Wilson RG Labels Source Marker Multi QuadraticLocal QuadraticLocal.Earn
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open WilsonMeasuredCompanionFace WilsonMeasuredCompanionSoft WilsonMeasuredCoefficientTransport
open WilsonPhysicalMarkedDefect.RegularProjection
open WilsonThermometerUnitFilingCoarse WilsonMeasuredCompanionTransport
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)
variable {G:Gauge}{n:Side}{T ι:Type}[Countable ι]{o:Fin 3→Site n}{P:Rep G n}
variable (E:Lamps T ι G P.p o (J))(v:Fin 3)(s:(J).Mode)(x:T)
theorem measurable : Measurable (peers E v s x):=by
  have logs:Measurable (E.log x):=by
    apply Measurable.tsum (f:=fun i U=>E.frame i x U)
    intro i
    apply (Overlay.Bands.sends _).measurable.comp
    unfold Lamps.light
    split
    · exact (E.legal x i).borel
    · exact masked_measurable _ _ _ (E.legal x i).borel
  exact (Poly.get s).measurable.comp ((Poly.pass_cont.measurable.comp logs).mul measurable_const)

variable {d:ℕ}{F:Frame G d}{S:SectionData F}{A:Hol G}
theorem integrable (h:Coefficient F n)(fit:h.Format (o v) A P){κ B σ C' Λ δ z:ℝ}
    (inc:h.remBound (o v) P κ B)(law:P.Lawful σ C' Λ δ z)
    (w:Fin 3→ℝ)(pos:∀j,0<w j){a C:ℝ}(regular:E.Paid w P.p.B a C)(ap:0≤a)(cp:1≤C):
    Integrable (fun U=>h.density (o v) S P U*peers E v s x U) (prior G _):=by
  have root:=h.envelope S law inc fit
  obtain ⟨K,bound⟩:=root.cost
  have budget:Envelope (fun U=>h.density (o v) S P U*peers E v s x U):=by
    refine ⟨root.meas.mul (measurable E v s x),K*(expense C*w v/Poly.toll w s),fun U=>?_⟩
    rw [norm_mul]
    exact mul_le_mul (bound U) (gross E w pos regular ap cp v s x U) (norm_nonneg _)
      ((norm_nonneg _).trans (bound U))
  exact budget.integrableC _

variable (R:Run G){N per a j:ℕ}{P:Rep G (R.family.side a per)}
  {o:Fin 3→Site (R.family.side a per)}(E:Lamps T ι G P.p o (J))(v:Fin 3)
  {F:Frame G d}(h:Coefficient F (R.family.side a per)){A':Hol G}(fit:h.Format (o v) A' P)
  (S:SectionData F){κ B k σ C' Λ δ z:ℝ}(inc:h.remBound (o v) P κ B)
  (rent:Hard.Rent P.activities.forced P.activities.K P.p P.p.supportExponent k)
  (law:P.Lawful σ C' Λ δ z)(w:Fin 3→ℝ)(pos:∀j,0<w j)(cap:ℝ)(cp:1≤cap)
  (regular:E.Paid w P.p.B P.p.supportExponent cap)
local notation "old" => (Hard.rent rent : Hard T P.p P.activities.forced P.activities.K o (J))
local notation "newK" => WilsonOriginalDepositedHard.joined (old) v h fit (fun _=>1)
local notation "lower" => (⟨E,(old)⟩:Gallery T ι o P (J))
local notation "upper" => (⟨E,(newK)⟩:Gallery T ι o P (J))
local notation "read" => reading R (N:=N)
include inc law w pos cap cp regular in
theorem delta (s:(J).Mode)(x:T)(ja:j ≤ a):
    read (fun U=>h.density (o v) S P U*peers E v s x U) j ja-
      read (fun U=>(soft h).density (o v) S P U*peers E v s x U) j ja=
      read (fun U=>((upper).density x U).part s) j ja-
      read (fun U=>((lower).density x U).part s) j ja:=by
  have valid:∀x:T,‖(1:ℂ)‖≤1:=fun _=>norm_one.le
  have paid:=fund rent v h fit (fun _=>1) E w pos valid inc regular
  have integrable' (D:Gallery T ι o P (J)){M:ℝ}(bill:D.Pays w P.p.supportExponent cap M):
      Integrable (fun U=>(D.density x U).part s) (prior G _):=
    (Poly.get s).integrable_comp (QuadraticLocal.Tariff.integrable (J) o w pos D x bill P.p.exponent_pos.le law)
  have full:=integrable (S:=S) E v s x h fit inc law w pos regular P.p.exponent_pos.le cp
  have band:=integrable (S:=S) E v s x (soft h) (format h _ _ A' fit) (bill h _ _ inc)
    law w pos regular P.p.exponent_pos.le cp
  rw [←subtract R _ _ full band ja,←subtract R _ _ (integrable' (upper) paid.2) (integrable' (lower) paid.1) ja]
  congr 1
  funext U
  have q:=on_field rent v h fit (fun _=>1) E S w pos valid inc x s U
  simp only [one_mul] at q
  rw [q]
  ring

end YM.Integration.WilsonMeasuredCompanionTest
