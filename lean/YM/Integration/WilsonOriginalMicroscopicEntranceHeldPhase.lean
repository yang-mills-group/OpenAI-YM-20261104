import YM.Integration.WilsonOriginalMicroscopicEntranceHeldPhaseIncome
import YM.Integration.WilsonOriginalConditionalPhaseSum
import YM.Integration.WilsonOriginalAlternativeTrialPhaseCurrency

/-! All original signed ordinary faces are taken under one positive Wilson denominator.
The entire prescribed finite phase and physical source restorations have one absolute invoice. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldPhase
open Function Finset MeasureTheory Lattice Wilson RG Marker PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonMeasuredPublicEntrancePanel
open WilsonOriginalMicroscopicEntranceHeldMasterRead (ReadingAt)
open WilsonOriginalMicroscopicEntranceHeldPhaseIncome (entry)
open WilsonOriginalAlternativeTrialPhaseCurrency (amount)
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V](d:V→ℕ)
  {N per f K j requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}
  (A:Panel R d N per f K fk cut requested power t B)
local notation "J" => Stock.census V
local notation "C" => R.family
local notation "H" => (C).path.levels.clock.hatBeta f

/-- Arbitrary signed coefficients on the single actual measured conditional. -/
theorem signed (jf:j≤f)(W:Config G ((C).side j per))(hearing:ReadingAt R d A jf W)
    (roster:Finset (J).Mode)(c:(J).Mode→ℂ):
    let road:=jf.trans fk
    let field:=fun U=>∑s∈roster,c s*entry R d cut A s U
    let read:=actualTransport (C) (N:=N) field road W
    Integrable (fun U=>((C).path.rep N per K).eval U • field U) (prior G _) ∧
    read=∑s∈roster,c s*(actualTransport (C) (N:=N) (Raw R d A s) (road.trans cut) W-
      actualTransport (C) (N:=N) (Guard R d A s) road W) ∧
    ‖read‖≤((H)^requested)⁻¹*∑s∈roster,‖c s‖:=by
  intro road field read
  let part:=fun s=>actualTransport (C) (N:=N) (entry R d cut A s) road W
  obtain ⟨cash,linear⟩:=WilsonOriginalConditionalPhaseSum.original R roster c (entry R d cut A)
    (WilsonOriginalMicroscopicEntranceHeldPhaseIncome.original R d cut A) road W
  have heard (s):part s=actualTransport (C) (N:=N) (Raw R d A s) (road.trans cut) W-
      actualTransport (C) (N:=N) (Guard R d A s) road W ∧ ‖part s‖≤((H)^requested)⁻¹:=hearing s
  have row:read=∑s∈roster,c s*part s:=linear
  refine ⟨cash,?_,?_⟩
  · rw [row]
    exact Finset.sum_congr rfl fun s _=>congrArg (c s*·) (heard s).1
  · rw [row]
    calc
      _≤∑s∈roster,‖c s*part s‖:=norm_sum_le _ _
      _≤∑s∈roster,‖c s‖*((H)^requested)⁻¹:=by
        apply Finset.sum_le_sum
        intro s _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (heard s).2 (norm_nonneg _)
      _=((H)^requested)⁻¹*∑s∈roster,‖c s‖:=by rw [← Finset.sum_mul,mul_comm]

/-- The measured engineering radii and each actual input dose are restored once per occupied root. -/
theorem original (jf:j≤f)(W:Config G ((C).side j per))(hearing:ReadingAt R d A jf W)
    (roster:Finset (J).Mode)(c:(J).Mode→ℂ)(r:V→ℝ)(positive:∀a,0≤r a):
    let dose:=fun a=>(charged R d A a:ℂ)
    let money:=fun s:(J).Mode=>c s*∏a∈s.val,amount r d dose a
    let road:=jf.trans fk
    let field:=fun U=>∑s∈roster,money s*entry R d cut A s U
    let read:=actualTransport (C) (N:=N) field road W
    Integrable (fun U=>((C).path.rep N per K).eval U • field U) (prior G _) ∧
    read=∑s∈roster,money s*(actualTransport (C) (N:=N) (Raw R d A s) (road.trans cut) W-
      actualTransport (C) (N:=N) (Guard R d A s) road W) ∧
    ‖read‖≤((H)^requested)⁻¹*∑s∈roster,‖c s‖*∏a∈s.val,((r a)^(d a)*‖(dose a)⁻¹‖):=by
  intro dose money road field read
  obtain ⟨paid,rows,fee⟩:=signed R d A jf W hearing roster money
  refine ⟨paid,rows,?_⟩
  have cost (s:(J).Mode):‖money s‖=‖c s‖*∏a∈s.val,((r a)^(d a)*‖(dose a)⁻¹‖):=
    WilsonOriginalAlternativeTrialPhaseCurrency.cost r d dose positive (c s) s
  simpa only [cost] using fee
end YM.Integration.WilsonOriginalMicroscopicEntranceHeldPhase
end
