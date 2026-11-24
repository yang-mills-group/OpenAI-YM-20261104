import YangMills.WilsonProof.NativeSupport.Commissioned259.Quotes.Energy
/-! # Export this progression about actual reports in the two-radius measurement.
    Compact G.1 basis & clock, enough also for G.1 all T polynomial estimates. Note
    the *strong* physical (C5) hypotheses. Keep purchases before use. No G.9 needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Quotes
open Function Filter Set Asymptotics PowerSeries MeasureTheory
open Extraction Table Spec OPE OPE.Orbits Climb PhysMS
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Maxwell Maxwell.Free Trace.Pilot XSpace XSpace.Normalize XSpace.Structure1 Dframe
open FVA2.Scale Scale.Jury ScaleCost O.Score Comparing Pose Original Matrix
open Facets Reg.Point
open scoped Topology ContDiff Classical BigOperators Matrix
variable {I : Type*}{L:Filter I} {G : Gauge} {d n q m e : ℕ} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (U : Final C f S) (J Y : ℝ→PhysMS.tower S) (N : WilsonPrescription G) {A : ∀ d:ℕ, ℝ→Change G d}
    (hJ:Leading U J) (P:Realized J Y N A (Paper.meter U J N.criterion)) (ν:ℝ)
    {sim : G.Simple} (M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim M σ dial)
    (h : Shop U J N) (hp: normal U J N.store) (hQ:∀ d:ℕ, Mixture U J N d)
local notation "late" => 𝓝[>] (0:ℝ)
local notation "δ" => g0 G
local notation "t" => Paper.meter U J N.criterion
local notation "ψ" => GroupS.ψ N.criterion M ν
local notation "Z" => GroupS.gaugeN N.scheme N.criterion M ν
local notation "l" => Quotes.together
local notation "rr" => (@Prod.fst ℝ ℝ)
local notation "T" => (@Prod.snd ℝ ℝ)
lemma fstt : Tendsto rr l late:= tendsto_fst
lemma far : ∀ᶠ i in l,T i∈Icc 1 2 := tendsto_principal.mp (tendsto_snd (f:=late))
include H P hJ h hp hQ
lemma clock_form (p:ℕ)(hz:1 ≤ p) : ClockQuote G ψ t p := by
  let X:= (clock_unit U J Y N hJ P ν M H h hp (hr:=fstt) far (hQ _) p hz)
  have he:= homebound X.expense; obtain ⟨c,hc,V⟩:= he.exists_pos
  refine ⟨c,hc,?_⟩; filter_upwards [eventually_prod_principal_iff.mp V.bound, g0_pos sim] with r h v s ht hu
  have hi : _ := h _ ⟨ht,hu⟩
  apply hi.trans_eq; change c*‖δ r^(p+1)*1‖=_; rw [mul_one,Real.norm_of_nonneg (by positivity)]
lemma field_form (p:ℕ)(hz:1 ≤ p) (d:ℕ) : FieldQuote G Z t (via Y) d p := by
  let K i:= ScaleCost.actual (via Y) d (rr i) (T i)- ScaleCost.form Z d (T i) p (t (rr i)); have hi : (stiffness ∘ K)=O[l] fun i=> δ (rr i)^(p+1) := by
    refine matrixPay.mpr fun i j=> ((homebound ((estimate U J Y N hJ P ν M H h hp (hr:=fstt) far (hQ d) (hQ _) p hz i j).expense)).congr_left ?_).congr_right ?_
    · intro x; rfl
    intro i; exact mul_one _
  obtain ⟨c,hc,Q⟩:= hi.exists_pos
  refine ⟨c,hc,?_⟩; filter_upwards [eventually_prod_principal_iff.mp Q.bound, g0_pos sim] with r h v s ht hu
  calc
    _ ≤ ‖stiffness (K (r,s))‖ := le_abs_self _
    _ ≤ _ := (h _ ⟨ht,hu⟩).trans_eq (by change c*‖δ r^(p+1)‖=_; rw [Real.norm_of_nonneg (by positivity)])
theorem G1_step : StepCost G ψ Z t (via Y) := by
  refine ⟨fun m=> clock_form U J Y N hJ P ν M H h hp hQ (m+1) (by omega),fun d m=> field_form U J Y N hJ P ν M H h hp hQ (m+1) (by omega) d⟩
end YM.FVA2.GradedFar259.Quotes
