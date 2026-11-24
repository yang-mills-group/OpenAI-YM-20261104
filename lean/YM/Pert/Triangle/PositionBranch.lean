import YM.Pert.Scale.End
import YM.Pert.Triangle.FirstChange
/-! Conditional position-chart coupling diagnostic through six, with unconditional raw leading zero along the actual Wilson sequence. These are correlation tests, not exact connected phase-wise predictions or arbitrary absolute-scale results. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Pert.Triangle
open Function Set Filter Topology MeasureTheory Maxwell Analysis Spec Climb Labels RawLabels Extra.FD Position Scale Ward
open scoped Topology ContDiff
variable {G:Gauge} (hg:G.Simple) (F:Frames G)
include hg in
lemma no_variation {x:Points 3} (hx:x∈conf 3) : disc (fun i=>(⟨6,(basic F) i⟩:(freeTable F).Tag)) x=0 := free_point_base hg F hx
lemma rotationFixed (K:E4≃ₗᵢ[ℝ]E4) (p:Points 3) :
    profileChoice (WithLp.toLp 2 (fun j:Fin 3=>K (p j)))=profileChoice p := congrArg (fun r:ℝ=>(↑(stamp*r):ℂ)) (real_rotation K p)
lemma choiceFar {a : Points 3}(ha:a∈tsupport profileChoice) : farEnough a := by
   refine candidFar conventionSeparate ?_
   apply closure_mono (show support profileChoice ⊆ support testReal from fun p hp=> ?_) ha
   exact fun e=>hp (show (↑(stamp*testReal p):ℂ)=0 by rw [e, mul_zero];rfl)
abbrev inquiry (F : Frames G) := candidate F profileChoice
theorem clean (C:Family G) : CleanProfiles (inquiry C.labels) := fun _=>⟨profileChoice, rfl⟩
-- same hierarchy
variable {C : Family G} {I : Extraction.Order} {S : Table C.book} {b : Final C I S} (X:Scaling S) (h:FirstExtension b X)
local notation "Q" => inquiry C.labels
include hg
omit X in
lemma whiteness : decode Q (white Q) (i:=show Fin (Conditions.slots Q) from (0:Fin 1)) (basic C.labels) = 0 := by
  let M := (freeTable C.labels).classMoment (freeTable C.labels) (fun _:Fin 3=>6)
  have he (q:Fin 3→_): ContinuousOn (fun x:Points 3=> M x q) (conf _) := (((freeTable C.labels).class_smooth _ (table_smooth _) (fun i=>(⟨6,q i⟩ : (freeTable C.labels).Tag))).continuousOn)
  rw [decode_profile Q (white Q) (i:=show Fin (Conditions.slots Q) from (0:Fin 1)) (clean _) M he (fun _=>rfl)]
  change (∫ x: Points 3,profileChoice x * M x (basic C.labels))=0
  have q x : profileChoice x * M x (basic C.labels)=0 := by
    change profileChoice x * (disc (fun j=> (⟨6,basic C.labels j⟩:(freeTable C.labels).Tag)) x)=0
    by_cases hx:x∈conf 3;rw [no_variation hg C.labels hx,mul_zero]; rw [show profileChoice x=0 from Test.vanishes _ hx,zero_mul]
  simp_rw [q,MeasureTheory.integral_zero]

variable (G) in
def byDiagnostic (x:ℂ) := x/(cTest G)
variable {n:ℕ} (A : Conditions C.labels 6 n) {φ : Ledger A→Buffer C.labels 6}
def bareMeasure (k:ℕ) := byDiagnostic G (exactMean X k (basic C.labels) profileChoice)
def positionMeasure (k:ℕ) (s:ℝ) := byDiagnostic G (Complex.ofReal (actualTest Q X (φ:=φ) k s 0))
def predictedMeasure (L : Lattice.Side) (k' j p:ℕ) := bareResponse A (φ:=φ) profileChoice L k' p j / (cTest G).re
include h in
theorem actual_bare_leading : Tendsto (bareMeasure X) atTop (𝓝 0) := by
   have he := exact_tape X h (basic C.labels) profileChoice
   unfold bundle at he
   have H (x:Points 3) : profileChoice x * disc (fun i => (⟨6,basic C.labels i⟩ :(freeTable C.labels).Tag)) x=0 :=
       (by by_cases hx:x∈conf 3;rw [no_variation hg C.labels hx,mul_zero]; rw [show profileChoice x=0 from Test.vanishes _ hx,zero_mul])
   simp only [H,integral_zero] at he
   unfold bareMeasure byDiagnostic; convert! (he.div_const (cTest G)) using 1; simp
omit hg in
theorem predicted_even {J} (hf : Parity.Fair A J) (hu:Reports (chart A) (white A) 0 φ)
   (L : Lattice.Side) (hL : Tendsto (fun i=>finite A L i 0) atTop (𝓝 (white A))) j p (he:Even j) :
    ∀ᶠ k in atTop, predictedMeasure A (φ:=φ) L k j p = 0 := (vanishes A profileChoice hf hu L hL p j he).mono fun k hk=>by simp only [predictedMeasure,hk,zero_div]
-- raw exact law here not adjusted in all μ frame
include h in
theorem adjusted_limit (hq:CleanProfiles A) (hl:Reports (chart A) (white A) 0 φ) {s:ℝ} (hs:0<s) :
   Tendsto (fun j:ℕ×ℝ=>positionMeasure X A (φ:=φ) j.1 j.2) (atTop ×ˢ 𝓝 s) (𝓝 0) := by
  have z : chart Q (white Q,0) 0=0 := by
    change Complex.re (decode Q (white Q) (i:=show Fin (Conditions.slots Q) from (0:Fin 1)) ((motor C.labels 0) ∘ basic C.labels))=0
    rw [show (motor C.labels (d:=6) 0)=ContinuousLinearMap.id ℝ _ from by unfold motor; simp only [Submodule.coe_zero,add_zero];rfl]
    change (decode Q (white Q) (i:=show Fin (Conditions.slots Q) from (0:Fin 1)) (basic C.labels)).re=0
    rw [whiteness hg (C:=C)];rfl
  let hd := response_limit h hq hl Q (clean _) hs
  have hp := (continuous_apply (A:=fun _:Fin 1=>ℝ) 0).continuousAt.tendsto.comp hd
  rw [z] at hp
  have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp hp |>.div_const (cTest G)
  simpa only [Complex.ofReal_zero,zero_div,positionMeasure,byDiagnostic,Function.comp_def] using ht
end YM.Pert.Triangle
