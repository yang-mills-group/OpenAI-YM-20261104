import YM.Integration.WilsonSurveyedColorSubtraction

/-! The finite choices of open color index preserve the dimensional
test estimates, smoothness, and the full holomorphic MS regulator germ. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorVacuumTests
open Set Function Filter MS Plane Koszul Heat Flux Arts Arts.Pilot Spin Arc Wire Rock
open Landau Garment Shine Hem Mell Pearl Train
open WilsonSurveyedColorTensor WilsonSurveyedColorQuotient WilsonSurveyedColorPilot
open WilsonSurveyedColorSubtraction
open scoped Classical BigOperators Topology ContDiff
variable {G : Gauge} (U : G.Color ≃ₗᵢ[ℝ] G.Color) {D P V : Type}

theorem momentum (f : V → P) (F : Score G D P) (w : Legs (Note G D V)) :
    turn U F (w.map (fun i => (i.1,f i.2))) =
      turn U (fun v => F (v.map (fun i => (i.1,f i.2)))) w := by
  induction w generalizing F with
  | nil => rfl
  | cons i w ih =>
    change Koszul.D (i.1,f i.2) (turn U F) _ = Koszul.D i (turn U _) w
    rw [derivative,derivative]
    simp only [Finset.sum_apply,Pi.smul_apply]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (entry U j i.1.2 • ·) (ih (Koszul.D (MS.Color.setLeg (i.1,f i.2) j) F))

theorem closedTest {I X : Type} (T : Submodule ℂ (I → ℂ)) (f : I → X → ℂ)
    (each : ∀ w, (fun i => f i w) ∈ T) {C : (X → ℂ) → ℂ} (hc : C∈Centre X) :
    (fun i => C (f i)) ∈ T := by
  refine Submodule.span_induction (p:=fun C _ => (fun i => C (f i)) ∈ T) ?_ T.zero_mem ?_ ?_ hc
  · rintro _ ⟨w,rfl⟩
    exact each _
  · intro A B _ _ hA hB
    exact T.add_mem hA hB
  · intro c A _ hA
    exact T.smul_mem c hA

variable {I E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def tested (z : UScale I) (a : I → ℝ) (ha : ∀ i, 0≤a i) : Submodule ℂ (I × E → ℂ) where
  carrier := {f | veg z (fun i x => f (i,x)) a}
  zero_mem' := Costs.zero (fun i _ _ => ha i)
  add_mem' hf hg := Costs.add hf hg
  smul_mem' c _ hf := Costs.L (c • ContinuousLinearMap.id ℝ ℂ) hf

theorem prices {z : UScale I} {a : I → ℝ} {f : I → Mob G} (h : fell z a f) :
    fell z a (fun i => allDims U (f i)) := by
  intro m E _ _ _ w
  have a0 := znon h
  let T := tested (E:=E) z a a0
  let F (ix : I × E) (v : Wire (Cfield G m) E (SectorP m)) := fieldVal (f ix.1 m) v ix.2
  have he := closedTest T F (fun v => h m E v) ((pilot U).sense.reaches w)
  change veg z (fun i x => (pilot U).beam (F (i,x)) w) a at he
  change veg z (fun i x => turn U (f i m) (w.map (fun l => (l.1,l.2 x)))) a
  have point (i : I) (x : E) :=
    momentum U (fun A : E →L[ℝ] SectorP m => A x) (f i m) w
  simp_rw [show ∀ (i : I) (x : E), turn U (f i m) (w.map (fun l => (l.1,l.2 x))) =
      turn U (fun v => f i m (v.map (fun l => (l.1,l.2 x)))) w from point]
  simpa only [emits,F,fieldVal,sail] using he

theorem forest {A : Set ℂ} {f : ℂ → Mob G} (hf : Hol A f) :
    Hol A (fun z => allDims U (f z)) := by
  refine ⟨fun c R hr hc => prices U (hf.price c R hr hc),?_⟩
  intro m w z hz
  let T : Submodule ℂ (ℂ → ℂ) := {
    carrier := {F | DifferentiableAt ℂ F z}
    zero_mem' := differentiableAt_const _
    add_mem' ha hb := ha.add hb
    smul_mem' c _ ha := ha.const_smul c }
  have h := closedTest T (fun z => f z m) (fun l => hf.top m l z hz)
    ((pilot U).sense.reaches w)
  change DifferentiableAt ℂ (fun i => (pilot U).beam (f i m) w) z at h
  change DifferentiableAt ℂ (fun i => turn U (f i m) w) z
  simpa only [emits] using h

theorem live {f : Coat G} (hf : Live f) : Live (coat U f) := by
  obtain ⟨F,g,R,hR,hg,he,rfl⟩ := hf
  exact ⟨allDims U (g 0),_,R,hR,forest U hg,he.mono (fun z hz => congrArg (allDims U) hz),rfl⟩

theorem meromorphic {f : Coat G} (hf : mer f) : mer (coat U f) := by
  obtain ⟨k,hk⟩ := hf
  have h := live U hk
  refine ⟨k,?_⟩
  apply Live.congr h
  exact Eventually.of_forall (fun z => map_smul (allDims U) _ _)

end YM.Integration.WilsonSurveyedColorVacuumTests
end
