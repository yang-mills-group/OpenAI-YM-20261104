import YM.Integration.FVA1Physical.Round2.PhysicalRectangle

/-! Restrict arbitrary sets of chart coordinates while keeping the
original rooted spatial jet majorants, even when each test chooses a
different frozen complement. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Round2
open Filter Function Finset Lattice Push Push.Uniform MSbar MSbar.Lis MSbar.Whisk
open scoped Classical BigOperators Topology ContDiff
variable {σ : Type} [Fintype σ]

def coordinateProjection (K : Finset σ) : Positions σ →L[ℝ] Positions σ :=
  ContinuousLinearMap.pi fun i => if i∈K then ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:σ=>ℝ) i else 0

def coordinateSlice (K : Finset σ) (base x : Positions σ) : Positions σ :=
  fun i => if i∈K then x i else base i

omit [Fintype σ] in
theorem coordinateSlice_affine (K : Finset σ) (base x : Positions σ) :
    coordinateSlice K base x=coordinateSlice K base 0+coordinateProjection K x := by
  funext i
  by_cases hi : i∈K <;> simp [coordinateSlice,coordinateProjection,hi]

omit [Fintype σ] in
theorem coordinateProjection_bolt (K : Finset σ) (i : σ) :
    coordinateProjection K (bolt i)=if i∈K then bolt i else 0 := by
  funext j
  by_cases hi:i∈K <;> by_cases hj:j∈K <;> by_cases he:j=i <;>
    simp_all [coordinateProjection,bolt]

theorem coordinateSlice_ball (K : Finset σ) {base x : Positions σ} {w:ℝ}
    (hb : base∈Metric.closedBall 0 w) (hx : x∈Metric.closedBall 0 w) :
    coordinateSlice K base x∈Metric.closedBall 0 w := by
  have hw := (norm_nonneg base).trans (mem_closedBall_zero_iff.mp hb)
  apply mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg hw).mpr _)
  intro i
  by_cases h:i∈K
  · simpa [coordinateSlice,h] using (norm_le_pi_norm x i).trans (mem_closedBall_zero_iff.mp hx)
  · simpa [coordinateSlice,h] using (norm_le_pi_norm base i).trans (mem_closedBall_zero_iff.mp hb)

private theorem affine_roc {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] (P : X →L[ℝ] E) (b : E) (F : E → ℝ)
    (l : List X) {x : X} (k : ℕ) (h : ContDiffAt ℝ k F (b+P x)) (len : l.length≤k) :
    roc (fun y=>F (b+P y)) l x=roc F (l.map P) (b+P x) := by
  induction l generalizing x with
  | nil => rfl
  | cons i l ih =>
    have sm : DifferentiableAt ℝ (roc F (l.map P)) (b+P x) :=
      (Lis.smooth k 1 _ h (by simp only [List.length_cons,List.length_map] at *; omega)).differentiableAt (by simp)
    have germ : roc (fun y=>F (b+P y)) l =ᶠ[𝓝 x] (fun y=>roc F (l.map P) (b+P y)) :=
      ((continuous_const.add P.continuous).continuousAt.eventually (h.eventually (by simp))).mono
        (fun y H=>ih H (by simp only [List.length_cons] at len; omega))
    rw [roc,List.map_cons,roc,germ.fderiv_eq]
    exact congrArg (fun A : X →L[ℝ] ℝ=>A i) ((sm.hasFDerivAt.comp x (P.hasFDerivAt.const_add b)).fderiv)

private theorem roc_zero_slot {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F:E→ℝ) (l:List E) (zero : (0:E)∈l) : roc F l=0 := by
  induction l with
  | nil => simp at zero
  | cons i l ih =>
    rcases List.mem_cons.mp zero with h|h
    · subst i; funext x; simp [roc]
    · funext x; rw [roc,ih h]; simp

theorem coordinateSlice_buoy (K : Finset σ) (base : Positions σ) (F : Positions σ → ℝ)
    (l : List σ) (x : Positions σ) (k : ℕ)
    (h : ContDiffAt ℝ k F (coordinateSlice K base x)) (len : l.length≤k) :
    buoy (F ∘ coordinateSlice K base) x l =
      if ∀ i∈l,i∈K then buoy F (coordinateSlice K base x) l else 0 := by
  let P := coordinateProjection K
  let b := coordinateSlice K base 0
  have eq : coordinateSlice K base=fun y=>b+P y := funext (coordinateSlice_affine K base)
  rw [eq] at h ⊢
  unfold buoy
  rw [show roc (F ∘ fun y=>b+P y) (l.map bolt) x=
    roc F ((l.map bolt).map P) (b+P x) from affine_roc P b F _ k h (by simpa using len)]
  by_cases kept : ∀ i∈l,i∈K
  · rw [if_pos kept]
    congr 1
    rw [List.map_map]
    exact List.map_congr_left fun i hi => by simp only [Function.comp_apply,P,coordinateProjection_bolt,if_pos (kept i hi)]
  · rw [if_neg kept]
    obtain ⟨i,hi,off⟩ := by simpa only [not_forall,Classical.not_imp] using kept
    have zero : 0 ∈ (l.map bolt).map P := List.mem_map.mpr
      ⟨bolt i,List.mem_map_of_mem hi,by simp [P,coordinateProjection_bolt,off]⟩
    rw [roc_zero_slot _ _ zero]; rfl

end YM.Integration.FVA1Physical.Round2
