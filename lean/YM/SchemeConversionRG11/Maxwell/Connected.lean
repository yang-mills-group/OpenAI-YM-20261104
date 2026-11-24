import YM.SchemeConversionRG11.Maxwell.Tracks

/-! # No continuous ambiguity due to tracks. Stay in metric compact spaces. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeConversionRG11.Corona
open Function Filter MeasureTheory Metric Maxwell Maxwell.Free Wick Tensor Set
open scoped Topology BigOperators RealInnerProductSpace InnerProduct
variable {G : Gauge}

def toDoors (G : Gauge) : (G.ColorIndex → G.Color) →L[ℝ] Door G := LinearMap.toContinuousLinearMap (𝕜:=ℝ) {
    toFun f := ∑ i : G.ColorIndex, tint (f i) ∘L cp i
    map_add' f g := by ext1 x; simp only [sum_apply,add_apply]; change (∑ i, x i • (f i+g i))=_; simp only [smul_add,Finset.sum_add_distrib]; rfl
    map_smul' t f := by ext1 x; simp only [sum_apply,smul_apply, RingHom.id_apply]; rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro i _; exact smul_comm (x i) t (f i) }
lemma door_test (L : Door G) : toDoors G (fun i ↦ L (unitColor G i))=L := by
  apply ContinuousLinearMap.ext; intro x
  change (∑ i : G.ColorIndex, tint (L (unitColor G i)) ∘L (cp (G:=G) i)) x=L x
  rw [sum_apply]
  conv_rhs => rw [← color_sum x, map_sum]
  simp only [map_smul]; rfl
lemma firm_cont : Continuous fun u : G.El ↦ firm u := by
  have he u : firm (G:=G) u=toDoors G (fun i ↦ firm u (unitColor G i)) := (door_test _).symm
  rw [funext he]; exact (toDoors G).continuous.comp (continuous_pi fun i ↦ adj_cont _)
lemma firm_flow (x : G.Color) : HasDerivAt (fun s : ℝ ↦ firm (G.lieExp (s • x))) (adh G x) 0 := by
  rw [show (fun s : ℝ ↦ firm (G.lieExp (s • x))) = (toDoors G) ∘ fun s i ↦ firm (G.lieExp (s • x)) (unitColor G i) from funext fun s ↦ (door_test _).symm]
  exact door_test (adh G x) ▸ (toDoors G).hasFDerivAt.comp_hasDerivAt (0:ℝ) (hasDerivAt_pi.mpr fun i ↦ adj_has ..)

/-- Minimized slice. -/
def Closer (T : Door G) := ∀ u : G.El, ‖T-1‖≤‖T-firm u‖
lemma around {T : Door G} (h : T∈Tracks G) (hx : ∀ u:G.El, firm u≠T) :
    ∃ L : Door G,L∈Tracks G ∧ Closer L ∧ L≠1 ∧ ‖L-1‖≤‖T-1‖ := by
  let D u := ‖T-firm (G:=G) u‖
  obtain ⟨u,_,hu⟩ := isCompact_univ.exists_isMinOn univ_nonempty (show Continuous D from (continuous_const.sub (firm_cont (G:=G))).norm).continuousOn
  let L := firm u⁻¹*T
  have he : firm u*L=T := by unfold L; rw [← mul_assoc,← firm_mul,mul_inv_cancel,firm_one,one_mul]
  have hm : ‖L-1‖=D u := by rw [← (firmFair u).norm_left, mul_sub,mul_one,he]
  refine ⟨L,inMul (firm_tracks u⁻¹) h,fun v ↦ ?_,fun hc ↦ ?_, ?_⟩
  · rw [hm,← (firmFair u).norm_left, mul_sub,he,←firm_mul]; exact hu (mem_univ (u*v))
  · rw [hc, mul_one] at he; exact hx u he
  rw [hm,← firm_one]; exact hu (mem_univ 1)
lemma scalesAdj (T : Door G) (r : ℝ) : (r • T)†=r • (T†) := ContinuousLinearMap.ext fun x ↦ ext_inner_right ℝ fun y ↦ by rw [ContinuousLinearMap.adjoint_inner_left]; change ⟪x,r • T y⟫=⟪r • _,y⟫; rw [real_inner_smul_left,real_inner_smul_right]; exact congr_arg (r*·) (ContinuousLinearMap.adjoint_inner_left T y x).symm

lemma toward_one (H : G.Simple) (T D : ℕ → Door G) (s : ℕ→ℝ) (hs : Tendsto s atTop (𝓝 0)) (hx : ∀ i,s i≠0)
    (ht : ∀ i,T i∈ Tracks G) (he : ∀ i,T i=1+s i • D i) {w : Door G} (hw : Tendsto D atTop (𝓝 w)) :
    w∈Store G := by
  classical
  have hT : Tendsto T atTop (𝓝 1) := by
    have hz : Tendsto (fun i ↦ s i • D i) atTop (𝓝 ((0:ℝ) • w)) := hs.smul hw
    rw [zero_smul ℝ w] at hz; rw [funext he]; exact (by simpa using hz.const_add (1:Door G))
  have hi : Tendsto (fun i ↦ (D i)†) atTop (𝓝 (w†)) := ContinuousLinearMap.adjoint.continuous.continuousAt.tendsto.comp hw
  have hA i : (D i)†*T i+D i=0 := by
    have hp : (T i)†*T i=1 := Fair.inv (ht i).1
    conv_lhs at hp => arg 1; rw [he i,map_add,ContinuousLinearMap.adjoint_one,scalesAdj]
    rw [add_mul,one_mul,scaleL] at hp
    conv_lhs at hp => arg 1; rw [he i]
    apply smul_right_injective (Door G) (hx i)
    dsimp only; rw [smul_zero,smul_add,add_comm]
    rw [add_assoc] at hp; exact add_eq_left.mp hp
  have hQ : w†= -w := by
    have hh := (hi.mul hT).add hw
    rw [mul_one] at hh
    simp_rw [hA] at hh
    exact eq_neg_of_add_eq_zero_left (tendsto_nhds_unique hh tendsto_const_nhds)
  apply tangent_form H hQ; intro x
  let V i := (D i)†*adh G x*T i + adh G x*D i
  have hv : Tendsto (fun i ↦ - V i) atTop (𝓝 (w*adh G x-adh G x*w)) := by
    have he := (((hi.mul_const (adh G x)).mul hT).add (tendsto_const_nhds (x:=adh G x) |>.mul hw)).neg
    rw [hQ,mul_one,show -w*adh G x=-(w*adh G x) from ContinuousLinearMap.ext fun _ ↦ rfl,show -(-(w*adh G x)+adh G x*w)=w*adh G x-adh G x*w by abel] at he; exact he
  apply (Store G).closed_of_finiteDimensional.mem_of_tendsto hv
  apply Eventually.of_forall; intro i; apply Submodule.neg_mem
  rw [← show (s i)⁻¹ • (s i • V i)=V i from inv_smul_smul₀ (hx i) _]; apply Submodule.smul_mem
  rw [show s i • V i = (T i)†*adh G x*T i - adh G x from ?_]
  · exact Submodule.sub_mem _ ((ht i).2 x) (LinearMap.mem_range_self _ _)
  unfold V; rw [he, map_add,ContinuousLinearMap.adjoint_one,scalesAdj]; simp only [mul_add,add_mul,mul_one,one_mul,smul_add]
  -- use precise order on quadratic
  simp only [scaleL,scaleR]; abel

end YM.SchemeConversionRG11.Corona
