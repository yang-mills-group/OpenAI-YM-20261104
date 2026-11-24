import YM.RGComparison.Core16.Lumen.Force
/-!
# Cutoffs suppress bad neighborhoods (not analytic and never put under Gaussian)

Need complement terms in remainder after expectation, because the mask saturates the derivative
w.r.t. one physical link only. Other-link events are untouched. Cost compiled on this same radius
receipt. Uniform tail probabilities charged by union over needed roots (Hut).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen.Planet
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Forge Push.AbsoluteSums.Animals Matrix
open Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G:Gauge}{S:Side}{ι k T A D:Type}
-- bump datum purchased from Good
variable {δ:ℝ} (b: ContDiffBump (0:ℝ))

structure Dust (δ:ℝ) :Prop where
   R : b.rIn=δ^2/8
   D : b.rOut=δ^2/4
   pos: 0<δ
lemma buys {δ:ℝ}(h:0<δ):∃ b:ContDiffBump (0:ℝ), Dust b δ:= by
    have hd:0<δ^2:=by positivity
    exact ⟨⟨δ^2/8,δ^2/4,by positivity,by linarith⟩,rfl,rfl,h⟩

def tenderness (B : G.Mat) :ℝ:= b (1-B.trace.re/G.repDim)
lemma feels : ContDiff ℝ ∞ (tenderness (G:=G) b):= by
    unfold tenderness; let p := (traceLinearMap (Fin G.repDim) ℝ ℂ).toContinuousLinearMap
    have hp: ContDiff ℝ ∞ (fun B:G.Mat=> B.trace.re) := Complex.reCLM.contDiff.comp p.contDiff
    exact (show ContDiff ℝ ∞ b from b.contDiff).comp (contDiff_const.sub (hp.div_const _))

def lamp (x:G.El):ℝ:= b (G.price x)
def shaft (j:G.ColorIndex)(x:G.El):= fderiv ℝ (tenderness (G:=G) b) (G.mat x) (G.colorMat (colors G j)*G.mat x)
lemma shaft_cont (j:G.ColorIndex):Continuous (shaft b j):=by
    exact (((feels (G:=G) b).continuous_fderiv (by simp)).comp G.continuous_mat).clm_apply (continuous_const.mul G.continuous_mat)
lemma lamp_cont : Continuous (lamp (G:=G) b):=b.continuous.comp G.continuous_price
lemma heats (j:G.ColorIndex)(x:G.El):HasDerivAt (fun t=>lamp b (spin j x t)) (shaft b j x) 0:= by
    change HasDerivAt (tenderness (G:=G) b ∘ (fun t=> G.mat (spin j x t))) _ _
    have he : G.mat (spin j x 0)=G.mat x:=by rw [spin_zero]
    unfold shaft; have hv : HasFDerivAt _ _ (G.mat (spin j x 0)):= show HasFDerivAt (tenderness b) (fderiv ℝ (tenderness b) (G.mat x)) _ from he.symm ▸ ((feels (G:=G) b).differentiable (by simp) _|>.hasFDerivAt) -- ▸
    exact hv.comp_hasDerivAt 0 (spin_mat j x)
variable {b}(h:Dust b δ)
include h
lemma far {x:G.El}(hx:δ ≤ G.chord x):∀ᶠ y:G.El in 𝓝 x,lamp b y=0:=by
    have hp := sq_le_sq₀ h.pos.le (G.chord_nonneg _)|>.2 hx
    rw [G.chord_price] at hp; have hh : b.rOut < G.price x:=by rw [h.D]; nlinarith only [hp,sq_pos_of_pos h.pos]
    filter_upwards [G.continuous_price.continuousAt.eventually (lt_mem_nhds hh)] with y hy
    exact b.zero_of_le_dist (by rw [Real.dist_eq,sub_zero,abs_of_nonneg (G.price_range y).1]; exact le_of_lt (show b.rOut< G.price y from hy))

omit h in
lemma flair (j:G.ColorIndex){x:G.El}(u:ℝ)(w:∀ᶠ y:G.El in 𝓝 x,lamp b y=u) : shaft b j x=0:= by
    have h₀:Tendsto (spin j x) (𝓝 0) (𝓝 x):=by
       have h: (spin j x 0)=x:=spin_zero ..
       have h₁ : Continuous (spin j x):=(spin_cont j).comp (f:=fun r:ℝ=>(x,r)) (by fun_prop)
       have h₂:= h₁.tendsto 0; rwa [h] at h₂
    exact (heats b j x).unique ((hasDerivAt_const ..).congr_of_eventuallyEq (h₀.eventually w))
lemma near {x:G.El}(hx:G.chord x < δ/2):∀ᶠ y:G.El in 𝓝 x,lamp b y=1:=by
    have hp := sq_lt_sq₀ (G.chord_nonneg _) (div_nonneg h.pos.le (zero_le_two))|>.2 hx; rw [G.chord_price] at hp
    have hh : G.price x < b.rIn:=by rw [h.R]; nlinarith only [hp]
    filter_upwards [G.continuous_price.continuousAt.eventually (gt_mem_nhds hh)] with y hy
    refine b.one_of_mem_closedBall ?_; rw [Metric.mem_closedBall,Real.dist_eq,sub_zero,abs_of_nonneg (G.price_range _).1]; exact le_of_lt (show G.price y < b.rIn from hy)

omit h
variable (b) [Fintype ι][Fintype k][Fintype T][Fintype D]
variable {X:Shelf G A D}(P:Planet X S ι k T)(i:Wire G ι)
def skip (x : Sky G ι):Prop:= crisp X.δ (P.heat i.1|>.erase i.1) x
def dark (x : Sky G ι): ℝ:= if P.skip i x then lamp b (x i.1) else 0
def faint (x : Sky G ι):ℝ:= if P.skip i x then shaft b i.2 (x i.1) else 0
omit [Fintype k] [Fintype T] [Fintype D] in
lemma dark_grip (x:Sky G ι):0 ≤ P.dark b i x ∧ P.dark b i x ≤ 1:= by unfold dark; split; exact ⟨b.nonneg,b.le_one⟩; norm_num
lemma havenreal {Y:Type*}[TopologicalSpace Y][MeasurableSpace Y][BorelSpace Y][CompactSpace Y]{f:Y→ℝ}(h:Continuous f):Envelope f:=⟨h.measurable, isCompact_univ.exists_bound_of_continuousOn h.continuousOn|>.imp (fun _ hh v=> hh v (Set.mem_univ v))⟩
omit [Fintype k] [Fintype T] [Fintype D] in
lemma cloaked {f:Sky G ι→ℝ}(hf:Envelope f):Envelope (fun x=> if P.skip i x then f x else 0):= by
    let s: Set (Sky G ι):= {x | P.skip i x}
    have hm:MeasurableSet s:= (crisp_open ..).measurableSet
    change Envelope (s.indicator f); exact ⟨hf.meas.indicator hm, hf.cost.choose,fun i=> (norm_indicator_le_norm_self f i).trans (hf.cost.choose_spec i)⟩
omit [Fintype k] [Fintype T] [Fintype D] in
lemma whirl : Envelope (P.dark b i) ∧ Envelope (P.faint b i) :=
    ⟨P.cloaked i (havenreal ((lamp_cont b).comp (continuous_apply i.1))),P.cloaked i (havenreal ((shaft_cont b i.2).comp (continuous_apply i.1)))⟩
variable {b P}(hJ:Dust b X.δ)
omit [Fintype k] [Fintype T] [Fintype D] in
private lemma spins (x : Sky G ι) (f:ℝ) : P.skip i (raybay i f x) ↔ P.skip i x:=by unfold skip crisp raybay gust; exact forall₂_congr (fun j hj => by rw [if_neg (ne_of_mem_erase hj)])
omit [Fintype k] [Fintype T] [Fintype D] in
lemma splat (x:Sky G ι): HasDerivAt (fun j=>P.dark b i (raybay i j x)) (P.faint b i x) 0:=by
    simp_rw [dark,spins]; unfold faint; by_cases h:P.skip i x
    · simp only [h, ↓reduceIte, gust,raybay]; exact heats ..
    simp_rw [if_neg h]; exact hasDerivAt_const ..
include hJ
omit [Fintype k] [Fintype T] [Fintype D] in
lemma away {x:Sky G ι}(hw:¬crisp X.δ (P.heat i.1) x):∀ᶠ t:ℝ in 𝓝 0, P.dark b i (raybay i t x)=0:=by
    simp_rw [dark,spins]; by_cases h:P.skip i x
    · have hl : X.δ ≤ G.chord (x i.1):=by
          contrapose! hw; intro j hj; by_cases he:j=i.1; rw [he]; exact hw; exact h j (mem_erase.mpr ⟨he,hj⟩)
      have hQ : Continuous (spin i.2 (x i.1)):= (spin_cont i.2).comp (f:=fun t:ℝ=> (x i.1,t)) (by fun_prop); have hP: Tendsto (spin i.2 (x i.1)) (𝓝 0) (𝓝 (x i.1)) := by simpa only [spin_zero] using (show Tendsto _ _ (𝓝 (spin i.2 (x i.1) 0)) from hQ.continuousAt.tendsto)
      simp only [h, ↓reduceIte, gust,raybay]; exact hP.eventually (far hJ hl)
    simp [h]
omit [Fintype k] [Fintype T] [Fintype D] in
lemma live {x:Sky G ι}(hw:crisp (X.δ/2) (P.heat i.1) x):P.dark b i x=1 ∧ P.faint b i x=0:=by
    have hs:P.skip i x:= crisp_negligible _ _ (by linarith [hJ.pos]) (erase_subset ..) hw
    unfold dark faint; rw [if_pos hs,if_pos hs]; have he:= near hJ (hw i.1 (P.loc_heat i.1)); exact ⟨he.self_of_nhds,flair _ 1 he⟩
end YM.RGComparison.Core16.Lumen.Planet
