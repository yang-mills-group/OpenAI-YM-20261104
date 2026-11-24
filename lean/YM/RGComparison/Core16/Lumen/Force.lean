import YM.RGComparison.Core16.Lumen.Inverse
/-!
# Real cost score through a healthy H in θ variation, at all other real-side arguments
Nonanalytic far energies all retain numbers for this β. Keep actual thermal & genuine Jacobians.
The derivative of likelihood contributes no near cost (not removing from the density farther out).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen.Planet
open Function Filter Lattice RG Tree Wilson MeasureTheory Pressure Metric Push.Uniform Forge Push.AbsoluteSums.Animals Matrix
open PertExtension PertExtension.Series Tested Radial Therm
open Finset
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {G:Gauge}{S:Side}{ι k T A D:Type} [Fintype ι][Fintype k][Fintype T][Fintype D]
variable {X:Shelf G A D}(P:Planet X S ι k T)

def press (m : D → Bool) : G.Color →L[ℝ] Point G D:= (0:G.Color→L[ℝ] G.Color).prod (ContinuousLinearMap.pi (fun i=> if m i then ContinuousLinearMap.id .. else 0))
omit [Fintype D] in
lemma press_eq (m:D→Bool)(v:G.Color):press m v=(0,fun i=> if m i then v else 0):=by
    refine Prod.ext rfl ?_; funext i; change (if m i then ContinuousLinearMap.id .. else (0:G.Color→L[ℝ] G.Color)) v=(if m i then v else 0); split <;> rfl
lemma press_cost (m:D→Bool) (v:G.Color) : ‖press m v‖ ≤ ‖v‖:= by rw [press_eq,Prod.norm_def]; refine max_le ((le_of_eq (by simp)).trans (norm_nonneg v)) ?_; rw [pi_norm_le_iff_of_nonneg (norm_nonneg v)]; intro i; change ‖if m i then v else 0‖ ≤ _; split; rfl; simp

def hint (a:k) (i:ι)(p:D):Bool := decide (P.stem a p=some i)
variable (i:Wire G ι)
def drizzle (a:k)(g:ℝ)(x:Sky G ι):= (fderiv ℝ (X.U (P.glyph a)) (P.load a g x)) (press (P.hint a i.1) (roll i.2 (G.mat (x i.1))))
def attr (g:ℝ)(x : Sky G ι):= ∑ a∈P.within i.1, P.drizzle i a g x
omit [Fintype ι] [Fintype k] [Fintype T] [Fintype D] in
lemma hint_eq (a:k):press (P.hint a i.1) (colors G i.2) = P.tip a i:=by
    rw [tip,P.mark_price,press_eq]; congr 1; funext p; unfold portrait hint; cases h:P.stem a p with
    | none=> simp
    | some j=> by_cases h:j=i.1 <;> simp [h,one]

omit [Fintype k] [Fintype ι] [Fintype T] [Fintype D] in
lemma plotted (a:k)(g:ℝ): Continuous (P.load a g) :=by
    unfold load; refine continuous_const.prodMk (continuous_pi fun i=>?_); simp only [portrait]; rcases he:P.stem a i with _|j
    · exact continuous_const
    · exact G.continuous_curvature.comp (continuous_apply j)
variable {P}(H:P.Steady)(g:ℝ)
include H
lemma drizzle_cont (a:k): Continuous (P.drizzle i a g):= by
    unfold drizzle
    exact (((H.prices.smooth _).continuous_fderiv (by simp)).comp (P.plotted a g)).clm_apply ((press (P.hint a i.1)).continuous.comp ((roll_hot i.2).continuous.comp (G.continuous_mat.comp (continuous_apply i.1))))
lemma stout : Continuous (P.attr i g):=by unfold attr; exact continuous_finsetSum _ fun a _=> drizzle_cont i H g a
variable (hg:amen X g)
include hg

def raybay (i:Wire G ι):= gust i.2 i.1
omit H hg [Fintype ι] [Fintype k] [Fintype T] in
lemma porting (a:k)(x : Sky G ι): HasDerivAt (fun s=>P.load a g (raybay i s x))
    (press (P.hint a i.1) (roll i.2 (G.mat (x i.1)))) 0:=by
    rw [press_eq]; unfold load; apply HasDerivAt.prodMk (hasDerivAt_const ..); rw [hasDerivAt_pi]; intro d
    unfold hint portrait raybay gust; cases he:P.stem a d with
    | none=> simp; exact hasDerivAt_const ..
    | some r=> by_cases h:r=i.1
               · rw [h] at he; simp only [h, ↓reduceIte, Option.elim_some, decide_true]; exact sleeve ..
               simp [h]; exact hasDerivAt_const ..

lemma reading (x:Sky G ι) (hx : crisp X.δ (P.heat i.1) x) : HasDerivAt (fun t:ℝ=> (P.F g).output g (raybay i t x)) (- P.attr i g x / g^2*(P.F g).output g x) 0:=by
    let u := raybay i; let B:=P.F g; let S:=P.within i.1
    have hz : u 0 x=x:= gust_zero ..
    have hw : Continuous fun t => u t x := by
        have h: Continuous (fun r:ℝ=> (r,x)) := by fun_prop
        exact (gust_cont i.2 i.1).comp (f:=fun r:ℝ=> (r,x)) h
    have he : ∀ᶠ t:ℝ in 𝓝 0, crisp X.δ (P.heat i.1) (u t x):= hw.continuousAt.eventually ((crisp_open ..).mem_nhds (show crisp X.δ (P.heat i.1) (u 0 x) by rw [hz]; exact hx))
    have hl (s:ℝ) : AlwaysOff i.1 (u s x) x:= fun j hj=>if_neg hj
    let W:= - P.attr i g x/g^2
    have ht t: HasDerivAt (fun r=> B.cash t g (u r x)) (W* B.cash t g x) 0:=by
       let f (a:k)(r:ℝ):=B.cost t (u r x) a; let Δ (a:k):=if a∈S then P.drizzle i a g x else 0
       have h a: HasDerivAt (f a) (Δ a) 0:=by
          by_cases ha:a∈ S
          · have hw (y:Sky G ι) (hy:crisp X.δ (P.heat i.1) y): B.cost t y a=X.U (P.glyph a) (P.load a g y) := H.pay g hg _ _ _ (crisp_negligible _ _ le_rfl (P.soil_heat ha) hy)
            rw [show Δ a =_ from if_pos ha]; apply HasDerivAt.congr_of_eventuallyEq _ (show _=ᶠ[𝓝 (0:ℝ)] (fun s=> X.U (P.glyph a) (P.load a g (u s x))) from he.mono fun t ht=> hw _ ht)
            have hx :=H.prices.payment (P.glyph a) (P.load a g x) (mem_closedBall_zero_iff.mpr (P.load_calm H a hg (crisp_negligible _ _ le_rfl (P.soil_heat ha) hx)))
            have hp : HasFDerivAt (X.U (P.glyph a)) (fderiv ℝ (X.U (P.glyph a)) (P.load a g x)) (P.load a g (u 0 x)):= by rw [hz]; exact (hx.differentiableAt (by simp)).hasFDerivAt
            exact hp.comp_hasDerivAt 0 (porting i g a x)
          rw [show f a=fun (_:ℝ)=> B.cost t x a from funext fun s=>H.outside g hg a _ _ t (fun j hj=> hl _ j (fun e=> ha ((P.in_heat ..).1 (e ▸ hj)))), show Δ a=_ from if_neg ha]; exact hasDerivAt_const ..
       have hh:= HasDerivAt.fun_sum (u:=univ) fun a _=> h a
       have hS: ∑ x,Δ x=P.attr i g x:= by rw [show _ = ∑ a∈S,Δ a from (sum_subset (subset_univ S) (fun i _ hi=> show Δ i=0 from if_neg hi)).symm]; exact sum_congr rfl fun i hi=> if_pos hi
       rw [hS] at hh
       unfold Base.cash W; apply ((hh.neg.div_const _).exp).congr_deriv; rw [mul_comm]; simp only [Pi.neg_apply,f,hz]; rfl
    have h t : HasDerivAt (fun r=> B.choices t (u r x) * B.cash t g (u r x)) (W*(B.choices t x*B.cash t g x)) 0:=by
       have hW t s (hs : crisp X.δ (P.heat i.1) (u s x)): B.choices t (u s x) = B.choices t x := H.warm g hg _ _ _ (hl s) hs hx t
       apply HasDerivAt.congr_of_eventuallyEq _ (show _=ᶠ[𝓝 (0:ℝ)] (fun r=> B.choices t x * B.cash t g (u r x)) from he.mono fun s hs => congr_arg (·*_) (hW t s hs))
       rw [mul_left_comm W]; exact (ht t).const_mul _
    unfold Base.output; rw [mul_sum]; exact HasDerivAt.fun_sum (u:=univ) (fun a _=>h a)
end YM.RGComparison.Core16.Lumen.Planet
