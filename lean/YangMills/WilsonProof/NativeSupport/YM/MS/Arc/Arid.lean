import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.Pumps
/-!
# Bounds for analytic interpolation at compact lines

Only Re exponent, no imaginary exponential. Streak convenient tag $2z+1$.
 Hol-pump not by declaration; prove later. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real
open scoped Topology ContDiff Interval
open ContinuousLinearMap
variable {I E F G: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F][NormedAddCommGroup G] [NormedSpace ℝ G]
def LogMass (A:ℝ)(z:ℂ): ℝ:= A ^ (2*z.re+1)
def cover (A:ℝ)(f:Tree E F): Prop:=∃ C, 0≤C∧ C≤A ∧ ∀ r x, C<r → f (r,x)=0
-- simplify C actually; could use just A≥0 and vanishes. change
variable {z:UScale I}{f:Tree E F}{A:ℝ}
lemma trailer (h:Reflect f)(hh:ContDiff ℝ ∞ f)(hp:cover A f): cover A (chop f):= by
    obtain ⟨C,hC,hs,hP⟩:=hp; refine ⟨C,hC,hs,fun r x hx=>?_⟩; have hv : (fun q:ℝ=> f (q,x))=ᶠ[𝓝 r] fun _=>0:= (lt_mem_nhds hx).mono (fun t ht=> hP t x ht); have h0:= (hv.fderiv_eq (𝕜:=ℝ)); -- maybe no
    apply smul_right_injective F (r:=r) (hC.trans_lt hx).ne'; dsimp only; rw [restore h hh,← (dr hh x r).deriv,hv.deriv_eq,deriv_const,smul_zero]
lemma cut_cover (h:Reflect f)(hh:ContDiff ℝ ∞ f)(hp:cover A f)(m:ℕ): cover A (pruning m f):= by
    suffices hi : cover A (pruning m f) ∧ Reflect (pruning m f) ∧ ContDiff ℝ ∞ (pruning m f) from hi.1
    induction m with| zero=> exact ⟨hp,h,hh⟩| succ m ih=> rw [spent]; exact ⟨trailer ih.2.1 ih.2.2 ih.1,chop_even ih.2.1 ih.2.2,c_chop ih.2.2⟩
-- replace weight with truncated version
def drop (A:ℝ)(z:ℂ):ℝ→ℂ := (Iic A).indicator (cloud z)
lemma stream_bound {Z:I→ℂ}(hh:∀ i,ups (Z i))(hA:1≤A): shadeB (fun i=>drop A (Z i)) (fun i=> LogMass A (Z i)) 0 where
    borel i:= cloud_sees.indicator (by apply measurableSet_Iic)
    pos i:= rpow_nonneg (by linarith) _
    pay i:= by
       filter_upwards [ae_restrict_mem (μ:=volume) (measurableSet_Ioi (a:=(0:ℝ)))] with p hp; unfold drop; simp only [pow_zero,mul_one]; by_cases hx:p∈ Iic A
       · rw [Set.indicator_of_mem hx,cloud_weight hp]; exact rpow_le_rpow (le_of_lt (show 0<p from hp)) hx ((hh i : _ < _).le)
       rw [Set.indicator_of_notMem hx,norm_zero]; exact rpow_nonneg (by linarith) _
variable [NormedSpace ℂ F][IsScalarTower ℝ ℂ F]
omit [CompleteSpace F] [IsScalarTower ℝ ℂ F] [NormedAddCommGroup E][NormedSpace ℝ E] in
lemma fetch_drop (h:cover A f) (Z:ℂ): fetching f (drop A Z)= fetching f (cloud Z):= by
   funext p; unfold fetching; refine integral_congr_ae (Eventually.of_forall fun t=>?_); unfold fetchP drop; dsimp only; by_cases hp:t∈ Iic A; rw [Set.indicator_of_mem hp]; obtain ⟨C,hC,hZ,H⟩:=h; simp only [H _ p (lt_of_le_of_lt hZ (Set.notMem_Iic.mp hp)), smul_zero]
variable {u:I→Tree E F}{a:I→ℝ}{Z:I→ℂ}
lemma compact_price (h:quiet z u a) (hm:∀ i,Reflect (u i))(ht:∀ i,cover A (u i))(hA:1≤A)(hx:∀ i,ups (Z i))(m:ℕ): veg z (fun i=>coreC (cloud (Z i)) m (u i)) (fun i=>a i*LogMass A (Z i)):= by
   have he:=core h hm m (stream_bound hx hA); simp_rw [coreC,fetch_drop (cut_cover (hm _) (h.smooth _) (ht _) _)] at he; exact he
-- nested full smooth compact
variable [MeasurableSpace G][BorelSpace G][FiniteDimensional ℝ G](μ:Measure G)[μ.IsAddHaarMeasure]
variable {f:I→(G×ℝ)× E→ F}
def towards (A:ℝ)(f:(G×ℝ)× E→ F): Prop:= ∀ p r x,A<r → f ((p,r),x)=0
lemma compact_sky (h: quiet z f a)(hm:∀ i,mirror (f i))(ht:∀ i,towards A (f i))(hA:1≤A)(hx:∀ i, ups (Z i))(m:ℕ): veg z (fun i=>swoop (Z i) μ m (f i)) (fun i=> a i * LogMass A (Z i)):= by
   refine compact_price (u:=fun i=> carpet μ (f i)) (Q.Gquiet μ h) (fun i=>mirror_r μ (hm i)) (fun i=>⟨A,by linarith,le_rfl,fun r x hp=>?_⟩) hA hx m; unfold carpet; dsimp only; simp_rw [ht i _ _ _ hp, integral_zero]
end YM.MS.Arc
