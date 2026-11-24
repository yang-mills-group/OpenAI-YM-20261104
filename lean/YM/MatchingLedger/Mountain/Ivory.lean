import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Meristem
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Lac
import YM.MatchingLedger.Mountain.Copper

/-!
 # Norm read (finite differentiability; Meristem & complete controlling sums)
   The lemma `faintness` identifies the iterated derivative of the sum with the sum of the derivatives under a summable bound. The later estimates retain the budgets and the assembled messages. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.MatchingLedger.Mountain
open Set Function Filter Precision RG MeasureTheory Lattice Wilson Metric Push.Uniform Exterior
open Work.F02 ConnectedActivityE6.Blaze
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius InnerProductSpace Classical
variable {ι κ E F : Type} [Countable ι] [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
   [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
variable (k:ℕ)

lemma faintness (V:Set E)(hr:IsOpen V) (f:ι→ E→ F)(b:ι→ℝ)(he:Summable b) (ht: ∀ i v,v∈V→Brush k (b i) 1 (f i) v)(x:E)(hx:x∈V):
    ContDiffAt ℝ (↑k) (fun y=>∑' i:ι,f i y) x ∧∀ j≤k,Summable (fun i=>iteratedFDeriv ℝ j (f i) x)∧ iteratedFDeriv ℝ j (fun y=>∑' i:ι,f i y) x=∑' i,iteratedFDeriv ℝ j (f i) x:= by
   letI : MeasurableSpace ι := ⊤
   haveI : MeasurableSingletonClass ι:= ⟨fun _=> by trivial⟩
   let m:Measure ι:= Measure.count
   let T (x:E)(i:ι) := f i x
   have hnn(i):0≤ b i:= (ht i x hx).nonneg
   have hh(y)(hy:y∈V)(i)(j)(hj:j≤k) : normJ j (f i) y ≤ b i:=(Brush.offer.mp (ht i _ hy)).inside j hj
   have hK(y)(hy:y∈V)(j)(hj:j≤k): Summable (fun i=> normJ j (f i) y):= Summable.of_norm_bounded he (fun i=> by simpa using hh y hy i j hj)
   have hf(y)(hy:y∈V)(j)(hj:j≤k): Integrable (JetF T j y) m:= integrable_count_iff.mpr (hK y hy j hj)
   have hQ: Meristem T x m k:= ⟨V,hr.mem_nhds hx,Eventually.of_forall (fun i y h=> (ht i y h).smooth),fun i hi=> ⟨b,(integrable_count_iff.mpr ?_), fun y t=> (hf y t i hi).1, Eventually.of_forall (fun a y t=> hh y t a i hi)⟩⟩; swap
   · simpa only [Real.norm_of_nonneg (hnn _)] using he
   have hv {Z:Type} [NormedAddCommGroup Z][NormedSpace ℝ Z][FiniteDimensional ℝ Z]{g:ι→ Z}(p:Integrable g m): ∑' i:ι,g i=∫ i,g i ∂m:= by rw [integral_countable p]; simp [measureReal_def,m]
   have g: (fun y=>∑' i,f i y)=ᶠ[𝓝 x] (fun y=> ∫ i,T y i ∂m):= (hr.eventually_mem hx).mono fun y hy=> hv (integrable_count_iff.mpr (show Summable (fun i=>‖f i y‖) from by simpa only [normJ,norm_iteratedFDeriv_zero] using hK y hy 0 (Nat.zero_le _)))
   have q:= hQ.calls
   refine ⟨q.1.congr_of_eventuallyEq g,fun j hj=> ⟨(hK x hx j hj).of_norm,?_⟩⟩
   rw [(g.iteratedFDeriv (𝕜:=ℝ) j).eq_of_nhds,(q.2 j hj).2]; exact (hv (q.2 j hj).1).symm
variable {k}

lemma faintFace (V:Set E)(hr:IsOpen V)(f:ι→ E→ F)(b:ι→ℝ) {C:ℝ}(h: SumBudget b C)(he:∀ i v,v∈V→ Brush k (b i) 1 (f i) v)(x:E)(hx:x∈V) : Brush k C 1 (fun y=>∑' i:ι,f i y) x:=by
   obtain ⟨ht,hp⟩:= faintness k V hr f b h.2.1 he x hx
   refine Brush.offer.mpr ⟨ht,fun i hi=>?_⟩
   unfold normJ; rw [(hp i hi).2]; have hu := summable_norm_iff.mpr (hp i hi).1
   apply (norm_tsum_le_tsum_norm hu).trans; exact le_trans (hu.tsum_le_tsum (fun v=> (Brush.offer.mp (he v x hx)).inside i hi) h.2.1) h.2.2
variable {r C μ:ℝ}{d:ι→ℕ}{f:ι→E→F}
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma meral {p:E→ F}{v:E} (h: Allows k p v C) : Brush k C 1 p v:= Brush.offer.mpr ⟨h.analytic.of_le le_top,h.norm_le⟩
lemma revenue.faint (h: revenue r k μ d f C)(hm: 0≤μ) (x:E)(hx:x∈ball 0 r): Brush k C 1 (fun y=>∑' i,f i y) x:=
   faintFace _ isOpen_ball f _ (h.cash hm) (fun i _ hh=> meral (h.proceeds i _ hh)) x hx
end YM.MatchingLedger.Mountain
