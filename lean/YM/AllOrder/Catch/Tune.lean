import YM.AllOrder.Catch.Lear
import YM.AllOrder.Laplace.Tilt
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch
open Function Filter Finset Topology Metric MeasureTheory
open PhysicalNext Repeat Lantern ConnectedActivityE6 Blaze Brush PositionX.Jet Laplace Laplace.SigmaP Tensor
open PertExtension.Series Radial
open scoped Topology Classical BigOperators ContDiff
variable {X Y ι:Type*}{V U W:X → Type}
variable [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (U i)][∀ i,NormedSpace ℝ (U i)]
variable {T:Clock X} {p a b c W₀:X→ℝ} {k j n:ℕ}{s v d B C:ℝ}{f:X→Word ℝ}{g:∀ i:X,V i→ℝ}
local notation "H"=> T.Meter
-- Run at fixed post. Hold z ergonomic. Allows HE tolerance shrinking with δ. Test weighting.Y.*.
namespace Clock.Meter
lemma close (F:ℝ→ℝ)(hx:ContDiffAt ℝ ω F d)(ha:Tendsto a T.rail (𝓝 d))(hb:Tendsto b T.rail (𝓝 d))(h:T.Meter (a-b) s): T.Meter (fun i=> F (a i) - F (b i)) s:= by
 obtain ⟨C,hC,HT⟩:= Brush.neighborhood d (k:=1) (f:=F) (by exact hx.of_le le_top); obtain ⟨r,hr,hR⟩:= Metric.mem_nhds_iff.mp HT; let V:= ball d r; have hp x (hz:x∈ V):Brush 1 C 1 F x:=hR hz;
 refine (h.lscale C).smaller (((ha.eventually (ball_mem_nhds _ hr)).and (hb.eventually (ball_mem_nhds _ hr))).mono fun i hi=>?_); have hu := (convex_ball d r).norm_image_sub_le_of_norm_fderiv_le (f:=F) (C:=C) (fun x hx=>(hp x hx).smooth.differentiableAt (by simp)) (fun x hx=> by rw [← norm_iteratedFDeriv_one]; exact ((Brush.offer.mp (hp x hx)).2 1 le_rfl)) hi.2 hi.1; change |F (a i)-F (b i)|≤ |C*(a i-b i)| ; rw [abs_mul,abs_of_pos hC]; exact hu -- dslope
end Clock.Meter
namespace TaylorCap
lemma tends (h:TaylorCap T k b a f)(hp:Tendsto (fun i=> f i 0) T.rail (𝓝 d)): Tendsto a T.rail (𝓝 d):= by
 have hi := (h.lead.down (by norm_num)).add hp; simp only [sub_add_cancel,zero_add] at hi; exact hi
lemma delaying (h:∀ i≤k,T.Meter (fun j=>f j i) s)(ht:H a v)(hs:0≤v): Cover T j (s+v*k) (fun _=>1) (fun i=>delay (f i) k) a:= by
 let m (l:ℕ) i (x:ℝ):= x^l* f i l; have hp l (he:l∈ range (k+1)) : Cover T j (s+v*k) (fun _=>1) (m l) a:= by
    let hq:= Finset.mem_range.mp he; let hv:= (show Cover T j v (fun _=>1) (fun (_:X)=>id) a from Cover.exponent hs ht.ab); let n:= h l (by omega); unfold m
    simp_rw [mul_comm _ (f _ _)]; refine ((hv.powerC l).smul n|>.weak (add_le_add le_rfl (by gcongr; omega))) -- type ℝ annotation
 have he: (fun i=>delay (f i) k)=∑ l∈range (k+1),m l:= funext fun i=>funext fun y=>by simp [delay,m]; -- layout
 rw [he]; exact Cover.collects _ hp
-- smooth h: center x∈cost.Rpower s>0.Lean.Truncated. hCap supplies jets not necessarily model scale finite.This proves arbitrary C.F(h_P(p)). Needed Chirps.
lemma delay_t (h:∀ i≤k,H (fun j=> f j i) 0)(ht:Tendsto (fun i=> f i 0) T.rail (𝓝 d))(ha:H a v)(he:v<0): Tendsto (fun i=> delay (f i) k (a i)) T.rail (𝓝 d):= by
 let g (j:ℕ)i:= a i^(j+1) * f i (j+1); have hP : H (fun i=>∑ j∈range k,g j i) v:= by
   apply Clock.Meter.sum; intro l hl; apply (((ha.pow (l+1)).mul (h _ (Finset.mem_range.mp hl)))).weak; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) l];
 have hQ := (hP.down he).add ht; simp_rw [delay,sum_range_succ',smul_eq_mul,pow_zero,one_mul]; simpa only [zero_add] using hQ
local notation "T₁"=> T.book (fun i:X => Metric.closedBall (0:ℝ) (b i))
lemma process (F:ℝ→ℝ)(hx:ContDiffAt ℝ ω F d)(h:TaylorCap T k b a f) (hp:Tendsto (fun i=> f i 0) T.rail (𝓝 d))(hb:H b (-(1/2)))(he:∀ᶠ i in T.rail,0<b i) : TaylorCap T k b (F∘a) (fun i=>run F (f i)) := by
 obtain ⟨hx₀,hx₁⟩:= (show Tendsto a T.rail (𝓝 d) ∧ Tendsto (fun i=>delay (f i) k (b i)) T.rail (𝓝 d) from ⟨h.tends hp, delay_t (fun i=>h.steps i) hp hb (by norm_num)⟩)
 let P:=T₁; let Q (t:ℕ) i:= delay (f i) t; let x:X→ ℝ:=fun i=> Q k i (b i); let P' := Sigma.fst (β:=fun i=> {t:ℝ//t∈Metric.closedBall 0 (b i)}); let hh := T.liftF P'; have h': Tendsto P' P.rail T.rail:= hh.tends;
 have hm j (hj:j≤k): TaylorCap T j b (fun i=> F (Q j i (b i))) (fun i=> run F (f i)):= by
    let x(i:Σ i, {t:ℝ//t∈Metric.closedBall 0 (b i)}):= i.2.1; let f(i:Σ i, {t:ℝ//t∈Metric.closedBall 0 (b i)}):= f (P' i); 
    let t:= fun i=> F ∘ Q j i; let hζ l (hl:l≤j) : P.Meter (fun i=> f i l) 0:= (h.steps l (hl.trans hj)).pays P' hh
    let hb' := cost_r hb; have ht:Cover P (j+1) 0 (fun _=>1) (fun i=> Q j (P' i)) x:= (delaying hζ (hb'.weak (by norm_num : -(1/2:ℝ)≤0)) (le_refl 0)).weak (by simp) -- needs hb attr T etc
    have hXX: Cover P (j+1) 0 (fun _=>1) (fun i=> t (P' i)) x:= by
       refine (Cover.weak (T:=P) (a:=0+0*(j+1:ℕ)) (Cover.comp (U:=fun _=>ℝ) (V:=fun _=>ℝ) (W:=fun _=>ℝ) (a:=0) (b:=0) (f:=fun i=> Q j (P' i)) le_rfl ht (Cover.loc hx (delay_t hζ (hp.comp h') hb' (by norm_num)))) (by simp))
    refine (paintT hb he (Nat.lt_succ_self j) (f':=t) hXX).fit (EventuallyEq.refl ..) (fun r hr=>?_); filter_upwards [(hp.eventually (hx.eventually (by simp)))] with i hi; exact ((Act.swell _ (le_refl j)).transit hi).writes r hr
 -- trick contdiff ω eventually? ω=top WithTop ℕ∞, not available? hx analytic.E
 refine ⟨(fun j hj=> (hm j hj).steps j le_rfl), fun j hj=> ?_⟩; let f':=fun i=> delay (f i) j (b i); have hy : H (a-f') (graded (j+1)):= h.stamps _ hj; have hw:= Clock.Meter.close F hx hx₀ (delay_t (fun i hi=> h.steps i (hi.trans hj)|>.weak le_rfl) hp hb (by norm_num)) hy
 apply (hw.add ((hm _ hj).stamps _ le_rfl)).eq_mem; exact Eventually.of_forall fun i=>by dsimp only [Function.comp_apply,Q]; abel
-- Polynomials with constant F0_t: use separately. Test.
end TaylorCap
end YM.AllOrder.Catch
