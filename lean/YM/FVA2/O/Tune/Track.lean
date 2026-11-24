import YM.FVA2.O.Tune.Glass
/-!
# Velocity for Taylor-OPE recognition
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Tune
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake
open scoped Topology ContDiff
variable {E F I U:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
variable {f H:ℝ→ E→F} {X Y:I→ ℝ→ E→F}{s:ℝ}
private def unitM : Measure ℝ:= volume.restrict (Set.Icc 0 1)
private instance : IsFiniteMeasure unitM:= ⟨by rw [unitM, Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
variable [CompleteSpace F][FiniteDimensional ℝ E]
omit [CompleteSpace F] in
private lemma month (h:Gym f)(hx:∀ p:E,Continuous (fun i=> f i p)) (r:ℝ) : Majorant unitM (fun z x=> f (r*z) x) := by
    refine ⟨ Eventually.of_forall (fun z=> h.sm _), fun j x=> (( h.jet_c hx x j ).comp (show Continuous (fun z:ℝ=> r*z) by fun_prop)).aestronglyMeasurable, fun j p=>?_⟩; obtain ⟨K,hK,hv⟩:= h.day ‖r‖ 1 (norm_nonneg _) zero_le_one p j; refine ⟨ closedBall p 1, closedBall_mem_nhds p zero_lt_one, fun _=> K,integrable_const ..,(ae_restrict_mem measurableSet_Icc).mono fun i hi=> hv _ ?_⟩; apply abs_le.mp; rw [abs_mul, abs_of_nonneg hi.1]; exact mul_le_of_le_one_right (abs_nonneg _) hi.2
lemma Gym.proceeds (h:Gym f)(hp:Gym H)(he:∀ p:E, Continuous (fun t:ℝ=> H t p))(hv:∀ i x,HasDerivAt (fun i=> f i x) (H i x) i)(i:ℝ)(j:ℕ)(x:E): HasDerivAt (fun p:ℝ=>iteratedFDeriv ℝ j (f p) x) (iteratedFDeriv ℝ j (H i) x) i := by
    let V (p:ℝ) (x:E):= p • ∫ r,H (p*r) x∂unitM; have hP (p:ℝ) : ContDiff ℝ ∞ (V p):= (month hp he p).contDiff.const_smul _
    have hh (p:ℝ)(x:E): V p x= desk (Function.uncurry H) (p,x) := ( table (Function.uncurry H) x p ).symm
    have hX : f=fun p=> (let a:=V p;a)+f 0:= by
       funext p x; change f p x= V p x+_; rw [hh]; exact eq_add_of_sub_eq (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y hy=> hv y x) ((he x).intervalIntegrable 0 p)).symm
    have hi p: iteratedFDeriv ℝ j (f p) x= (∫ r:ℝ in 0..p, iteratedFDeriv ℝ j (H r) x)+iteratedFDeriv ℝ j (f 0) x:= by
       calc
         _ = iteratedFDeriv ℝ j (V p) x+iteratedFDeriv ℝ j (f 0) x:= by conv_lhs=>rw [hX]; rw [iteratedFDeriv_add ((hP p).of_le (by exact_mod_cast le_top)) ((h.sm 0).of_le (by exact_mod_cast le_top)),Pi.add_apply] -- need conv scope
         _ = _ := by
            unfold V; rw [iteratedFDeriv_const_smul_apply' ((month hp he p).contDiff.contDiffAt.of_le (by exact_mod_cast le_top)),(month hp he p).identity]; congr 1; exact (table ( T:=fun y:ℝ×E=> iteratedFDeriv ℝ j (H y.1) x ) x p).symm
    convert! ((Heat.hfun (hp.jet_c he x j) i).add_const (iteratedFDeriv ℝ j (f 0) x)) using 1; funext p; exact hi p
section chart
variable {G:Gauge}{F H:Glade G I}{i:I}
omit [FiniteDimensional ℝ E] in
lemma booking (hF:Warm F false)(i:I)(l:Wire (BH G) E QP): Gym (fun t x=> F i t (sail l x)):= by
    refine ⟨fun t ht=>?_⟩; have hw:= hF.cost i t ht E l (fun p=>Bool.noConfusion p) (fun p=> Bool.noConfusion p); simp only [Cape, cw, one_zpow,one_mul] at hw; exact hw
omit [FiniteDimensional ℝ E] in
lemma Track_w (h:Warm F false)(hp: Warm H false)(hv:Velocity F H)(i:I)(w:Wire (BH G) E QP)(j:ℕ)(t:ℝ)(x:E): HasDerivAt (fun t:ℝ=> iteratedFDeriv ℝ j (fun p=> F i t (sail w p)) x) (iteratedFDeriv ℝ j (fun p=> H i t (sail w p)) x) t:= by
    obtain ⟨B,iA,iN,hB,v,L,hp',he⟩:= Latch.canon w (b:=false) (fun p=>Bool.noConfusion p); simp_rw [hp']; let U := ContinuousMultilinearMap.compContinuousLinearMapL (F:=ℂ) (fun _: Fin j=> L); let f:=fun t:ℝ=> fieldVal (F i t) v; let g:=fun t:ℝ=> fieldVal (H i t) v
    change HasDerivAt (fun t:ℝ=> iteratedFDeriv ℝ j (f t ∘ L) x ) (iteratedFDeriv ℝ j (g t ∘ L) x) t; have hf: Gym f:= booking h i v; have hg: Gym g:= booking hp i v
    simp_rw [ L.iteratedFDeriv_comp_right (hf.sm _) _ (by exact_mod_cast le_top : ((j:ℕ∞):WithTop ℕ∞)≤ ↑(⊤:ℕ∞)), L.iteratedFDeriv_comp_right (hg.sm t) _ (by exact_mod_cast le_top)]
    exact U.hasFDerivAt.comp_hasDerivAt t (hf.proceeds hg (fun q=> hp.walk i (sail v q) (fun q=>Bool.noConfusion q)) (fun t q=> hv i t _) t j _)
omit [FiniteDimensional ℝ E] in
lemma Track_now (T:IntervalFamily I)(h:Warm F false)(hp:Warm H false)(hv:Velocity F H)(w:Wire (BH G) E QP)(j:ℕ): T.Along (fun i p=> fieldVal (F i p) w) (fun i p=> fieldVal (H i p) w ) j:= fun i t _ p=> (Track_w h hp hv i w j t p).hasDerivWithinAt
end chart
end YM.FVA2.O.Tune
