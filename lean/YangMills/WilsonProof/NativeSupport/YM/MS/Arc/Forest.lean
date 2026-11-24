import YangMills.WilsonProof.NativeSupport.YM.MS.Arc.R1
/-!
# Embed ordinary momentum dimensions first

Separate rapid half-plane. Program recurs after this operation.
 Also quote ordinary Cart∫, proof flexible splitting E× (F× G) etc. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Arc
open Function Filter Set Finset MeasureTheory Real
open scoped Topology ContDiff Interval
open ContinuousLinearMap
variable {I E F G H: Type}[NormedAddCommGroup E][NormedSpace ℝ E]
 [NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup G][NormedSpace ℝ G]
 [NormedAddCommGroup H][NormedSpace ℝ H]
variable {z:UScale I}{a:I→ℝ} {u:I→(E×F)×G→H}
-- associator
private def A : (E×F×G) →L[ℝ] (E×F)×G:= ((fst ℝ E (F×G)).prod ((fst ℝ F G) ∘L snd ℝ E (F×G))).prod ((snd ℝ F G) ∘L snd ℝ E (F×G))
lemma deep (h:quiet z u a)(k j v:ℕ):∃ C:ℝ,0<C∧∃ b:ℕ,∀ i (p:E)(q:F)(x:G),
 ‖iteratedFDeriv ℝ k ((u i)∘ A (E:=E) (F:=F) (G:=G)) (p,q,x)‖*(1+‖p‖)^j*(1+‖q‖)^v ≤ C*((1+|z i|)*(1+‖x‖))^b*a i:= by
   obtain ⟨C,hC,b,hb⟩ := Q.man h k (j+v); let T := (A (E:=E) (F:=F) (G:=G)); have hV:T=A:=rfl
   refine ⟨(1+‖T‖^k)*C,mul_pos (by positivity) hC,b,fun i p q x=>?_⟩
   let D:= (p,q,x); let X := ‖iteratedFDeriv ℝ k (u i) ((p,q),x)‖; let L:= ‖iteratedFDeriv ℝ k ((u i)∘ T) D‖; let M:=1+‖T‖^k; let U:= ((1+|z i|)*(1+‖x‖))
   have hx:X≥0:= norm_nonneg _; have hm : 0≤ M:= by unfold M; positivity
   have hv : L≤M*X:= by unfold L; rw [T.iteratedFDeriv_comp_right (h.smooth i) D (by exact_mod_cast le_top)]; apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..); simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_comm _ (‖T‖^ k)]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hx -- defeq T D
   have H : (1+‖p‖)^j*(1+‖q‖)^v ≤ (1+‖(p,q)‖)^(j+v):= by rw [pow_add,Prod.norm_def]; gcongr <;> simp
   calc
     L*(1+‖p‖)^j*(1+‖q‖)^v = L*((1+‖p‖)^j*(1+‖q‖)^v) := by ring
     _ ≤ M*(X*(1+‖(p,q)‖)^(j+v)) := by rw [← mul_assoc M]; exact mul_le_mul hv H (by positivity) (by positivity)
     _ ≤ M*(C*U^b*a i) := mul_le_mul_of_nonneg_left (hb i (p,q) x) hm
     _ = _ := by unfold U M; ring -- U unfold
lemma Q.trees (h:quiet z u a) : quiet z (fun i=> u i ∘ A (E:=E) (F:=F) (G:=G)) a:= by
   apply Q.fromM (fun i=> (h.smooth i).comp A.contDiff); intro j k; obtain ⟨C,hC,b,hb⟩:=deep h j k 0; refine ⟨C,hC,b,fun i p q=>?_⟩; obtain ⟨q,x⟩:=q; specialize hb i p q x; rw [pow_zero,mul_one] at hb; refine hb.trans ?_; rw [Prod.norm_def]; gcongr; · exact Q.nonneg h i
   simp
variable [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E](μ:Measure E)[μ.IsAddHaarMeasure]
lemma Q.Gmajor (h:quiet z u a) (i:I): Majorant μ (fun p:E=> fun x:F×G=> u i ((p,x.1),x.2)):= (Q.trees h).major (Reserve.cover (μ:=μ) (Module.finrank ℝ E+1) (by omega)) i
-- Region integration preserves rest
variable [CompleteSpace H]
lemma Q.Gquiet (h:quiet z u a): quiet z (fun i (x:F × G)=> ∫ p, u i ((p,x.1),x.2) ∂μ) a:= by -- binder fun i x:F×G ambiguity
   apply Q.fromM (fun i=> (Q.Gmajor μ h i).contDiff); intro j k; let N:=Module.finrank ℝ E+1; let Lp (p:E):=((1+‖p‖)^N)⁻¹; obtain ⟨C,hC,b,hb⟩:=deep h j N k
   let D:=max 1 (∫ p:E,Lp p ∂μ); have hP (i:I): Integrable Lp μ:= by have hm := Reserve.dustInteg (S:=path z) (μ:=μ) (i:=i) N (by unfold N; omega); convert hm using 1; unfold Lp; ext x; simp [Scale.dust,Scale.weight]
   refine ⟨C*D,mul_pos hC (lt_max_of_lt_left zero_lt_one),b,fun i p q=>?_⟩
   let W:=(1+‖p‖)^k; let Hx:=((1+|z i|)*(1+‖q‖))^b*a i; let U:F×G:=(p,q); have hw: W>0:= by unfold W; positivity
   have ht: 0≤Hx:= by have ht:=Q.nonneg h i; unfold Hx; positivity
   let T: E→(F×G)→H:= fun x q=>u i ((x,q.1),q.2); rw [(Q.Gmajor μ h i).identity]; change ‖∫ x, iteratedFDeriv ℝ j (T x) U ∂μ‖*W≤ C*D*_ *a i
   have he': (C*D)*((1+|z i|)*(1+‖q‖))^b*a i=C*Hx*D:= by unfold Hx; ring
   rw [he']; apply (le_div_iff₀ hw).mp; refine (norm_integral_le_of_norm_le ((hP i).const_mul (C*Hx/W)) (Eventually.of_forall fun x=>?_)).trans ?_
   · have he:= norm_extDer ((h.smooth i).comp A.contDiff) x U j; apply he.trans
     have hz : (1+‖x‖)^N>0:= by positivity
     obtain hY:= hb i x p q; unfold Lp; dsimp only [U]; rw [← div_eq_mul_inv,le_div_iff₀ hz,le_div_iff₀ hw]; exact hY.trans_eq (mul_assoc ..)
   rw [integral_const_mul]; unfold D; rw [div_mul_eq_mul_div]; gcongr; exact le_max_right ..
end YM.MS.Arc
