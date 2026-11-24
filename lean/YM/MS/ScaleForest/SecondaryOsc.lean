import YM.MS.ScaleForest.WirePinned
import YM.MS.Fiddle.Tow
/-!
# Uniform decay on the remaining continuation axis after q-Fourier transforms

In the prescribed order of integration off the pin-contact locus. Keep rapid
decay in the loop-axis radius, with derivatives. This allows later
continuation in a wide shell. Use at bounded complex dimension and all
continuation-sector tests. Translation for finite differencing is *only* in
the unpruned primary components. Desired exponents are given as reciprocal
wavelength powers — do not need Gaussian-like analyticity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Arc Rock Path Spin Arts Osc Fiddle
open scoped Topology ContDiff
variable {I E F J:Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
   [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup J] [NormedSpace ℝ J]

variable {f : I→(F×J)×E→ℂ} {g : I→ F→ℂ} {a b z : I→ℝ}
variable [MeasurableSpace F][BorelSpace F] [FiniteDimensional ℝ F]
variable (μ:Measure F)[μ.IsAddHaarMeasure] (hf : quiet z f a) (hg : ∀ i, Peak (g i))

def stripeFourier (μ : Measure F) (g : F→ℂ) (f : (F×J)×E→ℂ) : J×E→ℂ := fun p=> ∫ q,g q*f ((q,p.1),p.2) ∂μ

include hf hg

private def fibre (t : I) (q : F) (p : J×E) := f t ((q,p.1),p.2)

theorem stripe_major (i:I) : Majorant μ fun q:F=>fun p:J×E=> g i q*f i ((q,p.1),p.2):= Vmajor (hg i) (Arc.Q.Gmajor μ hf i)

theorem stripe_conserve : quiet z (fun i=> stripeFourier μ (g i) (f i)) a:= by
   apply Q.fromM (fun i=> (stripe_major μ hf hg i).contDiff); intro j k
   let N:= Module.finrank ℝ F+1; let δ(q:F):=((1+‖q‖)^N)⁻¹
   obtain ⟨C,hC,l,hb⟩:=Arc.deep hf j N k
   let M:=max 1 (∫ q:F,δ q ∂μ);
   have hδ(i:I): Integrable δ μ:= by
     convert Reserve.dustInteg (S:=Arc.path z) (μ:=μ) i N (by unfold N; omega) using 1; unfold δ; ext q; simp [Scale.dust,Scale.weight]
   refine ⟨C*M,mul_pos hC (lt_max_of_lt_left zero_lt_one),l,fun i p x=>?_⟩
   let T : J×E:= (p,x); let W:=(1+‖p‖)^k; let U:=((1+|z i|)*(1+‖x‖))^l*a i; have hw :W>0:= by unfold W; positivity
   have hu : 0≤ U:= by have hh:=Q.nonneg hf i; unfold U; positivity
   let Y(q:F)(p:J×E):= g i q * f i ((q,p.1),p.2)
   rw [ (stripe_major μ hf hg i).identity ]; change ‖∫ q, iteratedFDeriv ℝ j (Y q) T ∂μ‖ * W ≤ _
   rw [show (C*M)*((1+|z i|)*(1+‖x‖))^l*a i=C*U*M from by unfold U; ring]
   apply (le_div_iff₀ hw).mp; refine (norm_integral_le_of_norm_le ((hδ i).const_mul (C*U/W)) (Eventually.of_forall fun q=>?_)).trans ?_
   · unfold Y; let L: (F×J×E) →L[ℝ] ((F×J)×E):= ((ContinuousLinearMap.fst ℝ _ _).prod ((ContinuousLinearMap.fst ℝ J E) ∘L ContinuousLinearMap.snd ℝ F (J×E))).prod ((ContinuousLinearMap.snd ℝ J E) ∘L ContinuousLinearMap.snd ℝ F (J×E))
     let m:= fun p:J×E => f i ((q,p.1),p.2); have ht: ContDiff ℝ ∞ m:= (hf.smooth i).comp (f:=fun p:J×E=>((q,p.1),p.2)) (by fun_prop)
     rw [show iteratedFDeriv ℝ j (fun p=>g i q * m p) T=g i q • iteratedFDeriv ℝ j m T from iteratedFDeriv_const_smul_apply (a:=g i q) (ht.contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul]; refine (mul_le_of_le_one_left (norm_nonneg _) ((hg i).pays _)).trans ((norm_extDer ((hf.smooth i).comp L.contDiff) q T j).trans ?_)
     obtain hx:= hb i q p x; unfold δ; rw [← div_eq_mul_inv, le_div_iff₀ (by positivity),le_div_iff₀ hw]; exact hx.trans_eq (mul_assoc ..)
   rw [integral_const_mul]; unfold M; rw [div_mul_eq_mul_div]; gcongr; exact le_max_right ..

-- finite difference costs (frequencies already in log-root shell)
variable {H : I→F} {T S : ℝ}
   (h : ∀ i, ‖H i‖ ≤ T) (ht : 0≤T)
   (hh : ∀ i q, g i (q - H i) = -(g i q))
   (he : ∀ i, ‖H i‖ ≤ S*b i) (hw : 0 < S)
include h ht hh

def shifted (H:I→F) (f:I→(F×J)×E→ℂ):= Osc.shift (fun i=> (H i,(0:J))) f

theorem stripe_step (i:I) :
    stripeFourier μ (g i) (f i) =(2:ℂ)⁻¹ • stripeFourier μ (g i) (shifted H f i):= by
   let V:F→ℂ:= g i; funext p
   let f' (i:I) (q:F×J×E) := f i ((q.1,q.2.1),q.2.2)
   have hp (i) (q:F×J×E) : (Osc.shift H f' i q) = shifted H f i ((q.1,q.2.1),q.2.2):= by simp [f',shifted, Osc.shift];
   have ht' : glob (Arc.path z) (fun _=>μ) (Module.finrank ℝ F+1):= Reserve.cover _ (by omega)
   have h0:= windCost (S:=Arc.path z) (V:=fun _=>-1) (f:=f') hg ht' (Q.trees hf)
      (fun i q=> by rw [hh]; ring ) (fun i=> by simpa only [cheap_length,one_mul] using h i) ht
      (fun i=> measurePreserving_add_left μ _) i p
   dsimp only [waveInt, f'] at h0 -- avoid unfolding f'
   change _= ∫ (q:F), g i q * Osc.shift H f' i (q,p) ∂μ at h0
   simp_rw [hp] at h0
   unfold stripeFourier
   rw [show ∫ (q:F), g i q * f i ((q,p.1),p.2) ∂μ= (∫ (q:F), g i q * f' i (q,p) ∂μ) from rfl, Pi.smul_apply,smul_eq_mul,← h0];
   unfold f'; dsimp only; ring

include he hw

theorem amplified (k : ℕ) : quiet z (fun i=> stripeFourier μ (g i) (f i)) (fun i=> a i * b i^k) := by
   induction k generalizing a f with
   | zero=> simpa using stripe_conserve μ hf hg
   | succ k ih=>
      let V:= Arc.path z
      have hv : quiet z (shifted H f) (fun i=> a i*b i) := by
        apply Rapid.monotone (step (z:=V) (T:=fun i=> (H i, (0:J))) hf (fun i=> by simp [V,h i]) ht)
        refine ⟨ S,hw,0,fun i p hp=>?_ ⟩
        have h_a:= Q.nonneg hf i; have ht':= h i; obtain he':= he i; simp only [ V,cheap_length,Prod.norm_mk,_root_.norm_zero,max_eq_left (norm_nonneg _),one_mul,mul_one,pow_zero]; nlinarith [ mul_le_mul_of_nonneg_left he' h_a]
      simp_rw [stripe_step μ hf hg h ht hh];
      convert (ih hv).L (ContinuousLinearMap.mul ℝ ℂ (2:ℂ)⁻¹) using 1
      · rfl
      funext i; rw [pow_succ]; ring

end YM.MS.ScaleForest
