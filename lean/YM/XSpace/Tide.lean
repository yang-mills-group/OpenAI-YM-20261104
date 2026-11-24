import YM.XSpace.Compat.Ride
import YM.XSpace.Sonar

/-! # Power-counted waveforms on the infinite cover for first-order amplitudes

Including any fixed translated observation, its exact smooth off-zero limit, and all
under native differences. Piece of lattice→continuum convergence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Tide
open YM.XSpace.Compat.KP
open Function Filter Set Trace Scale Lattice Sail Litter Further.FreeCovariance.KP Maxwell Maxwell.Free Analysis Tensor
open scoped Topology BigOperators ContDiff
variable {F F':Type*}[NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup F'][NormedSpace ℝ F']
variable {ι:Type} {L:Filter ι} {x:ι→Cover} {a:ι→ℝ}

def Glow (k:ℕ)(p:Cover→F): Prop:=∀ l:List Axis, ∃ C:ℝ,0≤C∧∀ x:Cover, ‖crack l p x‖≤ C*carry (k+l.length) (reach x)
def Pays (k:ℕ)(p:Cover→F)(f:E4→F)(L:Filter ι)(a:ι→ℝ)(x:ι→Cover)(u:E4): Prop:=∀ l:List Axis,Tendsto (fun i=> (a i)⁻¹^(k+l.length) • crack l p (x i)) L (𝓝 (ride l f u))
structure Beam (k:ℕ)(p:Cover→F)(f:E4→F): Prop where
  value (x:E4):x≠0→ContDiffAt ℝ ∞ f x
  glows : Glow k p
  beams {ι: Type}{L:Filter ι}{a:ι→ℝ}{x:ι→Cover}{u:E4}(hp:∀ᶠ i in L,0<a i)(h:Tendsto a L (𝓝 0))(hx:Tendsto (fun i=> a i • rcast (x i)) L (𝓝 u))(hu:u≠0): Pays k p f L a x u

lemma phase_cost {r m:ℕ}(n k:ℕ)(h:k≤r+m) : carry n r ≤ (1+(m:ℝ))^n * carry n k :=by
  unfold carry; rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); change Outline.saving r ≤ _; apply Outline.saving_fee h
lemma peak_move (p:Cover→F)(x y:Cover)(l:List Axis):crack l (sweep y p) x=crack l p (y+x):=by
  induction l generalizing p with | nil=>rfl | cons i l ih=> rw [snack,snack,show Δf i (sweep y p)= _ from tooth_sweep y i p]; exact ih (teeth i p)
lemma creek (l:List Axis)(C:F→ₗ[ℝ] F')(p: Cover→F) (x:Cover) : crack l (C ∘ p) x=C (crack l p x):=by
  induction l generalizing x with | nil=>rfl | cons i l ih=> change crack l _ _-crack l _ _=C (_-_); rw [ih,ih,map_sub]
lemma ride_linear {f:E4→F} (u:F→L[ℝ]F') (l:List Axis)(x:E4)(h:ContDiffAt ℝ ∞ f x) : ride l (u ∘ f) x=u (ride l f x):=by rw [reports l (f:=u ∘ f) (u.contDiff.contDiffAt.comp x h),reports l h]; rw [u.iteratedFDeriv_comp_left (h.of_le (WithTop.coe_le_coe.mpr le_top)) le_rfl]; rfl

namespace Beam
variable {k:ℕ}{p q:Cover→F}{f g:E4→F}
lemma map (X:Beam k p f) (C:F→L[ℝ] F'): Beam k (C ∘ p) (C ∘ f) :=by
  have he l x:= creek l C.toLinearMap p x
  refine ⟨fun x hx=> C.contDiff.contDiffAt.comp _ (X.value x hx),fun l=>?_,fun hp h hx hu l=> ?_⟩
  · obtain ⟨D,hD,H⟩:=X.glows l; refine ⟨‖C‖*D,by positivity,fun x=>?_⟩; change ‖crack l (C.toLinearMap ∘ _) _‖≤_; rw [he]; exact ((C.le_opNorm _).trans (mul_le_mul_of_nonneg_left (H x) (norm_nonneg _))).trans_eq (mul_assoc ..).symm
  rw [ride_linear C _ _ (X.value _ hu)]; exact (C.continuous.continuousAt.tendsto.comp (X.beams hp h hx hu l)).congr fun i=>by unfold comp; rw [map_smul]; exact congr_arg (_ • ·) (he _ _).symm
lemma step_forth (X:Beam k p f)(i:Axis):Beam (k+1) (Δf i p) (grad i f):=by
  have he(l:List Axis): k+1+l.length=k+(i::l).length:= by simp; omega
  refine ⟨fun x hx=>grad_smooth i (X.value x hx) (by simp),fun l=>?_,fun hp h hx hu l=>?_⟩
  · simpa only [he l,snack] using X.glows (i::l)
  rw [he,← snack]; exact X.beams hp h hx hu (i::l)
lemma moved (X:Beam k p f)(y:Cover):Beam k (sweep y p) f:= by
  refine ⟨X.value,fun l=>?_, fun {ι} {L} {a} {x} {u} hp h hx hu l=>?_⟩
  · obtain ⟨C,hC,H⟩:= X.glows l; let K:=k+l.length; let D:=(1+(reach y:ℝ))^K; refine ⟨C*D,by unfold D; positivity,fun x=>?_⟩; rw [peak_move]; apply le_trans (H _); rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hC; apply phase_cost; rw [← reach_neg y,add_comm y]; exact le_trans (le_of_eq (show reach x=reach (x+y+-y) by rw [add_neg_cancel_right])) (tree ..)
  have ht:= X.beams hp h (x:=fun i=>y+x i) (show Tendsto _ L (𝓝 u) from by simp_rw [Cross.rcast_add, smul_add]; simpa using (h.smul_const (rcast y)).add hx) hu l; simp_rw [peak_move]; exact ht
lemma sub (X:Beam k p f)(Y:Beam k q g): Beam k (p-q) (f-g):= by
  refine ⟨fun x hx=> (X.value x hx).sub (Y.value x hx),fun l=>?_,fun {ι} {L} {a} {x} {u} hp h hx hu l=>?_⟩
  · obtain ⟨C,hC,H⟩:=X.glows l; obtain ⟨D,hD,K⟩:=Y.glows l; refine ⟨C+D,by positivity,fun x=>?_⟩; rw [← peaked,map_sub,Pi.sub_apply,peaked,peaked,add_mul]; exact (norm_sub_le ..).trans (add_le_add (H x) (K x))
  have he := (X.beams hp h hx hu l).sub (Y.beams hp h hx hu l); simp_rw [← peaked,map_sub,Pi.sub_apply,peaked l p,peaked l q,smul_sub, ride_sub l (X.value _ hu) (Y.value _ hu)]; exact he
lemma smul (X:Beam k p f)(v:ℝ): Beam k (v • p) (v • f):=X.map (v • ContinuousLinearMap.id ℝ F)
lemma add (X:Beam k p f)(Y:Beam k q g): Beam k (p+q) (f+g):=by simpa using X.sub (Y.smul (-1))
lemma zero : Beam k (0:Cover→F) 0 := ⟨fun _ _=>contDiffAt_const,fun l=> ⟨0,le_rfl,fun x=> by simp [← peaked]⟩,fun {ι} {L} {a} {x} {u} _ _ _ _ l=> by simp [← peaked,ride_nil,tendsto_const_nhds]⟩
end Beam

lemma riding (l:List Axis): Pole (2+l.length) (ride l Green):=by
  have he(l:List Axis) {k:ℕ}{f:E4→ℝ}(h:Pole k f)(he:2≤k): Pole (k+l.length) (ride l f):=by induction l generalizing k f with | nil=> exact h | cons i l ih=> rw [List.length_cons, add_comm l.length,← Nat.add_assoc]; exact ih (h.step he (basis i)) (by omega)
  exact he l green_pole le_rfl
lemma greenBeam : Beam 2 cover Green:= by
  refine ⟨fun x hx=> freeSmooth hx,fun l=> (covers_decays l).imp (fun c h=> ⟨h.1.le, h.2⟩),fun {ι} {L} {a} {x} {u} hp h hx hu l=>?_⟩
  have ht : 0<‖u‖:=norm_pos_iff.mpr hu
  set k:=2+l.length; let w i:=rcast (x i); let f:=ride l Green; obtain ⟨C,hC,H⟩:= cover_value l; let A i:= ‖a i • w i‖; have he:= hx.norm; let g i:= C*a i*(A i^(k+1))⁻¹
  have hg : Tendsto g L (𝓝 0) := by
    have hx : Tendsto A L (𝓝 ‖u‖):= hx.norm
    simpa [g] using ((Tendsto.const_mul C h).mul ((hx.pow (k+1)).inv₀ (pow_ne_zero _ (ne_of_gt ht))))
  let z (i:ι):= (a i)⁻¹^(2+l.length) • crack l cover (x i); let Y i:= f (a i • w i); have hy:Tendsto Y L (𝓝 (f u)):= (ride_smooth l (freeSmooth hu)).continuousAt.tendsto.comp hx
  have h0: Tendsto (fun i=> z i-Y i) L (𝓝 0):=tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg (z i-Y i)) (?_) hg)
  · have hh:= h0.add hy; rw [zero_add] at hh; exact hh.congr fun i=>sub_add_cancel ..
  filter_upwards [hp,h.eventually (ge_mem_nhds (half_pos ht)),he.eventually (le_mem_nhds (div_two_lt_of_pos ht))] with i hi ha hw; change ‖a i • w i‖ ≥ ‖u‖ / 2 at hw; set b:= a i; let N:= ‖w i‖; have hh: A i=b*N:= by unfold A; rw [norm_smul,Real.norm_of_nonneg hi.le]
  have hw':1≤N:= by change b≤_ at ha; change A i≥_ at hw; rw [hh] at hw; nlinarith
  have hn : 0<N:=lt_of_lt_of_le zero_lt_one hw'
  unfold Y z; change ‖b⁻¹^k * _ - f (b • w i)‖ ≤ _; rw [(show f (b • w i)= b⁻¹^k*f (w i) from (riding l).degree b hi (w i) (norm_pos_iff.mp hn)),← mul_sub,norm_mul]; apply (mul_le_mul_of_nonneg_left (H _ hw') (norm_nonneg (b⁻¹^k))).trans_eq; unfold g; rw [hh, Real.norm_of_nonneg (pow_nonneg (inv_nonneg.mpr (show 0≤b from hi.le)) _)]; rw [show 3+l.length=k+1 by omega]; change b⁻¹^k*(C*(N^(k+1))⁻¹)= C*b*((b*N)^(k+1))⁻¹; rw [inv_pow]; field_simp; rw [mul_pow]; ring
end YM.XSpace.Tide
