import YM.OPE.Compatible.Straws.Golf
/-!
# Gauged parameterized fiber integration. No borrowed hypotheses
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal Matrix.Norms.Frobenius
open PertExtension Series GaussianScore Asymptotics Precision Cascade Cascade.Pilot Arc Adhesion Flock Coin
open Radial ScriptJ JetS
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E] [BorelSpace E]
variable {D I:Type}[Fintype D][Fintype I]{G:Gauge}
local notation "Lf" => Tested.germ
local notation "Y!" => Keys G I
local notation "K!" => Keys G (D ⊕ I)
local notation "U!" => Keys G D
local notation "BL" => prL (Equiv.refl (D ⊕ I)) G
local notation "BR" => prR (Equiv.refl (D ⊕ I)) G
namespace Fiber
open Stranded Shift Glass
section oL
variable {F:Type}[NormedAddCommGroup F][NormedSpace ℝ F]
omit [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] in
lemma compStar (v:E→F)(hv:ContDiffAt ℝ ∞ v 0)(ht:v 0=0)(f:F→ℝ)(h: Radial.Stationary f): Radial.Stationary (f∘v):=by
     have he : fderiv ℝ f 0=0:=by ext x; have hp:=h.base1 x; unfold jet at hp; simpa only [iteratedFDeriv_one_apply,Nat.factorial_one,Nat.cast_one,inv_one,one_mul,_root_.zero_apply] using hp
     refine ⟨( (show ContDiffAt ℝ ∞ f (v 0) from ht.symm ▸ h.smooth)).comp _ hv,?_,fun i=>?_⟩
     · rw [Function.comp_apply,ht,h.base0]
     unfold jet; rw [iteratedFDeriv_one_apply,fderiv_comp _ (ht.symm ▸ h.smooth.differentiableAt (by simp)) (hv.differentiableAt (by simp)),ht,he]; simp
omit [MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E] in
lemma pileStar (f g:E→ℝ)(h:Radial.Stationary f)(hg:Radial.Stationary g): Radial.Stationary (f+g):=by refine ⟨h.smooth.add hg.smooth,by rw [Pi.add_apply,h.base0,hg.base0,zero_add],fun i=>?_⟩; rw [show jet _ _ _= jet f 1 i+jet g 1 i from (by unfold jet; rw [iteratedFDeriv_add_apply (h.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) (hg.smooth.of_le (WithTop.coe_le_coe.mpr le_top)),_root_.add_apply,mul_add]),h.base1,hg.base1,zero_add]
end oL
variable (F:Fiber E G I)(X:Path E G D)
local notation "uΘ" k => armour U! k
abbrev remote (k:ℝ):K!→ℝ:= (F.f ∘ Spine X)+(armour U! k ∘ BL)
omit [BorelSpace E] in
lemma Zena (k:ℝ): Radial.Stationary (remote F X k):= pileStar _ _ (compStar _ (SpineJet X) (SpineBlew X) _ F.H) (compStar _ (BL).contDiff.contDiffAt (BL).map_zero _ (zAtom k))
omit [BorelSpace E] [FiniteDimensional ℝ E] in
lemma SpinD (w:K!): fderiv ℝ (Spine X) 0 w= (X.deck ((BL) w),(BR) w):=by
       let U:K!→E×Y!:= Spine X; have hp : ContDiffAt ℝ ∞ X.A (BL 0):= ( (BL).map_zero).symm ▸ X.hA; have hh:= (((hp.differentiableAt (by simp)).hasFDerivAt.comp 0 ((BL).hasFDerivAt)).prodMk ((BR).hasFDerivAt (x:=0))); rw [show fderiv ℝ U 0= _ from hh.fderiv]; simp only [map_zero];rfl
omit [BorelSpace E] in
lemma ZLevel (k:ℝ)(u:U!)(y:Y!): jet (remote F X k) 2 (camp F X (u,y))= u_q F (X.deck u)+ F.Q.P y y/2+armour U! k u:=by
     let q:= camp F X (u,y); let f:=F.f ∘ Spine (I:=I) X; let g:=armour U! k ∘ BL; have ht: ContDiffAt ℝ ∞ f 0:= (compStar _ (SpineJet X) (SpineBlew X) _ F.H).smooth; have hx:ContDiffAt ℝ ∞ g 0:= ((compStar _ (BL).contDiff.contDiffAt ((BL).map_zero) _ (zAtom k)).smooth); change jet (f+g) 2 q=_; rw [show jet (f+g) 2 q= jet f 2 q+jet g 2 q from (by unfold jet; rw [iteratedFDeriv_add_apply (ht.of_le (WithTop.coe_le_coe.mpr le_top)) (hx.of_le (WithTop.coe_le_coe.mpr le_top)),_root_.add_apply,mul_add]),show jet f 2 q= jet F.f 2 (fderiv ℝ (Spine X) 0 q) from (by unfold jet; unfold f; rw [Glass.slopeJet _ (SpineJet X) (SpineBlew X) F.f F.H]; rfl), show jet g 2 q= jet (armour U! k) 2 (BL q) from (by unfold jet;unfold g; rw [Next.Foundations.jets_linear (BL) ((zAtom k).smooth.of_le (WithTop.coe_le_coe.mpr le_top))];rfl),SpinD,(rig F X (u,y)).1,(rig F X (u,y)).2,zCash]; exact congr_arg (fun x=>x+armour U! k _) (F.split ..)
omit [BorelSpace E] in
lemma restores : ∀ᶠ b in atTop, Nonempty (F.SeriesUp X (armour U! b)):=by
      let f:= F.u_q; let A: U!→L[ℝ] (E×Y!):= (fderiv ℝ X.A 0).prod (F.M ∘L fderiv ℝ X.A 0); let CML:=iteratedFDeriv ℝ 2 F.f 0; let k:ℝ:= (Nat.factorial 2:ℝ)⁻¹ *‖CML‖*‖A‖^2; have hk:0≤ k:=by unfold k; positivity
      have hh(x:U!):‖f (X.deck x)‖≤ k*‖x‖^2:=by
          change ‖ _⁻¹*CML (fun _:Fin 2=>A x)‖≤ _; rw [norm_mul, Real.norm_eq_abs ((Nat.factorial 2:ℝ)⁻¹),abs_of_nonneg (by positivity)]; apply le_trans (mul_le_mul_of_nonneg_left (CML.le_opNorm _) (by positivity)); rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; unfold k;rw [mul_assoc,mul_assoc,← mul_pow]; gcongr; exact A.le_opNorm x
      have hZ: Measurable (Spine (I:=I) X):= (X.hf.comp (BL).continuous.measurable).prodMk (BR).continuous.measurable
      obtain ⟨s,hs,hU⟩:= zCosts (E:=U!); filter_upwards [eventually_ge_atTop ((k+1)/s)] with t ht
      let p:=armour U! t; let g:=remote F X t; let W:= camp F X
      have hr(x:U!):‖x‖^2 ≤ jet g 2 (W (x,0)):=by
          rw [ZLevel, _root_.map_zero,zero_div,add_zero]; have hx:= hh x; rw [Real.norm_eq_abs] at hx; have hl: (k+1)*‖x‖^2 ≤ p x:=by
              have he:armour U! t x=t*armour U! 1 x:=by unfold armour; rw [one_mul]
              calc
                 _ ≤ (t*s)*‖x‖^2:= mul_le_mul_of_nonneg_right ((div_le_iff₀ hs).mp ht) (sq_nonneg _)
                 _ ≤ t*armour U! 1 x:=by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hU x) (le_trans (by positivity) ht)
                 _ = _ := he.symm
          change _≤ f (X.deck x)+p x; linarith only [abs_le.mp hx |>.1,hl]
      have hy:Cel g:=by
           apply Radial.quadratic_min; intro v hv; obtain ⟨⟨x,y⟩,rfl⟩:= W.surjective v; obtain ⟨c,hc,H⟩:= F.Q.slope; have hh : jet g 2 (W (x,y))= jet g 2 (W (x,0))+ F.Q.P y y/2:=by rw [show jet g 2 _= _ from ZLevel F X t x y,show jet g 2 _=_ from ZLevel F X t x 0,_root_.map_zero];ring
           rw [hh]; by_cases hp:x=0
           · have h:y≠0:=fun he=>hv (by rw [hp,he,show ((0:U!),(0:Y!))=0 from rfl,map_zero]); exact add_pos_of_nonneg_of_pos ((sq_nonneg _).trans (hr x)) ((mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr h))).trans_le (H y))
           exact add_pos_of_pos_of_nonneg ((sq_pos_of_pos (norm_pos_iff.mpr hp)).trans_le (hr x)) ((mul_nonneg hc.le (sq_nonneg _)).trans (H y))
      let C:Lid G (D⊕I):=⟨g,Zena F X t,(F.C.comp hZ).add (((zBom t).smooth.continuous.measurable).comp (BL).continuous.measurable),hy,F.w ∘ Spine X,by rw [Function.comp_apply,SpineBlew]; exact F.hw, ((show ContDiffAt ℝ ∞ F.w (Spine X (0:K!)) from (SpineBlew X).symm ▸ F.HC)).comp _ (SpineJet X),F.hv.comp hZ⟩
      let w: U!→L[ℝ] K!:= W.toContinuousLinearMap ∘L ContinuousLinearMap.inl ..; have hv(x:U!):jet (g ∘ w) 2 x= jet g 2 (W (x,0)):=by unfold jet; rw [Next.Foundations.jets_linear _ ((Zena F X t).smooth.of_le (WithTop.coe_le_coe.mpr le_top))];rfl
      let Q:Lid G D:=⟨g ∘ w,compStar _ w.contDiff.contDiffAt w.map_zero g C.F,C.fmeas.comp w.continuous.measurable,⟨1,one_pos,fun i=>by rw [one_mul,hv]; exact hr i⟩,1,one_pos,contDiffAt_const,measurable_const⟩
      refine ⟨⟨C,penon Q,rfl,rfl,fun v y=>?_,zAtom _⟩⟩; rw [← penon_shape, show jet C.f 2 _= _ from ZLevel F X _ v y,show jet Q.f 2 _=_ from hv v,ZLevel]; simp only [map_zero]; ring
end Fiber
end YM.OPE.Libra
