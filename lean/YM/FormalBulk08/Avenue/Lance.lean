import YM.FormalBulk08.Avenue.Elder
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Avenue
open Filter Set Metric MeasureTheory Function Lattice Laurent Bloch Exterior Precision RG Next.Free
open Stationary
open scoped Topology ENNReal BigOperators Classical ContDiff Matrix
open scoped Matrix.Norms.Frobenius
open Wilson
variable {n:Side}
open MSbar.Tree.Resolvent
variable {j:ℕ}{k:ℝ}
open Flat UVExtension.Free
variable {G:Gauge}
open Reef Mesa Gorge

variable {D l r:ℕ}
open Kemp Pose Dawn Spigot Orb Wick Series Jets MeasureTheory Lotus Shore Lava Rift
open Grail
-- exact Kalm & cream for any test mark at leading
open City PowerSeries
open Roof Wine Source Source.Drops Labels
variable {o:Loc G 1} {d:ℕ}
open Trellis Aster Dove Quire Clover Elm North
open Dove.Lab
variable {I:Type}{K:KernelChoices}{W:Lab G K I}
variable (s:Signed)
lemma mon_twist (p:Site n): rolls (mon (s.act p)) (s.act (mon p)):= by
   apply rolls_of_mode; intro x
   obtain ⟨y,hy⟩:=s.actEquiv.surjective x
   change s.act y=x at hy; rw [←hy, Stationary.act_phase,←cell_wrap, ←cell_wrap, ←wrap_signed, Stationary.mirror_cell]
lemma buck_twist (p:Site n)(k:ℝ)(v:Train j)(i a:Axis) : buckle k v (mon (s.act p)) (coord (s.perm i)) (coord (s.perm a))=buckle k v (mon p) (coord i) (coord a):= by
   by_cases hp:p=0; subst p; simp only [Signed.act_zero,mon_zero,buckle,↓reduceIte]; rfl
   have hz:s.act p≠0:= fun he=> hp (s.actEquiv.injective (he.trans (map_zero (Signed.actEquiv s)).symm))
   unfold buckle;rw [if_neg (mon_peak _ hz),if_neg (mon_peak _ hp)]; simp only [fieldD,mask_value,scaleD_one,coord_iff,s.perm.injective.eq_iff]; by_cases hm:i=a; swap; · rw [if_neg hm,if_neg hm]
   rw [if_pos hm,if_pos hm]; obtain ⟨x,h⟩:=mon_twist s p; have he:=Train.D_signed k v i s (mon p); rw [h, Train.D_stable] at he; simpa only [show ∀ i,axisEquiv.symm (coord i)=i from fun i=> axisEquiv.symm_apply_apply i] using he
lemma ink_curve (k:ℝ)(v:Train j)(x y t : Site n)(a:Axis) : carnel k v n (x,coord a) (y,coord a)= carnel k v n (s.act x+t,coord (s.perm a)) (s.act y+t,coord (s.perm a)) := by
   unfold carnel realOf; simp_rw [Matrix.map_apply,spectral_apply,add_sub_add_right_eq_sub]; congr 2;
   refine Fintype.sum_equiv s.actEquiv.toEquiv _ _ fun i=>?_ ; change cell _ _ * _ = cell (s.act _) _ * buckle k v (mon (s.act i)) (coord (s.perm a)) (coord (s.perm a)); rw [buck_twist, ← show ∀ (x y:Site n), s.act (x-y)=s.act x-s.act y from fun x y=>map_sub s.actEquiv x y,mirror_cell]
omit s in
lemma ink_pair_free (k:ℝ)(v:Train j)(x y:Site n)(a b: Axis)(hp:a≠b): carnel k v n (x,coord a) (y,coord b)=0:= by
   unfold carnel realOf; simp only [Matrix.map_apply,spectral_apply]; have he (p: Site n) : buckle k v (mon p) (coord a) (coord b)=0:= by unfold buckle;split <;> simp only [Matrix.zero_apply, fieldD,mask_value, coord_iff, hp,↓reduceIte]
   simp [he]
lemma dart_hh (k:ℝ)(v:Train j)(x y:wire G n): bandR G v k n x y= City.banner s (Pose.bearing x) * bandR G v k n (dart s x) (dart s y)*City.banner s (Pose.bearing y):= by
   obtain ⟨p,a,i⟩:=x; obtain ⟨q,b,j⟩:=y; obtain ⟨u,rfl⟩:=axisEquiv.surjective a; obtain ⟨w,rfl⟩:=axisEquiv.surjective b
   have he (x:Axis):axisEquiv.symm (axisEquiv x)=x:=axisEquiv.symm_apply_apply x
   rw [bandR_note,bandR_note]; simp only [bearing,dart,he];by_cases h:i=j; swap; · simp [h]
   rw [if_pos h,if_pos h]; by_cases hh:u=w; swap;
   · rw [show axisEquiv _=coord u from rfl,show axisEquiv _=coord w from rfl, ink_pair_free k v p q u w hh, ink_pair_free k v _ _ _ _ (s.perm.injective.ne hh),mul_zero,zero_mul]
   subst w; have hv: City.banner s u *City.banner s u=1 := by unfold City.banner; split <;> simp
   rw [show axisEquiv u=coord u from rfl]; nth_rw 1 [ink_curve s k v p q (posStat s u) u]; rw [mul_comm (City.banner s u),mul_assoc,hv,mul_one]
lemma sung (k:ℝ)(v:Train j): displayed G s n * bandR G v k n * (displayed G s n)ᵀ=bandR G v k n:= by
    ext i u;rw [Matrix.mul_apply,Finset.sum_eq_single (dart s u)]; swap;· intro b _ hb;simp [displayed,hb]
    swap; · simp
    simp only [Matrix.transpose_apply,displayed, Pi.single_eq_same]; rw [Matrix.mul_apply,Finset.sum_eq_single (dart s i)]
    · simp only [displayed, Pi.single_eq_same];exact (dart_hh s _ _ _ _).symm
    · intro b _ hb; simp [displayed,hb]
    simp
variable {T Y:Anthem D G}(h:Son T Y l s)
include h
private lemma otter (v:Train j)(k:ℝ)(p:Studio D)(w:chain (wire G n) r): marble r (binned v k n (Kemp.banner l (T p) n)) (dart s ∘ w)= marble r (binned v k n (Kemp.banner l (Y (Dawn.froth s D p)) n)) w * ∏ i, City.banner s (bearing (w i)):= by
    let V:=Kemp.banner l (T p) n;let Q:=Kemp.banner l (Y (Dawn.froth s D p)) n; let A:= displayed G s n; let F:= bandR G v k n
    have he : coeff 0 V=mixRows A (coeff 0 Q):= by
       let R:=City.arc G s n; have ht:=h n p (wire G n) (fun z:Jets.Rays (wire G n)=>z ∘ id) R (fun _ _=>1) rfl (map_zero R) (show ContDiffAt ℝ ω (fun z:Jets.Rays (wire G n)=> z) 0 from contDiffAt_id) R.contDiff.contDiffAt (fun _=>contDiffAt_const) ⟨1,rfl⟩ (.of_forall fun z=>by unfold R; rw [City.arc_pull]; ext1 b;simp [Lattice.gauge]); rw [Bank.pane_letter (displayed G s n) R R.contDiff.contDiffAt rfl,fit_translate] at ht; have hx:=congr_arg (coeff 0) ht; simp only [coeff_map] at hx; change MvPolynomial.rename id _=mixRows _ _ at hx;rw [MvPolynomial.rename_id_apply] at hx; exact hx
    change marble r (hearth F (coeff 0 V)) (dart s ∘ w)=_;rw [he, hearth_mix F, show A*F*Aᵀ=F from sung ..,Lava.target,pearl,tsum_fintype,Finset.sum_eq_single w];swap;· intro b _ hb; have he:∃ i,b i≠w i:=Function.ne_iff.mp hb; obtain ⟨i,hi⟩:=he; rw [Finset.prod_eq_zero (Finset.mem_univ i) (show A (b i) _=0 from (show City.displayed G s n (b i) ((dart s ∘ w) i)=0 from Pi.single_eq_of_ne ((darts s).ne (Ne.symm hi)) _)),mul_zero]
    swap; · simp
    simp only [A,comp_apply,displayed,Pi.single_eq_same];rfl
include h
lemma wave_spin (v:Train j)(hk:0<k)(hj:4≤j)(hp:Wade o T l)(ht:Wade o Y l)(p:Studio D)(w:chain (edgeL G) r): winner v k l T p r (dart s ∘ w)=winner v k l Y (Dawn.froth s D p) r w *∏ i, City.banner s (bearing (w i)):= by
   apply tendsto_nhds_unique (mat_greens v hk hj hp p r _)
   apply ((mat_greens v hk hj ht (Dawn.froth s D p) r w).mul_const _).congr'; refine .of_forall fun n=>?_; dsimp only; rw [show Lotus.drip n ∘ dart s ∘ w= dart s ∘ (Lotus.drip n ∘ w) from funext fun i=> arc_wrap s n _]; exact (otter s h v k p _).symm
end YM.FormalBulk08.Avenue
