import YM.XSpace.Chrome
/-!
# Evaluate the convolution at the first two chiral vertices

Symmetry emerges; cross-terms can have different shift conventions, which must be priced when proving the detection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Octave
open Function Set Filter Lattice Trace Relief Sail Asymptotics Chiral
open scoped Topology BigOperators
variable {x y z:Cover}{A B C:Toe}{i j:ℕ}
lemma ret_add (h:A∈Terrain i)(p:B∈Terrain i)(H:C∈Terrain j)(he:4< i+j)(x y:Cover): res (A+B) C x y=res A C x y+res B C x y:=by unfold res; rw [← (easyT h H he x y).tsum_add (easyT p H he x y)]; exact tsum_congr fun i=> add_mul ..
lemma ret_smul (n:ℝ)(A B:Toe)(x y:Cover): res (n • A) B x y=n*res A B x y:=by unfold res; rw [← tsum_mul_left]; exact tsum_congr fun i=>mul_assoc ..
lemma ret_fin {T:Type*}(p:T→Toe)(F:Finset T)(h:∀ i'∈F,p i'∈Terrain i)(H:A∈Terrain j)(he:4< i+j)(x y:Cover): res (∑ i∈F,p i) A x y=∑ i∈F,res (p i) A x y:=by
  classical induction F using Finset.induction_on with | empty=> simp [res,string] | insert k B hk ih=> rw [Finset.sum_insert hk,Finset.sum_insert hk]; have hh:=(fun w hw=>h w (Finset.mem_insert_of_mem hw)); rw [ret_add (h k (Finset.mem_insert_self ..)) (Submodule.sum_mem _ hh) H he, ih hh]
lemma ret_dual (h:A∈Terrain i)(p:B∈Terrain j)(he:4< i+j)(x y:Cover)(a:Axis): res (D a A) B x y=res A (η a B) x y:=by
  let q(w:Cover):= A (w-x); let r(w:Cover):= B (w-y); have hp:= duet_dual q r a (by apply (easyT (slide_hill h (step a)) p he x y).congr; intro w; change A (step a+(w-x))*_ = A (w+step a-x)*_; congr 2; abel) (easyT h p he x y); unfold res; rw [show (fun w=> string _ _ x y w)=(fun w:Cover=> D a q w*r w) from funext fun w=>by change (A (_-x+_)-_)*_=(A (w+_-x)-_)*_; rw [sub_add_eq_add_sub],hp]; apply tsum_congr; intro w; change q w * (B (w-step a-y)-_)= _*(B (w-y-step a)-_); rw [sub_right_comm w]; rfl
lemma ret_swap (A B:Toe)(x y:Cover): res A B x y=res B A y x:=tsum_congr fun i=>mul_comm ..
local notation "𝕆" => Sail.cover
abbrev chordal (a b:Axis):= res (η a 𝕆) (η b 𝕆)
lemma coil (x y:Cover): (∑ a:Axis,chordal a a x y)=𝕆 (x-y):=by
  let f (a:Axis):= D a (η a 𝕆); have he: (∑ a:Axis,f a)= Trace.lamp 𝕆:=by
    unfold f Trace.lamp; simp_rw [down_eq,LinearMap.sum_apply]; rfl -- 
  have hh(a:Axis): chordal a a x y=res (f a) 𝕆 x y:= by unfold f; rw [ret_dual (down_hill hill2 a) hill2 (by norm_num)]
  simp_rw [hh]; rw [← ret_fin (i:=4) f Finset.univ (fun k _=> steps_hill (down_hill hill2 k) k) hill2 (by norm_num), he, res]; unfold string; simp_rw [poisson,ite_mul,sub_eq_zero]; simp
lemma ret_grad_comm (A:Toe)(a b:Axis): η a (η b A)=η b (η a A):=by funext z; change A (z-step a-step b)-_-(A (z-_)-_)=A (z-step b-step a)-_-(A (z-_)-_); rw [sub_right_comm z]; change _-A (z-step a)-(A (z-step b)-A z)=_-A (z-step b)-(A (z-step a)-A z); ring
lemma shift_fee (a:Axis): η a 𝕆+D a 𝕆 ∈Terrain 4:=by rw [down_phase,neg_add_eq_sub]; rw [← neg_sub]; apply Submodule.neg_mem; exact surfaces (safekeeping (steps_hill hill2 a) _)
variable {ι:Type}{L:Filter ι}{a:ι→ℝ}{x y:ι→Cover}(s:Relief.Stage L a)(H:distFee L a (fun i=> x i-y i))
include s H in
lemma shrunk (hx:A∈Terrain 4)(hy:B∈Terrain 3): Little L a 2 (fun i=> res A B (x i) (y i)):=by
  unfold res; apply pull s; obtain ⟨p,hp,P⟩:=H; obtain ⟨E,hE,J⟩:= sonar hx; obtain ⟨F,hF,K⟩:=sonar hy
  apply tango (F:=fun i=> string (rate 4) (rate 3) (x i) (y i)) (B:=E*F) _ (mul_nonneg hE.le hF.le) (Eventually.of_forall (fun i w _=> by unfold string; rw [norm_mul,Real.norm_of_nonneg (mul_nonneg (sound ..).le (sound ..).le)]; exact (mul_le_mul (J _) (K _) (norm_nonneg _) (mul_nonneg hE.le (sound ..).le)).trans_eq (mul_mul_mul_comm ..)))
  apply jitter s (P:=fun i d=> d≤pad (x i-y i)) hp ((P.and s.good).mono fun i ⟨hi,h⟩=> (div_le_iff₀ h).2 (hi.trans_eq (mul_comm ..))); refine Eventually.of_forall fun i D hd h B _=>?_ ; have hi : 0<D:=zero_lt_one.trans_le hd; exact (Finset.sum_le_sum (fun w (_:w∈B)=> le_of_eq (Real.norm_of_nonneg (mul_nonneg (sound 4 (w-x i)).le (sound 3 (w-y i)).le)))).trans ((duet hd (Real.one_le_sqrt.mpr hd) h ⟨le_rfl,fun _=>le_rfl⟩ ⟨by norm_num,fun _=>le_rfl⟩ (by norm_num) B).trans (by norm_num; gcongr; norm_num))
include s H in
lemma conductor (i j:Axis): Little L a 2 (fun v=>chordal i j (x v) (y v)-chordal j i (x v) (y v)):=by
  refine ((shrunk s H (shift_fee i) (down_hill hill2 j)).sub (shrunk s H (shift_fee j) (down_hill hill2 i))).congr (fun v=>?_) (fun _=>rfl); rw [ret_add (down_hill hill2 i) (steps_hill hill2 i) (down_hill hill2 j) (by norm_num),ret_add (down_hill hill2 j) (steps_hill hill2 j) (down_hill hill2 i) (by norm_num),ret_dual hill2 (down_hill hill2 j) (by norm_num),ret_dual hill2 (down_hill hill2 i) (by norm_num), ret_grad_comm 𝕆 i j]; unfold chordal; ring
end YM.XSpace.Octave
