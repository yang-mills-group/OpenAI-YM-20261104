import YM.RegulatorIR.Pupil.Solstice
-- use real invariant scalar, no color U projection assumed

/-! Paid W1 gives exactly one rank-two normalization. No input projection
small divisor. Use one arbitrarily chosen color throughout.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Pupil.Rules
open Function Lattice Wilson PertExtension Orb Gauge Tree Tree.Forest MeasureTheory Filter Geometry Geometry.Field Geometry.End Chart RG Laplace Binding Ward Set Series Series.Radial Series.Tested Budget Budget.Tuple Budget.Layer Diagram Diagram.Formal Step Ledger Ledger.Sky Quadratic Taping Uniform Halo Halo.Sight Gain Prim Motion Budget.Packet Budget.Deck Finset Axial PowerSeries Momentum
open scoped ENNReal NNReal BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff PowerSeries Matrix
variable {G : Gauge}{T:Packet (Foot G) 2}

-- secondary. read colors after transport
variable (H: Rules T)(P:costM T)(x y: CapG G) (a b: Room)
include H P
lemma base_spin (p:Signed): shine T 2 (p.act a) (claw p x) (claw p y)= Pupil.sign p x.1*Pupil.sign p y.1*shine T 2 a x y:=by
 apply act_lift H P x y p a 2 (by omega); intro i hi; interval_cases i
 exact cloud0 H P x y a
 exact cloud1 H P x y a
omit P H
lemma night : shine T 2 (-a) x y=shine T 2 a x y:= by unfold shine recital; simp_rw [dial_opposite, even_two.neg_pow]
def shadeS (T: Packet (Foot G) 2)(a: Room)(i:Axis): G.Color →ₗ[ℝ] G.Color →ₗ[ℝ] ℝ:= LinearMap.mk₂ ℝ
    (fun x y : G.Color => ∑ u:G.ColorIndex,∑ v:G.ColorIndex,x u*y v*shine T 2 a (i,u) (i,v))
    (by intros; simp [add_mul,Finset.sum_add_distrib])
    (by intros; simp [mul_assoc,Finset.mul_sum])
    (by intros; simp [mul_add,add_mul,Finset.sum_add_distrib])
    (by intros; simp [mul_assoc,Finset.mul_sum,mul_left_comm])
include H
lemma shade_sym (i:Axis)(u v:G.Color) : shadeS T a i u v=shadeS T a i v u:=by
 let S(u v:G.ColorIndex):=shine T 2 a (i,u) (i,v)
 change ∑ k : G.ColorIndex,∑ j:G.ColorIndex,u k * v j * S k j=∑ k,∑ j, v k*u j*S k j; rw [sum_comm]; apply sum_congr rfl;intro k _;apply sum_congr rfl;intro j _;rw [mul_comm (u j)];apply congr_arg; exact (rotor H ..).trans (night ..) -- infer
omit H
include P
lemma shimmer (i:Axis)(u v:G.Color) : shadeS T a i u v= ∑' z:Cover,sparkle T (0,i) (z,i) u v *dial a z^2:=by
 unfold sparkle; simp_rw [sum_mul]
 let f(j k:G.ColorIndex)(z: Cover):= u j*v k*(starE T (i,j) (i,k) z *dial a z^2)
 have hx : shadeS T a i u v= ∑ j:G.ColorIndex,∑ k:G.ColorIndex,u j*v k* ∑' z,starE T (i,j) (i,k) z*dial a z^2:=rfl
 rw [hx]; simp_rw [← tsum_mul_left]; have hs j k: Summable (f j k):= (P (i,j) (i,k) a 2 (by omega)).mul_left _
 simp_rw [mul_assoc (u _ * v _)] -- star terms
 change ∑ j,∑ k,∑' z,f j k z=∑' z,∑ j,∑ k,f j k z -- parentheses
 rw [Summable.tsum_finsetSum (fun i _=> summable_sum fun k (_:k∈Finset.univ)=> hs i k)]
 exact Finset.sum_congr rfl fun i _=> (Summable.tsum_finsetSum (fun k _=> hs i k)).symm
include H
lemma glows_color (u v:G.Color) (i : Axis) (k:G.El) : shadeS T a i (G.adjoint k u) (G.adjoint k v)=shadeS T a i u v:= by
 rw [shimmer P,shimmer P]; exact tsum_congr fun z=> congr_arg (· * _) (H.pearl k (0,i) (z,i) u v).symm
variable (hG:G.Simple)
include hG
lemma solar_eq (i:Axis) : ∃ c:ℝ,∀ u v:G.Color, shadeS T a i u v=c*inner ℝ u v:=by
 apply Gauge.invariant_scalar hG _ (shade_sym H a i)
 intro u v z
 let f:G.Color →L[ℝ] G.Color →L[ℝ] ℝ:= LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp (shadeS T a i))
 let X(t:ℝ):= G.adjoint (G.lieExp (t • u)) v
 let Y(t:ℝ):= G.adjoint (G.lieExp (t • u)) z
 have h : HasDerivAt (fun t=> f (X t)) (f (G.ad u v)) 0:= f.hasFDerivAt.comp_hasDerivAt (0:ℝ) (Stationary.color_pitch u v)
 have hp : HasDerivAt Y (G.ad u z) 0:= Stationary.color_pitch u z
 have he:= h.clm_apply hp; simp_rw [show ∀ t,f (X t) (Y t)= f v z from fun t=> glows_color H P ..] at he
 have hi:= he.unique (hasDerivAt_const ..)
 rw [show Y 0=z from by simp [Y],show X 0=v from by simp [X]] at hi; exact eq_neg_of_add_eq_zero_left hi
omit H P hG in
lemma shade_raw (i:Axis)(x y:G.ColorIndex): shadeS T a i (EuclideanSpace.basisFun _ ℝ x) (EuclideanSpace.basisFun _ ℝ y) = shine T 2 a (i,x) (i,y):=by
 unfold shadeS; simp [LinearMap.mk₂_apply,EuclideanSpace.basisFun_apply] -- simplify
-- fee test

def token (T:Packet (Foot G) 2) (c:G.ColorIndex):= shine T 2 (step 0) (1,c) (1,c)
variable {c:G.ColorIndex}(hf :token T c=0)
include hf
lemma shade_null (x y:G.ColorIndex) : shine T 2 (Lattice.step 0) (1,x) (1,y) =0:=by
 obtain ⟨q,H⟩:= solar_eq H P (step 0) hG 1
 let B:= EuclideanSpace.basisFun G.ColorIndex ℝ
 have hx:= H (B c) (B c)
 rw [show B= _ from rfl] at hx; rw [show inner ℝ (B c) (B c)=1 from B.inner_eq_one c,mul_one, show shadeS T _ _ _ _=token T c from shade_raw ..,hf] at hx
 rw [show shine T 2 _ _ _=shadeS T _ 1 (B x) (B y) from Eq.symm (shade_raw ..),H,← hx,zero_mul]
-- lifted tests. no need simplicity for longitudinal
omit hf hG
lemma square_null (i:Axis)(x y:G.ColorIndex): shine T 2 (step i) (i,x) (i,y)=0:=by
 have hp := cloud2 H P (i,x) (step i) y
 rw [sum_eq_single i] at hp; simp at hp; exact hp
 intro j _ hh;simp [hh];simp

def purePerm (e:Equiv.Perm Axis) : Signed:= ⟨e,fun _=>false⟩
omit H P in
lemma picks (e:Equiv.Perm Axis)(j:Axis): (purePerm e).act (step j:Room)=step (e j):=by rw [← Step.vec_pos, ← Step.vec_rotate (posDir j)]; rfl
omit H P in
lemma trades (x y:Axis)(h:x≠y): ∃ p:Equiv.Perm Axis,p 0=y ∧ p 1=x:=by
 let t:= Equiv.swap 0 y; let u:=t 1; have he:u≠ y:=by intro h; exact (show (1:Axis)≠0 from by decide) (t.injective (h.trans (Eq.symm (Equiv.swap_apply_left ..))))
 refine ⟨t.trans (Equiv.swap u x),by change Equiv.swap u _ (Equiv.swap 0 _ _)= _; rw [Equiv.swap_apply_left]; exact Equiv.swap_apply_of_ne_of_ne he.symm (Ne.symm (by assumption)),Equiv.swap_apply_left ..⟩ -- need disambiguation h
include hG hf
lemma square_all (i k:Axis)(x y:G.ColorIndex): shine T 2 (step k) (i,x) (i,y)=0:=by
 by_cases hx:i=k
 · subst i; exact square_null H P ..
 obtain ⟨p,h,hp⟩:= trades i k hx
 have ht:= base_spin H P (1,x) (1,y) (step 0) (purePerm p); rw [picks,h,shade_null H P hG hf,mul_zero] at ht
 rw [← hp];exact ht
end YM.RegulatorIR.Pupil.Rules
