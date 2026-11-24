import YM.SchemeRG11.Plate.Station
/-! Ward equation at marked point. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Tree
open Lattice Function Filter Haze Pert Bare Labels Bark MvPolynomial
open scoped Classical ContDiff
variable {U V E M L:Type*}[AddCommGroup L][One L] {G:Gauge}

def alpha (x:Four L)(j:ℕ)(k:Taylor G j →ₗ[ℝ] ℝ) := ((starLoft x j false 1 k):Pulse _).choose
def omegaJ (x:Four L)(j:ℕ)(k:Taylor G j→ₗ[ℝ] ℝ):= (1/2:ℝ) • ((starLoft x j true 1 k):Nimbus _).choose
lemma speak_alpha (x:Four L)(j:ℕ)(k:Taylor G j →ₗ[ℝ] ℝ)(v:Code G L→ℝ): sense v (alpha x j k)= k (starJet false 1 x j (tint v) (tint v)):=((starLoft x j false 1 k: Pulse _).choose_spec v).symm
lemma alpha_at (x:Four L)(j:ℕ)(k:Taylor G j→ₗ[ℝ] ℝ)(A:trunk G L): sense (cant A) (alpha x j k)=k (starJet false 1 x j A A):=by rw [speak_alpha,tint_inv]
lemma speak_omega (x:Four L)(j:ℕ)(k:Taylor G j →ₗ[ℝ] ℝ)(v:Code G L→ℝ): aeval v (omegaJ x j k)=(1/2:ℝ) * k (starJet true 1 x j (tint v) (tint v)):=by rw [omegaJ,map_smul,((starLoft x j true 1 k:Nimbus _).choose_spec v).symm]; rfl
lemma omega_at(x:Four L)(j:ℕ)(k:Taylor G j→ₗ[ℝ] ℝ)(A:trunk G L):aeval (cant A) (omegaJ x j k)=(1/2:ℝ) * k (starJet true 1 x j A A):=by rw [speak_omega,tint_inv]
lemma mute (x:Four L)(j:ℕ)(k:Taylor G j→ₗ[ℝ] ℝ)(e:Four L→G.Color): sense (cant (ascent e)) (alpha x j k)=0:=by rw [alpha_at,sworn,map_zero]
lemma tacks(v w:U→ℝ)(p:Paper U ℝ): HasDerivAt (fun t:ℝ=> MvPolynomial.aeval (v+t•w) p) (aeval v (vent w p)) 0:=by
 induction p using MvPolynomial.induction_on with
 | C c => simp_rw [vent_C,map_zero,aeval_C]; apply hasDerivAt_const
 | add a b ha hb=> simp_rw [map_add]; exact ha.add hb
 | mul_X a i ha =>
   have he:HasDerivAt (fun t:ℝ=> (v+t•w) i) (w i) 0:=by simp_rw [Pi.add_apply,Pi.smul_apply,smul_eq_mul]; simpa using (hasDerivAt_id' (0:ℝ) |>.mul_const (w i) |>.const_add (v i))
   simp_rw [map_mul (MvPolynomial.aeval _),aeval_X,vent_x,map_add,map_smul,map_mul, aeval_X]; convert! ha.mul he using 1; simp [add_comm,mul_comm]
lemma bookend (x:Four L)(j:ℕ)(k:Taylor G j→ₗ[ℝ] ℝ) (A B : trunk G L) :
  aeval (cant A) (vent (cant B) (omegaJ x j k))= (1/2:ℝ) * (k (starJet true 1 x j A B)+k (starJet true 1 x j B A)):=by
 let Q: trunk G L→trunk G L→ℝ :=fun U V=>k (starJet true 1 x j U V)
 have hq:= tacks (cant A) (cant B) (omegaJ x j k)
 have he(t:ℝ): aeval (cant A+t•cant B) (omegaJ x j k)=(1/2:ℝ)*(Q A A + t*(Q A B + Q B A)+t*t*Q B B):=by
   rw [show cant A+t•cant B=cant (A+t•B) from rfl,omega_at, Bark.star_add, star_add₂, star_add₂,star_s₂,star_s₂,star_s,star_s]; simp only [map_add,map_smul,smul_eq_mul]; unfold Q;ring
 simp_rw [he] at hq; apply hq.unique
 let z:ℝ:=Q A B+Q B A
 convert! ((((hasDerivAt_id' (0:ℝ) |>.mul_const z).const_add (Q A A)).add (((hasDerivAt_id' (0:ℝ)).mul (hasDerivAt_id' (0:ℝ))).mul_const (Q B B))).const_mul (1/2:ℝ)) using 1; simp [Q,z]
lemma brace (x:Four L)(j:ℕ)(k:Taylor G j→ₗ[ℝ] ℝ)(A:trunk G L)(e:Four L→G.Color)(he:e x=0):
 aeval (cant A) (vent (cant (ascent e)) (omegaJ x j k)) = -(1/2:ℝ) * sense (cant (spur e A)) (alpha x j k):=by
 rw [bookend,alpha_at]
 have h0 := congrArg k (heals A 1 x j e he)
 rw [map_add,map_add,map_zero,secular] at h0
 rw [secular]; linarith only [h0]
end YM.SchemeRG11.Tree
