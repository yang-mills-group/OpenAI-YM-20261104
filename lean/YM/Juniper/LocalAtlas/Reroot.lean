import YM.Juniper.LocalAtlas.Taylor
import YM.Juniper.LocalAtlas.Moments
/-!
 # Keep all tags/paths of the Poll GRACE law from the authentic analytic Sienna proof

 Aim all orders: cut shutters removed **after** taking the Taylor jets (not
 justified on entire variable disk). Use one registry of tensor coefficients
 independent of volume choices, as operator jets of the SAME integrand with
 flat sweep. Prepare polynomial weights on z to pay an entire uncut tensor
 integral, even though the field functions are globally only priced on the
 purchased disk in Body. On a larger disk in Body normalize z and prove exact
 rescaling of vote (using `Lantern.scratch`) to derive. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.LocalAtlas
open MeasureTheory Set Function Matrix Metric Filter
open PhysicalNext.Repeat Lantern Analysis
open ConnectedActivityE6 Blaze Brush Poll
open scoped Classical Topology ContDiff BigOperators MatrixOrder
variable {ι : Type}[Fintype ι][DecidableEq ι]
    {E : Type}[NormedAddCommGroup E][NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {φ ψ : E × Poll.Body ι→ℝ}{ρ:E→ Poll.Body ι}{M : E→ Matrix ι ι ℝ}
    {k : ℕ}{D b p W q : ℝ}
local notation "V" => ℝ × E
local notation "E#" => Poll.Body ι
local notation "g" => grace φ ψ ρ M
local notation "v" => Lantern.vote φ ρ

def turn (w : ℝ) : ℝ×E→L[ℝ] ℝ×E:= ContinuousLinearMap.prodMap (w • ContinuousLinearMap.id ℝ ℝ) (ContinuousLinearMap.id ℝ E)

omit [FiniteDimensional ℝ E] [DecidableEq ι] in
private lemma spooled (s : ℝ)(z : Poll.Body ι)(x:ℝ×E): Lantern.vote φ ρ (s • z) x= s^2 * v z (turn s x):= by
   -- exact at the integrand level, no integrated estimates anywhere
   unfold Lantern.vote; rw [← intervalIntegral.integral_const_mul]; refine intervalIntegral.integral_congr fun i _=>?_
   have hz : visit ρ (s•z) i x=visit ρ z i (turn s x):= by
      unfold visit; change (x.2,ρ x.2+i • x.1 • s • z)=(x.2,ρ x.2+i• (s*x.1) • z); rw [smul_comm x.1 s,mul_smul]
   unfold Lantern.offer scratch; rw [hz,show ((0:E),s • z)=s • ((0:E),z) from (by simp),map_smul]
   simp only [_root_.smul_apply,map_smul, smul_eq_mul]
   ring
omit [FiniteDimensional ℝ E] in
lemma branches (s : ℝ)(z : Poll.Body ι)(x:ℝ×E) : g (s • z) x=g z (turn s x)+(s^2-1)*(v z (0,0)-v z (turn s x)) := by
   unfold grace; rw [spooled,spooled]
   have ht (i:ℝ): visit ρ (s•z) i x=visit ρ z i (turn s x):= by unfold visit; change (x.2,ρ x.2+i • x.1 • s • z)=(x.2,ρ x.2+i• (s*x.1) • z); rw [smul_comm x.1 s,mul_smul]
   rw [ht,ht,show turn s (0,(0:E))=(0,0) from map_zero _, show (turn s x).2=x.2 from rfl]; ring

def cylinder (s x₀:ℝ) (E:Type) [NormedAddCommGroup E] := ball (0:ℝ) s ×ˢ ball (0:E) x₀
omit [FiniteDimensional ℝ E] in
lemma spin (s:ℝ) (hs:1 ≤ s) : ‖turn (E:=E) s‖ ≤ s:= by
   have hp:0 ≤ s:=zero_le_one.trans hs
   apply ContinuousLinearMap.opNorm_le_bound _ hp
   intro x; change max ‖s*x.1‖ ‖x.2‖ ≤ _
   rw [norm_mul,Real.norm_of_nonneg hp]; exact max_le (mul_le_mul_of_nonneg_left (norm_fst_le _) hp) ((norm_snd_le _).trans (le_mul_of_one_le_left (norm_nonneg _) hs))
variable (H : Golf φ ψ ρ M k D b b p) (hD:1 ≤ D)
local notation "u" => fee k p D
local notation "π" => acrossE k p D
-- leaf estimate grows polynomially in relτ. Choose uniform across larger
-- z only on ball radius ≥1. Brush radius still native; use .trim.
def scaleFee (n : ℕ)(p D : ℝ): ℝ:= fee n p D + 2*acrossE n p D
omit [FiniteDimensional ℝ E] in
private lemma spun {Y:Type}[NormedAddCommGroup Y] [NormedSpace ℝ Y] (f:ℝ×E→Y)(x:ℝ×E)(hs:1 ≤ q)(hf : Brush k p 1 f (turn q x)): Brush k (q^k*p) 1 (f ∘ turn q) x := by
   apply Brush.offer.2; refine ⟨hf.smooth.comp _ (f:=turn q) (turn (E:=E) q).contDiff.contDiffAt,fun i hi=>?_⟩
   -- use shift_affine
   unfold normJ; have he := hf.smooth.of_le (Nat.cast_le.mpr hi)
   have ha:= shift_affine (f:=f) x 0 (turn q) i (by rw [zero_add]; exact he); simp only [zero_add] at ha; refine (congr_arg norm ha).trans_le ?_ 
   apply le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..); rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_comm (q^k)]
   exact mul_le_mul ((Brush.offer.1 hf).2 i hi) (le_trans (pow_le_pow_left₀ (norm_nonneg _) (spin q hs) i) (pow_le_pow_right₀ hs hi)) (pow_nonneg (norm_nonneg _) _) hf.nonneg
include H hD
lemma abroad (q:ℝ)(hq:1 ≤ q)(x:ℝ×E)(ht : turn q x ∈ cylinder b b E)(z:Poll.Body ι)(hz:‖z‖ ≤ q) :
    Brush k (q^(k+2)*scaleFee k p D) 1 (g z) x:= by
  let z':= q⁻¹ • z; let y:= turn q x; have hv := zero_lt_one.trans_le hq
  have h'z : ‖z'‖ ≤ D := le_trans (b:=1) (by unfold z'; rw [norm_smul,Real.norm_of_nonneg (by positivity),inv_mul_le_iff₀ hv,mul_one]; exact hz) hD
  let K:= grace φ ψ ρ M z' ∘ turn q
  let A:= Lantern.vote φ ρ z' ∘ turn (E:=E) q; let C:= A 0
  have hy: y∈ ball (0:ℝ) b ×ˢ ball (0:E) b:=ht
  have hp (z:ℝ×E) (he: turn q z∈ ball (0:ℝ) b ×ˢ ball (0:E) b): Brush k (q^k*π) 1 A z:= spun (v z') z hq (commit D H (mem_ball_zero_iff.mp he.2) (mem_ball_zero_iff.mp he.1) h'z)
  have he:= spun (g z') x hq (compel D H (mem_ball_zero_iff.mp hy.2) (mem_ball_zero_iff.mp hy.1) h'z); have h0:b>0:=H.pos
  have hF := hp 0 (by simp only [map_zero]; exact ⟨mem_ball_self h0, mem_ball_self h0⟩)
  have hA:= he.gathering (((Brush.certified (x:=x) zero_le_one C |>.climb hF.bound le_rfl).separating (hp x ht)).smul (q^2-1))
  have hh : 0 ≤ u:= (compel D H (mem_ball_zero_iff.mp hy.2) (mem_ball_zero_iff.mp hy.1) h'z).nonneg
  have hu : 0 ≤ q^k*π:= hF.nonneg
  refine (hA.climb ?_ le_rfl).shimmy (Eventually.of_forall fun t=>?_)
  · rw [Real.norm_of_nonneg (show 0≤ q^2-1 from sub_nonneg.mpr (one_le_pow₀ hq)),pow_add, scaleFee]
    nlinarith only [mul_nonneg (show 0 ≤ q^2-1 from sub_nonneg.mpr (one_le_pow₀ hq)) (mul_nonneg (pow_nonneg hv.le k) hh), hu]
  change g z t=g z' (turn q t)+(q^2-1)*(C-v z' (turn q t)); unfold C A; simp only [Function.comp_apply,map_zero]; nth_rw 1 [← show q • z'=z from smul_inv_smul₀ hv.ne' z]; exact branches q z' t

lemma fee_nn : 0 ≤ scaleFee k p D:=by
  let x:ℝ×E:=0
  have ht:turn 1 x∈cylinder b b E:= by rw [map_zero]; exact ⟨mem_ball_self H.pos,mem_ball_self H.pos⟩
  simpa only [one_pow,one_mul] using (abroad H hD 1 le_rfl x ht 0 (by rw [norm_zero]; norm_num)).nonneg

def preAux (n : ℕ)(p D C: ℝ) := clump n (scaleFee n p D) C

lemma height {x:ℝ×E} (z:Poll.Body ι)(hq:1 ≤ q)(hz:‖z‖ ≤ q)(hx:turn q x∈cylinder b b E)
    (ht : Brush k W 1 Real.exp (g z x)) : Brush k (preAux k p D W*q^((k+2)*k)) 1 (Real.exp ∘ g z) x := by
   let w:= q^(k+2); let A:=scaleFee k p D; have hp := ht.nonneg; have hv:1 ≤ w:= one_le_pow₀ hq; have he:0 ≤ A:= fee_nn H hD
   apply (Lantern.composite (abroad H hD q hq x hx z hz) ht).climb _ le_rfl; rw [pow_mul,preAux]; unfold clump; norm_num only [mul_one]
   change _ ≤ ((k.factorial:ℝ)*W*(1+(1+A))^k)*w^k; rw [mul_assoc _ _ (w^k),← mul_pow]
   refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ _) (by positivity)
   · change 0 ≤ 1+(1+w*A); positivity
   change 1+(1+w*A)≤_; linarith only [hv]

end YM.Juniper.LocalAtlas
