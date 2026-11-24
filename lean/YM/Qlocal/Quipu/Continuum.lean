import YM.Qlocal.Quipu.Psi
import YM.Comparison.RG02.Assembly.Bi
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Sonnet.Tern
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open Further.PhysicalPeriodLimitF933 Shingle Macrame Lace
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial AllOrder Fire Laplace Laplace.SigmaP Ker Ker.Start
open Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port Tilt
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{c r:Side}{a b C D Λ σ:ℝ}{k N l i j n m:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Key T[n] G)
local notation "Lℓ"=> Lobby P K G
local notation "I₀"=>Ad G P K
variable {α:Type}[Fintype α] [DecidableEq α] {B:Marker.Census α}
local notation "Y"=> ((Coarse G⊕α)⊕ J)
local notation "Ω[" n "]"=> rule ((Coarse G⊕α)⊕J) n
open Comparison.RG02
-- Taylor of the HEIGHT assembly on any reader line.No derivative of masks.Ar.Alb. Later use Price guarantee. 
section jet
variable {U X : Type} [NormedAddCommGroup X][NormedSpace ℝ X]
private lemma swing {f:ℝ→ℝ}(hf:ContDiffAt ℝ ω f 0)(k n:ℕ):
   Radial.jet (fun t:ℝ=> t^k * f t) n 1=if k≤n then Radial.jet f (n-k) 1 else 0:=by
 by_cases h:k≤n;
 · rw [if_pos h]; let H:= Assembly.Clipper.exponent hf (ContinuousLinearMap.id ℝ ℝ) 1 k (n-k); simp only [ContinuousLinearMap.id_apply,Nat.add_sub_of_le h,one_pow,one_mul] at H; exact H
 rw [if_neg h]; have hx := (((Assembly.GradeAt.shifts (fun x:ℝ=>x) contDiffAt_id rfl k).mul (Assembly.GradeAt.unchecked hf)).jet_z (i:=n) 1 (by omega)); exact hx
private lemma swinging {f:X→ℝ}(hf:ContDiffAt ℝ ω f 0)(x:X)(k:ℕ): ContDiffAt ℝ ω (fun t:ℝ=> t^k*f (t • x)) 0:= (contDiffAt_id.pow k).mul (show ContDiffAt ℝ ω (fun t:ℝ=> f (t • x)) 0 from (((zero_smul ℝ x).symm ▸ hf : ContDiffAt ℝ ω f ((0:ℝ)•x)).comp (f:=fun t:ℝ=>t • x) _ (contDiffAt_id.smul contDiffAt_const))) -- hf requires f 0 at composed 0
private lemma leaning {f:X→ℝ}(hf:ContDiffAt ℝ ω f 0)(x:X): ContDiffAt ℝ ω (fun t:ℝ=> f (t • x)) 0:= by simpa only [pow_zero,one_mul] using swinging hf x 0
private lemma pound {f:X→ℝ}(hf:ContDiffAt ℝ ω f 0)(x:X)(k:ℕ): Radial.jet (fun t:ℝ=> f (t • x)) k 1= Radial.jet f k x:= by
 let v:ℝ→L[ℝ] X:=ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) x; exact (Assembly.jet_continuous_right v (hf.of_le le_top) 1).trans (congr_arg _ (show v 1=x from one_smul ℝ x))
private lemma pile {F:U→ ℝ→ℝ}(u:Finset U)(he:∀ i,ContDiffAt ℝ ω (F i) 0)(k:ℕ): Radial.jet (fun t=>∑ v∈u,F v t) k 1=∑ v∈u,Radial.jet (F v) k 1:= by unfold Radial.jet; rw [iteratedFDeriv_fun_sum_apply (fun i _=>(he i).of_le le_top), _root_.sum_apply]; exact mul_sum ..
private lemma tap {f:ℝ→ℝ}(hf:ContDiffAt ℝ ω f 0)(x:ℝ)(k:ℕ): Radial.jet (fun t:ℝ=>x*f t) k 1=x*Radial.jet f k 1:= (Assembly.jet_apply_left (x • (ContinuousLinearMap.id ℝ ℝ)) f k (hf.of_le le_top) 1).symm -- t*x
end jet
section shift
open Tilt Two Kinetic Floe
variable (p:Clip){ι:Type}[Nonempty ι](x:ι→PathData G)(L:ι→ℝ)
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (L i))
variable (F:ι→candidates P K G)(h:proofC P K p x Q F)
variable {δ H:ℝ} (A : PortPre P K p x b δ H)(ht:0<b)
variable (hn:Ad G P K c)
variable (i:ι)(s:Senses B)
set_option quotPrecheck false
open Arbor Album
local notation "K'"=> know (costs P K p x A i α) c -- status
local notation "Z" => flatten (α:=α) (G:=G) P K hn
local notation "φ"=> Lapis.orbit (G:=G) T[c] (F i c)
local notation "η₀"=> fderiv ℝ φ 0
local notation "θ"=> colorful (η₀)
local notation "q"=> θ ∘ Tilt.walkB ∘ Z

variable (V:Ker.rule ((Coarse G⊕α)⊕RealSlice.Vertical G P K) c)
include ht h hB hx
variable (U:Tale B G) (X':U.Decision) (p':α→Site P.L) {ℓ ξ:ℝ}(hU:U.Allows ℓ ξ)(hξ:0<ℓ)
include hU hξ
local notation "Hκ"=>Fin (U.depth+1)
local notation "H'[" n "]"=> Fin (Fin.val n+Lagger.dues U.power s.val + 1)
local notation "η"=> (Binding.gaugeL (G:=G) T[c] (q V))
open Comparison.RG02.Bulk
local notation "ζ"=> (Z V).1.2
local notation "S"=> Tale.life T[c] U X' (F i c) p'
set_option quotPrecheck false
local notation "N'[" n "," r "]"=> Tern.heightZ P K s p' (X' s n r) (U.array s n r) c U.method
local notation "Ψ'"=> (essence s).card
variable (hQ:PaintSupply G N σ)
include hQ
open Lagger
set_option maxHeartbeats 600000 in
lemma roll (k:ℕ) (hh:dues U.lag s.val ≤ k): (∑ t:Places s c, Tale.life T[c] U X' (F i c) p' s t k (Z V))=∑ e:Fin (U.depth+1),∑ r:H'[e], (if U.stampE s e.val r.val ≤ k then jet (N'[e,r]) (k-U.stampE s e.val r.val) (K' V) else 0):= by
 let Q' (e:Hκ) (r:H'[e]):= N'[e,r]; let hF (v:Places s c):= posed S[c] T[c] (U.markℓ X' (Arbor.drew S[c] v p') s); let hC(v:Places s c):= placard v (ζ); let g(t:ℝ):=∑ v:Places s c,hC v * hF v (t • η); let u(e:Hκ)(r:H'[e]) (t:ℝ):= t^U.stampE s e.val r.val * Q' e r (t• K' V)
 have he(v:Places s c):ContDiffAt ℝ ω (hF v) 0:= (joint_receipt S[c] T[c] ((U.quartile s (Arbor.drew S[c] v p') hU hξ X').zeroAt)).smooth
 have he'(e:Hκ)(r:H'[e]):ContDiffAt ℝ ω (Q' e r) 0:= (facts P K s p' _ (U.array s e r) (hU.pay ..) hξ hQ c hn).2
 have hf (v):ContDiffAt ℝ ω (fun t:ℝ=> hC v*hF v (t• η)) 0:= contDiffAt_const.mul (leaning (he v) _); have hu e r:ContDiffAt ℝ ω (u e r) 0:=swinging (he' e r) _ _
 let H : ℝ:=Radial.jet (fun t:ℝ=>t^ (essence s).card * g t) k 1
 apply Eq.trans (b:=H); 
 · unfold H; rw [swing (ContDiffAt.sum (fun i _=>hf i)), if_pos (show (essence s).card≤ k by rw [Tale.hence] at hh; omega)]; erw [pile univ hf]; refine Finset.sum_congr rfl fun i _=> ?_; unfold Tale.life; rw [if_pos hh,tap (leaning (he i) η), pound (he i) η]; exact mul_comm ..
 unfold H; rw [funext fun t=> (show (t^(essence s).card*g t)=(∑ e:Hκ,∑ r:H'[e],u e r t) from heavens P K p x L Q hB hx F h A ht hn i s V U X' p' hU hξ t)]; rw [pile univ (fun e=>(ContDiffAt.sum (fun i _=>hu e i)))]; refine Finset.sum_congr rfl fun e _=> ?_; rw [pile univ (hu e)]; refine Finset.sum_congr rfl fun r _=> ?_; unfold u; rw [swing (leaning (he' e r) (K' V)),pound (he' e r) (K' V)]
end shift
end YM.Qlocal.Quipu.Sonnet.Tern
