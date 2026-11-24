import YM.Qlocal.Quipu.Continuum
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
section shift
open Tilt Two Kinetic Floe
variable (p:Clip){ι:Type}[Nonempty ι](x:ι→PathData G)(L:ι→ℝ)
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (L i))
variable (F:ι→candidates P K G)(h:proofC P K p x Q F)
variable {δ H:ℝ} (A : PortPre P K p x b δ H)(ht:0<b)
variable (hn:Ad G P K c)
-- Realm: arrays share shape throughout the Licence application.Allows functions of V before schools. may ALWAYS pass maximum height & pad.This is REAL template and only analytic marked regular runway, not actual.
open Lagger
abbrev Stanza {α:Type}[DecidableEq α](B:Marker.Census α)(G:Gauge) (r:α→ℕ) (d:ℕ) := ∀ s:Senses B, ∀(e: Fin (d+1))(n: Fin (e.val+dues r s.val+1)), Album ℕ s G n.val
variable {g:α→ℕ} {y t:ℕ}
abbrev Stanza.son (U:Stanza B G g t)(y:ℕ): Tale B G:= ⟨g,t,y,U⟩
variable (Γ M: ι→ℝ) (U:ι→Stanza B G g t)(X : ∀ i,Stanza.son (U i) y |>.Decision) (ψ : ι → α→Site P.L)
variable (hM : CreditF Γ l M){u:ℝ}(hu : 0<u)(hU:∀ i,(Stanza.son (U i) y).Allows u (M i))(hb:b ≤ γ N u P)
set_option quotPrecheck false
local notation "W[" i "]"=> Stanza.son (U i) y
local notation "w"=> max (billH E J δ H) 1
local notation "C[" i "]"=> costs P K p x A i α
local notation "λ'"=>l +4*N
abbrev scores (i:ι) (c:Side) : Book ((Positions (Primary c G) × rule α c) × Poll.Body (Key (trees P K c) G)):= Tale.activity T[c] (Stanza.son (U i) y) (X i) (F i c) (ψ i)
variable (hQ:PaintSupply G N σ)(s:Senses B)(e:Fin (t+1))(r':Fin (e.val+dues g s.val+1))
abbrev echo (k:ℕ)(i:ι)(n:Side): Ω[n]→ℝ:= if hn:I₀ n then (∑ t':Places s n,Tale.life T[n] (W[i]) (X i) (F i n) (ψ i) s t' k) ∘ flatten (α:=α) P K hn else 0
local notation "Z[" e "," r "]"=> reckoned P K s ψ (fun i=>X i s e r) (fun i=> U i s e r) (j:=k-(Fin.val e+dues g s.val-Fin.val r)) (k:=y)
local notation "U₁"=> Tilt.raycut P K α (scores P K F U X ψ)
local notation "U₂"=> echo P K F U X ψ
include hQ hM hB hx ht h hU hb hu
include A
lemma prepaid (hk:k≤N): License (Ad G P K) Γ (fun i n=> Z[e,r'] i n ∘ know (costs P K p x A i α) n) b k (l+4*k):= License.move (P:=fun _=> max (billH E J δ H) 1) (freeC _ (zero_le_one.trans (le_max_right ..))) ht (fun i=> salaries P K p x L Q hB hx F h A ht i) ((into P K s ψ (fun i=> X i s e r') (fun i=>U i s e r') M Γ (fun i=>(hU i).pay s e r') hM hu hQ hB (k:=y) (show k-(e.val+dues g s.val-r'.val) ≤ N by omega)).squeeze hb (by omega) le_rfl)
local notation "Eκ"=> Tilt.raycut P K α (scores P K F U X ψ) k
private def jointly (k:ℕ):= dues (fun i:α => g i+1) s.val ≤ k
set_option maxHeartbeats 500000 in
lemma paidM (hk:k≤N) : License (Ad G P K) Γ (U₂ s k) b k (l+4*k):= by
 let z:=U₂ s k; let f:= jointly (g:=g) s k; by_cases ht':dues (fun i:α => g i+1) s.val ≤ k; swap; · apply License.adapt (License.null Γ ht); intro i n hn; funext v; unfold echo; rw [dif_pos hn,Function.comp_apply,Finset.sum_apply,Finset.sum_eq_zero]; exact fun i hv=> if_neg ht'
 let u (e:Fin (t+1))(r:Fin (e.val+dues g s.val+1))(i:ι)(n:Side):=(if e.val+dues g s.val-r.val≤k then Z[e,r] i n ∘ know C[i] n else 0)
 let d:=l+4*k; have hz(e r): License (Ad G P K) Γ (u e r) b k d := by
   unfold u; split_ifs; -- check binder `split_ifs` can't unfold under lambda?
   · exact prepaid P K p x L Q hB hx F h A ht Γ M U X ψ hM hu hU hb hQ s e r hk
   exact License.null Γ ht
 refine License.adapt ( License.pile univ (fun e i n=>∑ r,u e r i n) (fun i _=> License.pile univ (u i) (fun j _=> hz i j) ht) ht ) ?_; intro i n hn; funext v; unfold echo; rw [dif_pos hn, Function.comp_apply, Finset.sum_apply, Finset.sum_apply,roll P K p x L Q hB hx F h A ht hn i s v (W[i]) (X i) (ψ i) (hU i) hu hQ k ht']; simp_rw [Finset.sum_apply]; refine Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun r _=>?_ ; unfold u; split
 next ht=> erw [if_pos ht] <;> rfl
 next ht=> erw [if_neg ht] <;> rfl
lemma shaped : Tanner P K α (scores P K F U X ψ) Γ b N (l+4*N):=by
 constructor
 · intro i n hn; exact Tale.starts ..
 · intro k hk; refine License.adapt (License.pile univ (fun s=>(echo P K F U X ψ s k)) (fun i _=>(paidM P K p x L Q hB hx F h A ht Γ M U X ψ hM hu hU hb hQ i hk).squeeze le_rfl le_rfl (by omega)) ht) ?_; intro i n hn; funext v; unfold Tilt.raycut echo; rw [dif_pos hn,Function.comp_apply, scores,Tale.activity]; simp_rw [dif_pos hn,Finset.sum_apply,Function.comp_apply,Finset.sum_apply]
 intro i n hn k; exact Tale.licensed ..
end shift
end YM.Qlocal.Quipu.Sonnet.Tern
