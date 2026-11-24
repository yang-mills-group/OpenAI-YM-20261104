import YM.AllOrder.Floe.Guards
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{n m:Side}{a b C D Λ σ:ℝ}{k N l:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Key T[n] G)
local notation "Lℓ"=> Lobby P K G
local notation "I₀"=>Ad G P K
set_option quotPrecheck false
local notation "Q[" n "," hn "]"=> (arbitrate P K (n:=n) hn)
variable {ι:Type} [Nonempty ι] (p:Clip) (O: ChartRatio G)(x:ι→PathData G)(L: ι→ℝ)
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (L i)) (hO:LocalRatio O)
local notation "Z"=> Q.tables p P
variable (F:ι→candidates P K G)(h:proofC P K p x Q F)
set_option quotPrecheck false
local notation "A[" i "," n "]"=> clay P K (x i) p n
local notation "u[" i "," n "]"=> Lapis.orbit T[n] (F i n)
variable (V:ι→ Layout G) (T:Finset Age) (hV:∀ i,Legal T (V i)) (Γ:ι→ℝ)
local notation "D[" i "," n "," hn "]"=> (startup T[n] O (label S[n]) (x i) p Q hn (hx i) (h i n hn) hO)
local notation "W"=> License (Ad G P K) Γ
open Iron
variable {δ H:ℝ} (A : PortPre P K p x b δ H)(ht:0<b)(hs:b≤leaseF a N)
variable (hL : CreditF Γ l L)
local notation "U[" i "," n "," hn "]"=> books T[n] (V i) T D[i,n,hn]
local notation "A₀[" i "," n "," hn "]"=> (rooted P K p x L Q hx F h i (n:=n) hn)
local notation "d₀"=> stalk P K p x A
open Kinetic
open Haiku Kinetic Kinetic.Port.Refuge
local notation "Ω0"=>prePhase P K p O x L Q hx hO F h V T hV
local notation "D₀[" i "," n "," hn "]"=> augment T[n] (V i) T D[i,n,hn] (hV i)
lemma precise_top (i:ι) (n:Side)(hn:I₀ n) (v':rule (Coarse G) n) (k:ℕ): let A:=D₀[i,n,hn]; let V':=exteriorL G n; ratePlan A k (V' v')= just (preview A) k + (Ω0 i k n) v':= by
  intro A V'; unfold prePhase ratePlan; rw [dif_pos hn]; by_cases hp:k=0; subst k; change preview A- liftQ _ _ _ + _= _; rw [if_pos rfl]; change _+distilled A 0 (V' v')= preview A+(distilled A 0 (V' v')-liftQ _ _ _); -- placeholders?
  · rw [sub_add_eq_add_sub,add_sub_assoc]; rfl
  rw [if_neg hp]; have hv(d:ℝ): just d k=0:= if_neg hp; change just _ k+ distilled A k _= just (preview A) k + ((distilled A k ((exteriorL G n) v'))-0); rw [hv,hv,sub_zero]
include hx hV Q hO h F
variable (i:ι)(y:ℝ→ rule (Coarse G) n) (hy:ContDiffAt ℝ ω y 0)(hn:Ad G P K n)
include hy hn
lemma citation (k:ℕ) : let A:= D₀[i,n,hn]; let x':=exteriorL G n ∘ y; weigh y (fun j=>Ω0 i j n) k = weigh x' (ratePlan A) k - just (preview A) k := by
 intro A x'; let L:= ratePlan A; let a j:= L j ∘ exteriorL G n; let f:Book (rule E n):=fun j=> Ω0 i j n; have Heq : f= a - wirings (fun _=>preview A):=by funext j y; exact Eq.symm (sub_eq_of_eq_add' (precise_top P K p O («x») _ Q hx hO F h V T hV i n hn y j)) -- inspect param assumption
 change weigh y f k=_; have hv(j:ℕ): Response.Budget (y 0) a j:= fun k' _=> ((all_cost A k').smooth.contDiffAt.comp _ (exteriorL G n).contDiff.contDiffAt)
 rw [Heq,weigh_sub hy (hv _) (le_refl k) (install_just _ contDiffAt_const), just_read hy contDiffAt_const]; congr 1; -- may solve weigh definitional (comp)
 · exact ((Act.static (n:=k) (preview A)).writes k le_rfl)
omit hy hn
open AnalyticBridge.GaussianFieldAlignment Locations
lemma spectacle (k:ℕ)(i:ι)(n:Side)(hn:Ad G P K n) : Haiku.Etiquette (fun k=> Ω0 i k) n k:=by
 let W':=x i; let T₀:= T[n]; let A:= D₀[i,n,hn]; let x':=exteriorL G n; let C':= spend (f:=below P n) (V i) T (Laplace.primitive W' p);  have ht α:Toll (below P n) (C' α):= orchestra W' p (V i) T (hV i) α (hx i)
 have hp:0<A.paid 0:= mul_pos (pow_pos hO.scale _) (Real.exp_pos _)
 refine ⟨fun v w u p' he hx' hu hY=> ?_,fun v s hV0=> ?_⟩
 · rw [citation P K p O x L Q hx hO F h V T hV i v he hn k,citation P K p O x L Q hx hO F h V T hV i w hx' hn k]; apply congr_arg (·- _) (congr_fun (Response.tinted A hp hO hn.1 ht (x'.contDiff.contDiffAt.comp _ he) (x'.contDiff.contDiffAt.comp _ hx') hu ?_) k); change courier (x' ∘ w)=ᶠ[𝓝 0] _; rw [show courier (x' ∘ w)=_ from coach w]; simp_rw [show courier (x' ∘ v)=_ from coach v]; exact hY
 obtain ⟨ρ,hρ⟩:= Q.graph (Locations.forest s 0 T₀) (hx i) hn rfl rfl; let B:= augment (Locations.forest s 0 T₀) (V i) T (startup (Locations.forest s 0 T₀) O (label S[n]) W' p Q hn (hx i) hρ hO) (hV i); have he: 0<B.paid 0:= mul_pos (pow_pos hO.scale _) (Real.exp_pos _); let v':= Stationary.orderTurn s ∘ v; have hV': ContDiffAt ℝ ω v' 0:= (Stationary.orderTurn s).contDiff.contDiffAt.comp _ hV0
 rw [citation P K p O x L Q hx hO F h V T hV i v hV0 hn k,citation (y:=v') P K p O x L Q hx hO F h V T hV i hV' hn k]; apply congr_arg (·-_) (congr_fun _ k); trans weigh (x'∘v') (ratePlan B); -- incorrect congr_arg unification. fix
 · apply Response.balanced A (x'.contDiff.contDiffAt.comp _ hV0) hp hO hn.1 ht s 0 B he (x'.contDiff.contDiffAt.comp _ hV'); rw [show courier (x'∘v)=_ from coach v, show courier (x'∘v')=_ from coach v']; funext t; change Stationary.input G n (t•Stationary.orderTurn s _)=pull _ _ (Stationary.input G n (t• v t)); rw [←map_smul]; exact (Stationary.flip_links s _).symm
 exact coherent B A (x'.contDiff.contDiffAt.comp _ hV') he hO hn.1 ht hp
end YM.AllOrder.Floe
