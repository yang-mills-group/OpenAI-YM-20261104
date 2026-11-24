import YM.AllOrder.Kinetic.Peak
import YM.AllOrder.Haiku.Trunk
import YM.AllOrder.Haiku.Funds
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Kinetic.Port
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable (P:Patch)(K:KernelChoices){G:Gauge}{n m:Side}{a C Λ:ℝ}{k N:ℕ}
local notation "T[" n "]"=> trees P K n
local notation "S[" n "]"=> dock P K n
local notation "X[" n "]"=> Positions (Primary n G)
local notation "J"=> RealSlice.Vertical G P K
local notation "E"=> Coarse G
local notation "R[" n "]" => Poll.Body (Key T[n] G)

-- ι neutral. require at least one input context. realized at scheduled Tube and full σ via graph. station choose irrelevance.
variable {ι:Type} [Nonempty ι]
variable (p:Clip) (O: ChartRatio G)(x:ι→PathData G)(L: ι→ℝ){L':ℕ}
variable (Q:Push.Uniform.Before G a C P.J K (N+3)) (hB:P.Branches K G)(hx:∀ i,(x i).Bounds p a C (L i))
    (hO:LocalRatio O)
local notation "Z"=> Q.tables p P
local notation "Lℓ"=> Lobby P K G
variable (F:ι→candidates P K G)(h:proofC P K p x Q F)
namespace Refuge
open Haiku
set_option quotPrecheck false
local notation "R"=>topiary P K p O x L Q hx hO F h
lemma instant (x:Stationary.Link G n): Desk.night (exteriorL G n x)= Stationary.input G n x:= rfl
lemma coach (x:ℝ→ Stationary.Link G n): courier (exteriorL G n ∘ x)= life x:= by
  ext1 i; unfold Haiku.life courier; rw [Function.comp_apply,Function.comp_apply]; apply Eq.trans (b:=Desk.night (exteriorL G n (echo x i))) -- later simp
  · apply congr_arg; unfold Response.echo; rw [Function.comp_apply,map_smul]
  exact instant _
include hx Q hO h F
variable (i:ι)(y:ℝ→ rule (Coarse G) n) (hy:ContDiffAt ℝ ω y 0)(hn:Ad G P K n)
include hy hn
lemma statements (k:ℕ) : let A:= startup T[n] O (label S[n]) (x i) p Q hn (hx i) (h i n hn) hO; let x':=exteriorL G n ∘ y; weigh y (fun j=>R j i n) k = weigh x' (ratePlan A) k - just (preview A) k := by
 intro A x'; let L:= ratePlan A; let a j:= L j ∘ exteriorL G n; let f:Book (rule E n):=fun j=> R j i n; have Heq : f= a - wirings (fun _=>preview A):=by funext j y; exact Eq.symm (sub_eq_of_eq_add' (actual_top P K p O («x») _ Q hx hO F h i n hn y)) -- inspect param assumption
 change weigh y f k=_; have hv(j:ℕ): Response.Budget (y 0) a j:= fun k' _=> ((all_cost A k').smooth.contDiffAt.comp _ (exteriorL G n).contDiff.contDiffAt)
 rw [Heq,weigh_sub hy (hv _) (le_refl k) (install_just _ contDiffAt_const), just_read hy contDiffAt_const]; congr 1; -- may solve weigh definitional (comp)
 · exact ((Act.static (n:=k) (preview A)).writes k le_rfl)
omit hy hn
open AnalyticBridge.GaussianFieldAlignment Locations
lemma respectful (k:ℕ)(i:ι)(n:Side)(hn:Ad G P K n) : Haiku.Etiquette (fun k=> R k i) n k:=by
 let W:=x i; let T:= T[n]; let A:= startup T[n] O (label S[n]) W p Q hn (hx i) (h i n hn) hO; let x':=exteriorL G n; let C':= Laplace.primitive (f:=below P n) W p; let V:=ratePlan A; have ht α:Toll (below P n) (C' α):= (toll_main (hx i)).add ((toll_loop (hx i)).scale (α^2))
 have hp:0<A.paid 0:= mul_pos (pow_pos hO.scale _) (Real.exp_pos _)
 refine ⟨fun v w u p' he hx' hu hY=> ?_,fun v s hV=> ?_⟩
 · rw [statements P K p O x L Q hx hO F h i v he hn k,statements P K p O x L Q hx hO F h i w hx' hn k]; apply congr_arg (·- _) (congr_fun (Response.tinted A hp hO hn.1 ht (x'.contDiff.contDiffAt.comp _ he) (x'.contDiff.contDiffAt.comp _ hx') hu ?_) k); change courier (x' ∘ w)=ᶠ[𝓝 0] _; rw [show courier (x' ∘ w)=_ from coach w]; simp_rw [show courier (x' ∘ v)=_ from coach v]; exact hY
 obtain ⟨ρ,hρ⟩:= Q.graph (Locations.forest s 0 T) (hx i) hn rfl rfl; let B:= startup (Locations.forest s 0 T) O (label S[n]) W p Q hn (hx i) hρ hO; have he: 0<B.paid 0:= mul_pos (pow_pos hO.scale _) (Real.exp_pos _); let v':= Stationary.orderTurn s ∘ v; have hV': ContDiffAt ℝ ω v' 0:= (Stationary.orderTurn s).contDiff.contDiffAt.comp _ hV
 rw [statements P K p O x L Q hx hO F h i v hV hn k,statements (y:=v') P K p O x L Q hx hO F h i hV' hn k]; apply congr_arg (·-_) (congr_fun _ k); trans weigh (x'∘v') (ratePlan B); -- incorrect congr_arg unification. fix
 · apply Response.balanced A (x'.contDiff.contDiffAt.comp _ hV) hp hO hn.1 ht s 0 B he (x'.contDiff.contDiffAt.comp _ hV'); rw [show courier (x'∘v)=_ from coach v, show courier (x'∘v')=_ from coach v']; funext t; change Stationary.input G n (t•Stationary.orderTurn s _)=pull _ _ (Stationary.input G n (t• v t)); rw [←map_smul]; exact (Stationary.flip_links s _).symm
 exact coherent B A (x'.contDiff.contDiffAt.comp _ hV') he hO hn.1 ht hp
end Refuge
end YM.AllOrder.Kinetic.Port
