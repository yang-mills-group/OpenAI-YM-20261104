import YM.AllOrder.Floe.Stars
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
local notation "R"=> heat P K p O x L Q hx hO F h V T
open Kinetic
open Extra.Iteration
namespace Aero
open Haiku Echo Further.PhysicalPeriodLimitF933 Shingle Macrame
local notation "u'" => prePhase P K p O x L Q hx hO F h V T hV
local notation "u"=> I₀
-- Explicit inst PHeight
abbrev Snap (ι:Type)(G:Gauge) := ℕ → ι→Ink.Field (Coarse G)
def snap (S:Snap ι G)(j:ℕ):ι→ Ink.Money.Bills (Coarse G):= fun i n=> (S j i).table n
structure Scores (Ad:Side→Prop)(L:ι→ℝ)(σ:ℝ)(l N:ℕ) (F:ℕ→ι→Ink.Money.Bills (Coarse G))(Y:Snap ι G): Type where
 a : ℕ→ι→ℝ
 b : ℕ→ι→Side→ℝ
 pos:0<σ
 pay(k:ℕ)(hk:k≤N): CreditF L l (a k) ∧ Weight L l (b k)
 earns(k:ℕ)(i:ι) (hk:k≤N): Pert Ad (F k i) (Y k i) σ (a k i) (b k i) (k+2)
local notation "f₀"=>chant b N (3*N)
local notation "F'"=>Function.swap (u')
open Extra.Iteration
abbrev request (b:ℝ)(Γ:ι→ℝ)(l N:ℕ)(V:ι→Layout G)(j:Age): Prop:= ∃ f:ι→ℝ,∃ s,0<s∧CreditF Γ l f∧b ≤ leaseF s N ∧ ∀ i, Charged (V i j) s (f i)
variable (hh:∀ j∈T,Aero.request b Γ l N V j) -- σ enough
section congress
include Q hL ht hs hh hV A hB
lemma solo : ∃ M:Snap ι G,Nonempty (Scores I₀ Γ f₀ (diet l N) N (F') M):= by
 have hv k (hk:k≤N):= awakes P K p O x L Q hB hx hO F h V T hV Γ A ht hs hL hh hk
 choose M z D hM H h' using fun k (hk:k ≤ N) => (show License _ _ _ _ _ _ from hv _ hk)
 let x'(k:ℕ):= if h:k≤N then M k h else M 0 (Nat.zero_le N); let a(k:ℕ):= if h:k≤N then z k h else 0; let d(k:ℕ):= if h:k≤N then D k h else 0
 refine ⟨x',⟨a,d,soprano N ht _,fun k hk=> ⟨by rw [show a k= _ from (show a k=z k hk from dif_pos hk)]; exact hM k hk, by rw [show d k=D k hk from dif_pos hk]; exact H k hk⟩,fun k i hk=>?_⟩⟩
 unfold x' a d; rw [dif_pos hk,dif_pos hk,dif_pos hk]; exact h' k hk i
end congress
namespace Scores
variable {g:Snap ι G}{u₀ : Side→Prop}{C:ℕ→ι→Ink.Money.Bills (Coarse G)}{Γ} (H0:Scores u₀ Γ σ l N C g) (hk:k≤N) (y:ι) (h0:Often u₀)
include hk H0
lemma merit : Weight Γ l (H0.b k) := (H0.pay k hk).2
lemma plaus : Rank (rule E n) (k+2) ((g k y).table n):= ((H0.earns k y hk).1.binding (n:=n) H0.pos.le).2.1
include h0 in
lemma crossover (S:ℕ→Side)(hx:Tendsto (fun i=> (S i).val) atTop atTop) (m:ℕ→ℕ)(X:∀ i,Macrame.Window n (S i) (m i)) (hr:∀ i,0 < m i) (χ:(rule (Coarse G) n→ℝ)→ℝ)(hc:LinTest _ (k+2) χ): Tendsto (fun i=>χ ((↑(m i):ℝ)⁻¹ • (C k y (S i) ∘ convey (X i)))) atTop (𝓝 (χ ((g k y).table n))) := transported X (H0.earns k y hk) (scaleLean (merit H0 hk).grade y) hx H0.pos h0 hr _ hc
end Scores
variable {i:ι}{y:Snap ι G}{D':ℕ} {G₀:ι→ℝ}(H0:Scores (Ad G P K) G₀ σ D' N (swap (prePhase P K p O x L Q hx hO F h V T hV)) y) (hk:k≤N)
include H0 hk hB Q hV
lemma reign : Etiquette (fun k=> snap y k i) n k:= by
    exact Pump.armament (D:=fun _=>σ) (K:=fun z=> H0.b z i) (P:=fun z=> H0.a z i) (A:=fun k=>F' k i) (B:=fun k=> y k i) (fun k hk=>H0.earns k i hk) (fun k hk=> Ink.Echo.scaleLean (H0.merit hk).grade i) (fun _ _=>H0.pos) (dock_larger P K hB) (fun n k hn _ => spectacle P K p O x L Q hx hO F h V T hV k i n hn) n hk
end Aero
end YM.AllOrder.Floe
