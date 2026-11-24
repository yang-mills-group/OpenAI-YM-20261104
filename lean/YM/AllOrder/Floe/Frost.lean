import YM.AllOrder.Floe.Happen
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
namespace Aero
open Haiku Ink.Echo Pace
local notation "u'" => prePhase P K p O x L Q hx hO F h V T hV
local notation "F'"=>Function.swap (u')
variable {M:Snap ι G}(A:Scores (Ad G P K) Γ σ l N (Function.swap (prePhase P K p O x L Q hx hO F h V T hV)) M)
local notation "R"=> topiary P K p O x L Q hx hO F h
lemma haze (i:ι)(n:Side)(hn:Ad G P K n)(hk:k<3): u' i k n=R k i n:= by
 unfold prePhase topiary galaxy; rw [dif_pos hn,dif_pos hn]; apply congr_arg (·-_) ; let A:= D[i,n,hn]; let T':= T[n]; let C:= augment T' (V i) ∅ A (legal_less (V i) T (hV i) _ (empty_subset _)); -- remove invalid.L.H witness defined by less
 have hx : distilled (augment T[n] (V i) T A (hV i)) k=distilled C k:= by refine orient _ _ T _ (hV i) _ (empty_subset _) (fun i hi _=> i.senior) hk
 rw [hx]; have he: C.high=A.high:= (by simp [C,augment,venue]); have he' : distilled C k = distilled A k:= by change connected (castle _ _ A.pay.steer) volume (Impulse (fderiv ℝ A.quiet 0) C.high _) k=_; rw [he]; rfl
 rw [he']
variable {B:ℕ→ι→Ink.Field (Coarse G)} (H: Kinetic.Port.Presence P K p O x L Q hx hO F h B)(i:ι) (hk:k≤ N) (hK:k<3)
local notation "H'"=> dock_larger P K hB
include hk hK A H hB
lemma affair(n:Side) : ∀ i:ι,snap M k i n=snap B k i n:= by
 intro i; obtain ⟨b,C,D,h'⟩:=H.fee k hk; funext y; let w:=amplify n; let K' i:= (i+1)^4; let h:= limitless n; refine tendsto_nhds_unique_of_eventuallyEq (A.crossover hk i (dock_larger P K hB) w h K' (Ink.Echo.arm n) (fun i=>by unfold K'; positivity) _ (Ink.LinTest.eval _ y)) (Ink.Echo.transported (Ink.Echo.arm n) (h'.awake i) (Ink.Echo.scaleLean h'.story i) h h'.berth (dock_larger P K hB) (fun i=>by positivity) _ (Ink.LinTest.eval _ y)) ?_
 obtain ⟨d,H⟩:=dock_larger P K hB; filter_upwards [h.eventually (eventually_ge_atTop d)] with j hj; let g : (rule E (w j)→ℝ)→ℝ:=fun p=> (↑(K' j):ℝ)⁻¹*p (convey (arm n j) y); exact congr_arg g (haze P K p O x L Q hx hO F _ V T hV i (w j) (H _ hj) hK)
omit hk hK H
variable {δ e θ:ℝ} (q:Clip)(y:ι→PathData G)(Λ':ι→ℝ)(hy:∀ i,(y i).Bounds q δ e (Λ' i))(T0:ι→Towers P.L)(α:ι→ℝ)(hd:∀ i n,Channels P K p O x F q y α i n) (g:G.Simple) (hN:2≤N)
local notation "M₀"=> fun i k n=>snap M k i n
include hN hd g T0 hy
lemma cloudy : Haiku.Coat.strict ((M₀)+ fun i=> Coat.Stipend q (y i) (α i)) 3:=by
 obtain ⟨H,h⟩:= Kinetic.Port.screen P K p O x L Q hB hx hO F h; have hp:=clears P K p O x L Q hB hx hO F _ q y α Λ' hy T0 h hd hN g; intro i n k hk; let m i:= Coat.Stipend q (y i) (α i); let M' k i n:=snap H k i n; have hv:= hp i n k hk
 change Constant (snap M k i n + m i k n); rw [affair P K p O x L Q hB hx hO F _ V T hV Γ A h (by omega) hk n i]; exact hv
end Aero
end YM.AllOrder.Floe
