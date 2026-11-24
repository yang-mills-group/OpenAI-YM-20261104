import YM.AllOrder.Floe.Motion
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
open Haiku Echo StateE Further.PhysicalPeriodLimitF933 Shingle Macrame
local notation "u'" => prePhase P K p O x L Q hx hO F h V T hV
local notation "f₀"=> Function.swap (u')
variable (i:Age) (hi:i∈T)
include hi hV
variable {μ ε:ℝ} {Γ' : ι→ℝ}
local notation "R₀"=> i.prereq T
local notation "v'" => prePhase P K p O x L Q hx hO F h V (i.prereq T) (prereq_valid V T hV i hi)
variable {A B:Snap ι G}{M:ℕ}(W' : Scores (Ad G P K) Γ σ l N (Function.swap (prePhase P K p O x L Q hx hO F h V T hV)) A)
    (X':Scores (Ad G P K) Γ' μ M N (Function.swap (prePhase P K p O x L Q hx hO F h V (i.prereq T) (prereq_valid V T hV i hi))) B)
-- Link rank at κ doesn't consume higher. Price transition through Period Moment at ALL True Calls along any χ.Min crossing leg base.
include W' X' Q hV hB hi
-- across true periods.Family.P. generation witness (other statements for closeness and VAR independent data).
def ContinuousLife (A:Side→Prop)(n:Side) : Prop:= ∃ Y:ℕ→Side, ∃ N:ℕ→ℕ,Tendsto (fun i=>(Y i).val) atTop atTop∧ (∀ i,0<N i) ∧ ∀ i,Nonempty (Macrame.Window n (Y i) (N i)) ∧ A (Y i)

variable {r k':ℕ}{ε ζ:ℝ}{G':ℕ→Atom G r} (hp: ContinuousLife (Ad G P K) n)
omit X' W' hi hB Q hV in
lemma coinsT (v:Type)[NormedAddCommGroup v][NormedSpace ℝ v][FiniteDimensional ℝ v] (s:v) (k j:ℕ): Ink.LinTest v k (fun f=> jet f j s):= by
 constructor; intro F Q hF hQ; exact jet_add hF.read.smooth.contDiffAt hQ.read.smooth.contDiffAt s; intro f x h; unfold jet; rw [iteratedFDeriv_const_smul_apply (a:=x) (x:=0) (h.read.smooth.contDiffAt.of_le le_top),_root_.smul_apply,smul_eq_mul]; ring
-- fix omit includes
variable (hN: i.e≤ N)
include hN
lemma affords (t:ι)(f:ℕ→Atom G i.r)(ha:0<b)(he:Extra.Iteration.Charged f b D)(hK:ContinuousLife (fun n=>Ad G P K n ∧ Mentor (F:=trees P K n) (ρ:= F t n) (V t i) f) n) :
   jet (snap B i.e t n-snap A i.e t n) i.r=jet (Stationary.turnSeries (m:=n) f) i.r := by
 obtain ⟨Y,d,H,hH,hκ⟩:=hK; let L0(X:Side):= u' t i.e X; let L1(X:Side):=v' t i.e X; let φ(l:ℕ):= (hκ l).1.some; let X j:= convey (φ j) (α:=E)
 ext1 y; let q(g:rule E n →ℝ):= jet g i.r y; let ψ j:ℝ:= ((d j:ℕ):ℝ)⁻¹; let t0:=dock_larger P K hB; have hp:Ink.LinTest (rule E n) (i.e+2) q:= coinsT _ y ..
 let f₁(j:ℕ):= L1 (Y j); let f₂(j:ℕ):= L0 (Y j); have hh (j:ℕ): Rank _ (i.e+2) (f₂ j):= ((W'.earns i.e t hN).fees _ ((W'.merit hN).nonneg t) W'.pos (hκ j|>.2.1)).2.1
 have hz (j:ℕ): Rank _ (i.e+2) (f₁ j):= ((X'.earns i.e t hN).fees _ ((X'.merit hN).nonneg t) X'.pos (hκ j|>.2.1)).2.1
 let M(j:ℕ):= q (ψ j • (f₁ j ∘ X j)) - q (ψ j • (f₂ j ∘ X j))
 unfold snap; rw [jet_minus (X'.plaus hN t|>.read) (W'.plaus hN t |>.read)]; apply tendsto_nhds_unique_of_eventuallyEq (f:=M) ((X'.crossover hN t t0 Y H d φ hH q hp).sub (W'.crossover hN t t0 Y H d φ hH q hp)) (tendsto_const_nhds) _
 apply Eventually.of_forall; intro j; let y':= Y j; let ℓ:=X j; have he' : M j= ψ j*q ((f₁ j-f₂ j) ∘ ℓ):= by
    let g0:=f₂ j ∘ ℓ; let g1:= f₁ j ∘ ℓ; have hv0:=(hh j).lead (X j); have hv1:=(hz j).lead (X j); unfold M; rw [hp.scale _ _ hv0,hp.scale _ _ hv1,← mul_sub]; rw [show (f₁ j-f₂ j) ∘ ℓ=(f₁ j ∘ ℓ)-(f₂ j ∘ ℓ) from rfl]; apply congr_arg; rw [show q ((f₁ j ∘ ℓ) - (f₂ j ∘ ℓ))=q (f₁ j ∘ ℓ)-q (f₂ j ∘ ℓ) from congr_fun (jet_minus hv1.read hv0.read _) y]
 rw [he']; unfold q; rw [Kinetic.pivot (X j) (f₁ j-f₂ j) y ((Plausible.sub (hz j).read (hh j).read).smooth.contDiffAt)]; have hx':= (hκ j).2
 rw [show jet _ _ _= _ from centersH P K p O x L Q hB hx hO F h V T hV Γ i hi W' X' hx'.1 t f hx'.2 (Stationary.turns_analytic f ha he) (X j y),variet i.r n y' (φ j) f ha he]; exact inv_mul_cancel_left₀ (by exact_mod_cast (hH j).ne') _
end Aero
end YM.AllOrder.Floe
