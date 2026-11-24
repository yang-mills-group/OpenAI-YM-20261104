import YM.AllOrder.Floe.Sign
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe.Step
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration Pace Aero StateE
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G:Gauge}{ι:Type}[Nonempty ι]{a b C D Z Λ ε σ Ω:ℝ}{k r m n N l:ℕ}{j:Side}
open Rent
variable (Γ:ι→ℝ) {q:Clip} {R:ι→PathData G}{L:ι→ℝ}(h : ∀ i,(R i).Bounds q a C (L i)) (g:G.Simple) {s:Fees} (t:Age) {T: Age→ ι→ℝ} {H:ι→Scene G}(p:Age→ℕ)(α:ι→ℝ)
local notation "p≀"=> fun (i:Age)=> gateE (p i) N
-- issued Life cost. torus weights true Δ demand incoming direct. State.V.Cred.H= strict leaps.Largest.Z. Panel.
structure Aligned (p:Age→ℕ)(N:ℕ):Prop where
 firstF i: 1≤p i
 fareF {i j}: Age.before i j → gateE (p i) N +1≤p j
local notation "X"=> Age.scope (k+2)
local notation "Z"=> Age.scope (rank k)
structure Sustained (N:ℕ) (s:Fees)(H:ι→Scene G)(R:ι→PathData G)(T:Age→ι→ℝ)(d:ℕ)(q:Clip)(V:ι→Layout G)(Q:ι→ Coin): Prop where
 rents :∀ i∈Age.scope (d+2),∃ f:ι→ℝ, CreditF Γ (gateE (p i) N) f ∧ ∀ j, Quoted (V j i) (s i) (T i j+f j)
 income :∀ k<d,Pace.Cost Γ (gateE (p (bottom k)) N) (fun i=> Q i (rank k))
 due :∀ i,Pace.Earn (Q i) (α i)
 dormant : ∀ i,∀ j,d+3 ≤ j→ Q i j=0 -- typo k not d
 calls : Haiku.Coat.strict (fun i=> ask q (R i) (H i) (Q i) (Age.scope (d+2)) (V i)) (d+3)
variable {σ:Fees}{V:ι→Layout G}{Q:ι→ Coin} (h0:0≤Ω) (hh : ∀ i∈ Age.scope N,Rent.Spirit Γ q R H s i a C (σ i) Ω (p i) N (T i))
variable (A : Sustained Γ p α N s H R T k q V Q) (hp: ∀ i,0<s i)(hC: CreditF Γ 1 L)(hg:Aligned p N)(hT:∀ i∈Age.scope N,CreditF Γ (gateE (p i) N+1) (T i))(hα:Pace.Cost Γ 1 α)(hV:∀ i, Pace.Valid (H i) N)
-- issue maybe typo.
include hp A
lemma supports (i:ι) : Legal X (V i) := by
 refine ⟨fun j hj=> ?_,fun j hj=> ?_⟩
 all_goals obtain ⟨f,_,h⟩:= A.rents j hj
 · exact ⟨s j, T j i+f i,hp j,(h i).pay⟩
 exact (h i).symm
include hT hg h h0 hh hV hC hα g
local notation "L'"=> upto k
variable (hτ: Step.rank k ≤ N)
include hτ
lemma obtain_call (z:Age)(ht:z∈upto k) : ∃ (f:ι→ℕ→Atom G z.r) (α:ι→ℝ) (C:ι→ℝ), Pace.Cost Γ (gateE (p z) N) α ∧ CreditF Γ (gateE (p z) N) C ∧∀ i, Quoted (f i) (s z) (T z i+C i) ∧ Step.Beam (tape (k+2)) (V i) q (R i) (H i) (Q i) z.e z.r (f i) (α i):= by
 let r:= z.e; have ht': z.e=Step.rank k:= born_height z ht; have hk:z∈ Age.scope N:=Age.in_scope.mpr (ht'.trans_le hτ); have hc z'(h:z'∈X):= let i:=z'; (show i.e < z.e from (earlier z' h).trans_eq ht'.symm)
 have hv:∀ v≤N,Pace.Cost Γ (p z) (fun i=> Q i v):= by
   intro v hp; rcases v with _|v; · rw [show (fun i=> Q i 0)=fun i=>0 from funext fun i=> (A.due i).1]; exact Pace.Cost.fixed _
   rcases v with _|v; · rw [show (fun i=> Q i (0+1))=fun i=>0 from funext fun i=> (A.due i).2.1]; exact Pace.Cost.fixed _
   rcases v with _|v; · rw [show (fun i=> Q i (0+1+1))=α from funext fun i=> (A.due i).2.2]; exact hα.up (hg.firstF z)
   by_cases h': k ≤ v; · rw [show (fun i=> Q i (v+1+1+1))= fun i=>0 from funext fun i=> A.dormant i _ (by omega)]; exact Pace.Cost.fixed _
   have hh: Age.before (bottom v) z:= Or.inl (by change rank v<_; rw [ht']; unfold Step.rank; omega); have he:= hg.fareF hh; exact (A.income _ (Nat.lt_of_not_ge h')).up (by omega)
 apply pawns Γ h g z _ h0 («X»:=X) hc (hh _ hk) (supports Γ p α A hp) hp (by rw [ht']; exact A.calls) hV _ hv (hC.up (hg.firstF z)) (ht'.trans_le hτ)
 intro w hw; obtain ⟨f,hF,H⟩:=A.rents _ hw; have hd:= hg.fareF (i:=w) (j:=z) (Or.inl (hc w hw)); exact ⟨_,((hT w (Age.in_scope.mpr ((hc w hw).le.trans (ht'.trans_le hτ)))).up hd).add (hF.up (by omega)),fun i=> (H i).pay⟩
end YM.AllOrder.Floe.Step
