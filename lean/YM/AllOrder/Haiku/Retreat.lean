import YM.AllOrder.Haiku.Terrace
import YM.AllOrder.Haiku.Route
/-!
# Characterization: arbitrary finite-order pure step crystallizes real costed curvature rep

Perturbative series independent of real activity norms. Later floors before choosing
one real Mesh n rep. A priori not giving same reps per horizon automatically.
-/
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
open AllOrder.Haiku
-- one post seal at any N. Monotone augmentation in Q & Lodge by splicing; F frames interchangeable. ∃ Ghost plan ready at all n. 
structure Chords (b:ℝ) (C':ι→ℝ)(t:ι→Side→ℝ)(k:ℕ)(U:ι→ Ink.Field (Coarse G)): Prop where
 berth:0<b
 grant:Grade L C'
 story:Pay L t
 awake:∀ i,Pert (Ad G P K) (topiary P K p O x L Q hx hO F h k i) (U i) b (C' i) (t i) (k+2)

structure Presence (M:ℕ→ι→ Ink.Field E): Prop where
 fee (k : ℕ) (hk:k ≤ N) : ∃ b C' t, Chords P K p O x L Q hx hO F h b C' t k (M k)
 sentiment : Coat.memoir L (fun i k n=> (M k i).table n) N

include hB
lemma screen : ∃ M:ℕ→ ι→ Ink.Field (Coarse G), Presence P K p O x L Q hx hO F h M:= by
 obtain ⟨A⟩:= offers P K p x L Q hB hx; choose a ha A ha' using fun k (hk:k≤N)=>prism_at P K p O x L Q hB hx hO F h A hk -- choose all flattened auto? syntax missing explicit nested Exists
 let X k (x:ι):Ink.Field E:= if hk:k ≤ N then A k hk x else Ink.Field.void E -- conflict A Aspen
 choose t D he hu h' using ha'; let τ(k:ℕ) := if hk:k ≤ N then (a k hk,t k hk,D k hk) else (1,0,0)
 have hh(k) (hk:k≤N): Chords P K p O x L Q hx hO F h (τ k).1 (τ k).2.1 (τ k).2.2 k (X k):= by rw [show X k=A k hk from funext fun i=> dif_pos hk]; unfold τ; rw [dif_pos hk]; exact ⟨ha k hk, he k hk,hu k hk,h' k hk⟩
 refine ⟨X,⟨fun k hk=>⟨_,_,_,hh k hk⟩,fun k hk i n=> ?_,fun k hk p=> ?_ ⟩⟩; -- structure constructor incorrect conjunction
 · have hx' := fun k hk v=>(hh k hk).awake v
   have hv(i:ι):= Pump.armament (A:=fun k=>topiary P K p O x L Q hx hO F h k i) (B:=fun k=> X k i) (D:=fun k=>(τ k).1) (P:=fun k=>(τ k).2.1 i) (K:=fun k=>(τ k).2.2 i) (fun k hk=> hx' k hk i) (fun k hk=> Ink.Echo.scaleLean (Λ:=L) ((hh k hk).story) i) (fun k hk=>(hh k hk).berth) (dock_larger P K hB) (fun c k hc _=> Refuge.respectful P K p O x L Q hx hO F h k i c hc) n hk
   exact ⟨((hx' k hk i).1.binding (n:=n) ((hh k hk).berth.le)).2.1,hv i⟩
 exact Coat.Ready.path (hh k hk).grant (hh k hk).berth (fun i=> ((hh k hk).awake i).1) _

/-- Splice *infinitely supported period-compatible* Laurent charges (hyp finite order N).
Widths chosen after L cost (order and perturb accuracy explicit), Λ only receipt variable. -/
lemma new_script (hG:G.Simple): ∃ (M:ℕ→ι→Ink.Field E)(T:Coat.Repertoire ι G), Presence P K p O x L Q hx hO F h M ∧ Coat.Spliced L (fun i k n=> (M k i).table n) T (N+1):= by
 obtain ⟨y,hy⟩:=screen P K p O x L Q hB hx hO F h; obtain ⟨T,ht⟩:=Coat.onRamp hy.sentiment hG; exact ⟨y,T,hy, ht⟩
end YM.AllOrder.Kinetic.Port
