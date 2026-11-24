import YM.AllOrder.Haiku.Corona
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
open AllOrder.Haiku AllOrder.Haiku.Coat Further.PhysicalPeriodLimitF933 Shingle Macrame
variable (q:Clip) (u:ι→PathData G) (g:ι→ℝ) {b C' :ℝ}(V:ι→ℝ)(H:∀ i,(u i).Bounds q b C' (V i)) (W: ι → Towers P.L) -- namespace?
local notation "E0"=> rule (Coarse G) n
local notation "H0"=> home P K p O x L Q hx hO F h q u g
open Set
local notation "E'"=> fun i:ι=> Stipend q (u i) (g i)
def unpop (ι:Type)(G:Gauge) : Repertoire ι G:= fun j k v=> Stationary.issue (t:=k.val+1) 0
local notation "U₀"=> unpop ι G
lemma no_age (G:Gauge)(k:ℕ)(i:Fin (k+1)): Curled L (unpop ι G k i):= by
   refine ⟨1,zero_lt_one,(fun _=>0),⟨gia _ le_rfl,fun v=>?_⟩⟩; constructor <;> simp [unpop,SumBudget,Atom.budget,Atom.magnitude,Stationary.issue,Stationary.artery,Atom.Invariant,Atom.poly]
lemma unpop_trade (v:ι)(k:ℕ)(i:Fin (k+1))(p:ℕ)(n:Side): trade k ((U₀ k i v)) p n=0:=by
 unfold trade; have he : Stationary.turnSeries (U₀ k i v) (m:=n) = 0 := by ext x; simp [Stationary.turnSeries,Precision.uncut,Patch.average, unpop, Stationary.issue,Stationary.artery, Atom.unmasked, Atom.poly]
 split; rw [he]; ext1 i; simp [jet]; rfl
lemma vapor (ι:Type)[Nonempty ι](G:Gauge)(k:ℕ): crowd (unpop ι G) k=0:= by unfold crowd; apply Finset.sum_eq_zero; intro a ha; unfold reel; apply Finset.sum_eq_zero; intro i _; funext v p n; exact unpop_trade ..
-- all costs after-L. witnesses for choices.
include W hB H
lemma flux (hV:Grade L V)(hG:Grade L (fun i=>|g i|))(hk:2≤N)(hu:G.Simple)(hw:∀ i n,Channels P K p O x F q u g i n) : ∃ (M:ℕ→ι→ Ink.Field E) (T:Repertoire ι G),
  Presence P K p O x L Q hx hO F h M ∧ Spliced L ((fun i k n=>(M k i).table n)+fun i=> Stipend q (u i) (g i)) T (N+1) ∧ ∀ i<3,T i= (unpop ι G i):= by
  obtain ⟨M,hM⟩:= screen P K p O x L Q hB hx hO F h; have h' := clears P K p O x L Q hB hx hO F h q u g V H W hM hw hk hu; let R:= (fun i k n=>(M k i).table n)+ E'; let T₀:= unpop ι G
  let HE:memoir L R N:= memoir_plus hM.sentiment (caps q u L V g hV H hG hu N); have he(k:ℕ)(hc:3≤k)(hp:k≤N+1): ∃ T : Repertoire ι G,Spliced L R T k ∧ ∀ i<3,T i=T₀ i:= by
     induction k,hc using Nat.le_induction with
     | base=> exact ⟨T₀, ⟨fun v hv=> no_age L G v, by rw [show crowd T₀ 3=_ from vapor ι G 3,sub_zero]; exact h'⟩, fun _ _=> rfl⟩
     | succ k H ih=> obtain ⟨T,hT,h⟩:= ih (by omega); obtain ⟨B,hB,h'⟩:= hT.up (by omega) HE hu; exact ⟨B,hB,fun j hj=>(h' j (by omega)).trans (h j hj)⟩
  obtain ⟨T,Hx,hκ⟩:=he (N+1) (by omega) le_rfl; exact ⟨M,T,hM,Hx,hκ⟩
end YM.AllOrder.Kinetic.Port
