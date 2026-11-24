import YM.OPE.Portfolio.Cup
import YM.MergeProof.North.Dolphin
/-! # A layout with epochs across one or more levels

Only to a fixed budget stop. Keep the same layout even when waking siblings. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Cadet
open Function Filter Finset Lattice RG Wilson Pressure MeasureTheory
open Push Marker Accent Menu Extra.Multi Extra.Trajectories Ribbon Source Local
open Extra.Histories PhysicalNext.Repeat Lotus GridApprox.Nil OPE.Backup Motion
open Muster MergeProof.Float
open scoped Topology BigOperators Classical
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}{H:History G}{N p m i b:ℕ}
-- E here starting at m, all regulators p,N
set_option quotPrecheck false
structure Playout (H:History G)(p m N:ℕ) (V:Type) where
   positions : ∀ i:ℕ,V→Site (H.S.side i p)
   primary : V
   tint : V→Motion
   awake:tint primary=(1,false)
   pin i: m ≤ i → i≤N → positions i primary=0
   coherent : Migrating H m p N positions

def elevation (D : Playout H p m N V) (i:ℕ) := D.positions i
variable (L:Playout H p m N V){I:Type}[Fintype I][DecidableEq I]
namespace Playout
def spectrum (t:ℕ) (x:I→ Site (H.S.side t p)) (i:V×I): Site (H.S.side t p):= affine (L.tint i.1).1 (L.positions t i.1) (x i.snd)
def skater (s:I→ℂ) (i:V×I):= scalar (L.tint i.fst) (s i.snd)
def permutation (i:V):= Equiv.swap L.primary i
lemma swapped (i:V): L.permutation i L.primary=i:= Equiv.swap_apply_left ..
def street (W:I→ℝ) := W ∘ (@Prod.snd V I)
abbrev adapted (g:∀ i:ℕ, I→ Cup (H.rep N p i)) (i:ℕ) :=g i -- not needed
variable (a:I→Site (H.S.side i p))(t:ℕ)(f:I→ Cup (H.rep N p i))(C:I→ℂ)
include L
def occupied (t:ℕ) (a:I→ Site (H.S.side i p)) : Prop:= Occupancy (L.spectrum i a) t
def cupsReg (i:ℕ)(f:I→Cup (H.rep N p i)) (b:V×I):= stepUp (L.tint b.1) (L.positions i b.1) (f b.snd).home
def cupsRes (i:ℕ)(f:I→Cup (H.rep N p i))(b:V×I):= floatUp (L.tint b.1) (L.positions i b.1) (f b.snd).leaves
lemma principal (hl:m ≤ i)(hp:i ≤ N) (b:I) : L.spectrum i a (L.primary,b)=a b:=by
    unfold spectrum; dsimp only; rw [L.awake,L.pin i hl hp]; simp [affine]
lemma attended (hl:m ≤ i)(hp:i ≤ N) (b:I) : L.cupsReg i f (L.primary,b)=(f b).home:=by unfold cupsReg; dsimp only; rw [L.awake,L.pin i hl hp]; exact Ribbons.stepid _ -- name?
lemma fleur (hl:m ≤ i)(hp:i ≤ N) (b:I) : L.cupsRes i f (L.primary,b)=(f b).leaves:=by unfold cupsRes; dsimp only; rw [L.awake,L.pin i hl hp]; exact Ribbons.floatid _
lemma pepped (b:I) : L.skater C (L.primary,b)=C b:=by unfold skater; dsimp only; rw [L.awake]; rfl
lemma rebind (hl:m ≤ i)(hp:i ≤ N) : May L.primary L.tint (L.positions i) L.permutation (L.cupsReg i f) (L.cupsRes i f) (L.skater C):=by
    intro j _; refine ⟨L.swapped j,fun b=>?_⟩; rw [L.attended f hl hp,L.fleur f hl hp,L.pepped]; exact ⟨rfl,rfl,rfl⟩
lemma roster (hl:m ≤ i)(hk:i ≤ N)(j v) : L.spectrum i a (j,v) = affine (L.tint j).1 (L.positions i j) (L.spectrum i a (L.primary,v)):=by rw [principal L a hl hk]; rfl
lemma accord (ht:m ≤ i)(hn:i<N): L.positions (i+1)=fun j=>(H.levels.clock.op i p).ratio.embed (L.positions i j):=(L.coherent.mare i ht hn).symm
lemma spectrum_step (ht:m ≤ i)(hn:i<N) {F:I→ Site (H.S.side (i+1) p)}(he:∀ j,a j=(H.levels.clock.op i p).ratio.parent (F j)): L.spectrum i a= (H.levels.clock.op i p).ratio.parent ∘ L.spectrum (i+1) F :=by
    funext v; unfold spectrum; rw [comp_apply,L.accord ht hn,he]; exact (parent_affine _ (H.S.block_odd _) _ _ _).symm
lemma representing (h:H.Selected)(hl:m ≤ i)(hp:i ≤ N) : ∃ k:V×I→ ℕ→ Config G (H.S.side i p)→ℂ,(∀ v, Dominated (k v))∧ L.cupsRes i f= fun v=> profile (H.rep N p i).activities (k v):=by
    choose k hk hK using fun b:V×I=> (f b.2).upbeat (L.tint b.1) (L.positions i b.1) ((h.represents N p i hp).good.labels.moves _ _).some; exact ⟨k,hk,funext hK⟩
-- use `gust` in next files
local notation "u'"=> L.positions i
local notation "Z"=> (H.rep N p i)
structure Market (s:Ward (Names V I))(a:I→Site (H.S.side i p))(u:I→Cup (H.rep N p i))(p':Config G (H.S.side i p)→Poly (Names V I))(W:I→ℝ)(x:ℝ) :Prop where
   width b:0<W b
   tall : Bard Z s L.primary L.tint L.permutation u' (L.spectrum i a) (L.cupsReg i u) (L.cupsRes i u) p' (W ∘ (@Prod.snd V I)) x
structure ArcMarket (s:Ward (Names V I))(a:I→Site (H.S.side i p))(u:I→Cup (H.rep N p i))(p':Config G (H.S.side i p)→Poly (Names V I))(W:I→ℝ)(δ θ:ℝ)(c:I→ℂ) :Prop where
   width b : 0<W b
   pepper b: W b*‖c b‖≤1
   tall : ∃ k:V×I→ℕ→ Config G (H.S.side i p)→ℂ,L.cupsRes i u=(fun v=> profile (H.rep N p i).activities (k v))∧ Buccaneer Z L.permutation L.tint L.primary s (L.spectrum i a) u' (L.cupsReg i u) k p' (fun b=>δ*W b) δ θ (L.skater c)
-- use widths WITHOUT δ on passage
end Playout
end YM.MergeProof.Ribbons.ManyCopies.Cadet
