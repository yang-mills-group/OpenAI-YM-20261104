import YM.OPE.Sweep.Ballet
import YM.OPE.Loom.Reprice
/-!
# Across a thin length span before capture with recharged budget on separated steps (adapted from Sweep.Ballet)
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Next.Rank Station Corona Next.Rank.Spindle Cells
open scoped Topology BigOperators Classical
variable {Z V I J : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
  [Fintype J][DecidableEq J]{G:Gauge}{n:Side}
variable (C:Family G)(N p m j d:ℕ)
    {W:Bid.Worth}{u ψ φ δ σ χ x:ℕ→ℝ}{ζ:ℕ→ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
set_option quotPrecheck false
local notation "H" => C.path
local notation "Y" => C.path.levels
local notation "P'" => C.path.levels.budget
local notation "R" => C.path.rep N p
variable (E:∀ i:ℕ,V→Site (C.side i p))(o:∀ i:ℕ,V×I→Site (C.side i p))(P:V→ Motion)(v:V)(B:V→Equiv.Perm V)
    (i₀:I) (J':V→ℝ)(t:I→ℕ) (s: (i:I)→ C.label (t i)) (q:I→Motion)(a:I→ℝ) (F:V×I→ Config G (C.side N p)→ℂ) {α z:ℝ}{l:ℕ}(hm:m+1≤j)(hj:j<N)
local notation "h!"=> lt_of_lt_of_le (Nat.lt_succ_self m) (le_trans hm hj.le)
local notation "F!"=> (birth (Names V I) (R N) F)
local notation "X"=> (fun i:I=>δ j*(φ j*a i))
local notation "Y'"=> ((Y).budget (m+1))
local notation "T'"=> (Labels.frames G).level d
local notation "U" => Next.Foundations.localSection G d
local notation "Z'"=> (C.S.a (m+1)^d*(x m*(4*(1/z))))
variable (h:C.Makes)(hh:Scrim C W u ψ φ δ ζ r D)(hP: C.ref d ≤ m)(he: SwornClusterCuts C (μ:=D) (δ:=δ) (r:=r) (C.ref d) d χ δ x)
include h hh hP he hm hj
set_option maxHeartbeats 500000 in
lemma twine
    (ht:∀ i,C.ref (t i) ≤ j)(hM:∀ i,a i*Next.Rank.Spindle.paid C (t i) j N p (s i) ≤ ζ (t i) j)(hw:∀ i,0<a i)
    (hr:Migrating H m p N E)(hv:P v=(1,false))(hf:E m v=0)(h₀:∀ i,o (m+1) (i,i₀)=E (m+1) i)(hx:∀ i,i≠v→B i v=i)
    (hA:∀ k:ℕ,m+1 ≤ k→ k ≤ N→ Collar (o k) v (E k) P)
    (hE:Migrating H j p N o)(hc:∀ k:ℕ,m+1 ≤ k→ k<j→(C.path.levels.clock.op k p).ratio.parent ∘ o (k+1)=o k)
    (hK: Edition.Spaced (P' j).B (o j))
    (hS:∀ i,i≠v→∀ b:I,F (i,b)=stepUp (P i) (E N i) (F (v,b))) (hY:∀ i,F (v,i)=MergeProof.item C (t i) N p (s i) (fun m'=>o m' (v,i)) (q i))
    (hX: Integrable (F!) (prior G _))
    (hω:Occupancy (E m) (r m))(hω':Occupancy (E (m+1)) (r m))
    (a' : ℕ → I→ℝ) (hU : a' j = fun i=> δ j*(φ j*a i)/8)
    (hX' : ∀ i, m+1 ≤ i→ i≤j→∀ l,0<a' i l)
    (hn : ∀ i,m+1 ≤ i→ i<j→ Occupancy (o i) (r i))
    (hPeg : ∀ i,m+1 ≤ i→ i<j→ Repegs (o i) (P' i).B (fun l:V×I=>δ i*(a' (i+1) ∘ Prod.snd) l) (a' i ∘ Prod.snd) (1/2) 1 (Names V I))
    (hw' : ∀ i,m+1 ≤ i→i<j→∀ l,(6*((C.S.block i).val:ℝ))*a' i l ≤ a' (i+1) l) (hNe:m+1 < j)
    (hΩ:∀ i:V×I, coverNumber (P' (m+1)).B ({o (m+1) (i.1,i₀),o (m+1) i}:Support _) ≤ l)
    (hz:0<z)(hy:z ≤ cashIn H δ (Fintype.card I) l (m+1) (a' (m+1)))
    (hJ: ∀ i,0<J' i)(hε:∀ i,J' i ≤ δ m*(z/(16*x m))) :
    ∃ Q₀: Coefficient T' (C.S.side m p), Q₀.Format 0 (Next.Foundations.hol G) (R m) ∧ Q₀.remBound 0 (R m) (kappa H m) Z' ∧ (T').coeffSize Q₀.x ≤ Z' ∧
       Served (R m) (fun i=> radiant (alto H m d) (P i) (E m i) (Q₀.exponentialEntry 0 U (R m))) (fun i=> sunny (R m) Q₀.forced (P i) (E m i) (alto H m d)) (gust H N p N (birth (Bud V) (R N) (fun y c=>∏ i,F (y,i) c)) m (h!).le) (E m) J' (P' m).supportExponent 1 :=by
    obtain ⟨σ,hq⟩:=he.city; let r':= C.ref d; let A:= Fintype.card I; have hZ:= hP.trans m.le_succ; have hZU:= hZ.trans hm; have hZ': 0 < A:= Fintype.card_pos_iff.mpr ⟨i₀⟩
    have hB : ∀ k≥r', ClusterPars H δ χ r k := fun k hk=>⟨he.crisp k hk, he.funs k hk,he.bars k hk⟩
    have hF' : Brine C.path (C.ref d) δ φ:=⟨fun i _=> hh.costs.stay.water _ (Nat.zero_le i),fun i _=> hh.costs.stay.mint _ (Nat.zero_le i),fun i _=> hh.costs.stay.split _ (Nat.zero_le i),fun i _=> hh.costs.stay.support _ (Nat.zero_le i)⟩
    obtain ⟨-,hL,-⟩:= (hh.costs.heights d (C.ref d) N p le_rfl (hZU.trans hj.le)).choose_spec
    obtain ⟨f,g,K,hg,hL',hD⟩:= upper C t N j p W u ψ φ δ ζ r D s o q a v E P B F σ χ hh.costs h hq hZU ht hj (fun i=>(Occupancy.of_injective (Edition.injected _ _ (P' j|>.B_pos) hK) i).trans (hh.back _)) hE ⟨fun _ _ i _ j _=> hK i j⟩ hM hw ⟨fun i hi=>hr.mare i (by omega)⟩ hx (fun i hi hp=>hA i (hm.trans hi) hp) hS hY hX
    have hA':Arsenal (R j):=by
       cases j with
       | zero=> omega
       | succ j=> exact (hq.moon N p j (by omega) (by omega)).1.contact
    let Q:= gust H N p N (F!); have H0 : Live H N p E o P v B Q δ χ j hj.le (a' j) f:=by rw [hU]; exact Under.solved h.wilson hq hZU hj.le (fun i=> (congrFun hU i) ▸ hX' j hm le_rfl i) (he.crisp j hZU) hA' (W:=X) hD hg hL' (fun i=> (show 8*(δ j*(φ j*a i)/8) = _ from (by ring)).le)
    have hV' (i:ℕ) (hl:m+1 ≤ i) (hJ:i≤j) : Live H N p E o P v B Q δ χ i (hJ.trans hj.le) (a' i) f:=by
       induction hJ using Nat.decreasingInduction with
       | self=> exact H0
       | of_succ i hi ih=>
          let Λ := ((C.path.levels.clock.op i p).ratio)
          have ht : i < N:= hi.trans hj
          have hp:Occupancy (o i) (r i):= hn _ hl hi
          have hN:Occupancy (o (i+1)) (r i):= by
             intro v; apply le_trans (Finset.card_le_card _) (hp (Λ.parent v)); intro j hj;
             apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _,?_⟩; rw [← hc _ hl hi]; simpa only [Function.comp_apply] using congr_arg Λ.parent (Finset.mem_filter.mp hj).2
          have hx(i:ℕ): 1 ≤6*((C.S.block i).val:ℝ) := by linarith only [show (2:ℝ) ≤ (C.S.block i).val from size_enough C.path i]
          exact (ih (hl.trans i.le_succ)).toUnder.comp_step h.wilson hq (hZ.trans hl) ht (hr.mare i (le_trans (m.le_succ) hl) ht|>.symm) (fun x hx k=> hA _ (hl.trans i.le_succ) ht x hx k) (gust_step H _ _ _ _ ht) (gust_live H _ _ _ _ hX _) (hc _ hl hi) hN hp (he.brings i (hZ.trans hl) N p ht|>.1) (hx i) (hPeg _ hl hi) (hw' i hl hi) (hX' i hl hi.le)
    rw [gust_step _ _ _ _ _ h!,ripe i₀ (by omega) hX]
    exact Live.winter h.wilson hq i₀ h! (hV' _ le_rfl hm) hP hf (hr.mare m le_rfl h!|>.symm) h₀ hv hω hω' (hn _ le_rfl hNe) (hA _ le_rfl h!) hZ' le_rfl (hB (m+1) hZ) (gust_live H _ _ _ _ hX _) hΩ (he.brings m hP N p h!|>.2) (he.dollars m hP) hJ hε hz hy
end YM.MergeProof.Ribbons.ManyCopies
