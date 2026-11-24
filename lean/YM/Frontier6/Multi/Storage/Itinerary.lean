import YM.Frontier6.Multi.Storage.Warranty

/-! Walking coarsewards, shrinking only at decreasing-arity stops. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Canopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V C O:Type}[Fintype V][DecidableEq V][Fintype O][DecidableEq O][Fintype C][DecidableEq C]
variable {G:Gauge}
section
variable (H:History G)(δ:ℕ→ℝ)(r:ℕ→ℕ)(D:∀ N p i,i<N→GaugeDoor (H.rep N p (i+1)) (H.rep N p i))
variable {N p i:ℕ}(σ χ:ℕ→ℝ)(v:V) (P:V→Motion)(B:V→Equiv.Perm V)
   (E:∀ i:ℕ,V→Site (H.S.side i p))(o:∀ i:ℕ,Live V O→Site (H.S.side i p))
set_option quotPrecheck false
local notation "P'"=> H.levels.budget
local notation "R"=> H.rep N p
local notation "X"=> (Now V O)
variable (h:H.Selected)(μ:ℕ)(hr:Thor H δ r D σ χ μ) (w0:ℝ)
local notation "c!"=>fun i:ℕ=>Salt.scent (P' i).B (r i) ((P' i).supportExponent+1/2) 1 (δ i) 1 (χ i)
local notation "n"=> Fintype.card O
variable (F:Config G (H.S.side N p)→Poly (Now V O))
local notation "Y"=> gust H N p N F
variable (root:O){π:Concentrate O C} (ε:ℝ) {m j:ℕ}
structure Storage (F:Config G (H.S.side N p)→Poly (Now V O))(j i:ℕ)(hi:i ≤ N)(ε w0:ℝ): Prop where
   pick : ∃ (C':Type)(_ : Fintype C')(_ : DecidableEq C') (π:Concentrate O C') (root' : C')(w:C'→ℝ),
       π.seat root'=root ∧ warrant H.S ε (Fintype.card O-Fintype.card C') (Fintype.card O) j i w0 ≤ total w ∧ Stores H v P B E (fun i=>o i ∘ (batt π).seat) i (N:=N) ((batt π).reap ∘ gust H N p N F i hi) w

structure Travel (x k:ℕ) (μ:ℕ)(ε:ℝ) (N:ℕ): Prop where
   advance : μ ≤ x
   leave (i:ℕ) : x < i → i < k →∀ h:i<N, MergeProof.Float.Runs (D N p i h) (H.levels.clock.op i p) (6*((H.S.block i).val:ℝ))
   books (i:ℕ) : x < i → i < k → 1 ≤ δ i * mintK (H.levels.budget i).B ∧ 8 ≤ (H.levels.budget i).B
   shelf (i:ℕ): x < i→ i< k→ (((H.levels.budget i).B+(H.levels.budget i).B+1:ℕ):ℝ)^4 * c! i ≤ 1/2 ∧ Real.exp (c! i)-1 ≤ 1
   bill : 0 < ε ∧ ε ≤ 1 ∧ ∀ i,x < i→ i< k → ε ≤ restoreRate H.levels δ i
   back (i:ℕ) : x ≤ i→ i< k→(H.levels.clock.op i p).ratio.embed ∘ E i=E (i+1)
   stalk (i:ℕ) : x < i→ i< k→(H.levels.clock.op i p).ratio.parent ∘ o (i+1)=o i
   shaped (i:ℕ): x < i→ i ≤ k→ Shaped v P (E i) (o i)
   clear (i:ℕ) : x < i → i ≤ k → Between (o i) ((H.levels.budget i).B)
   exchange (j:V): j≠v→ B j v=j
   ceiling (i:ℕ): x ≤ i→ Fintype.card O ≤ r i
local notation "S"=>Storage H v P B E o root F
variable (ht:Travel H δ r D χ v P B E o m j μ ε N)
local notation "b!"=>fun (π:Concentrate O C)(i:ℕ)=>o i ∘ (batt π).seat
include h hr ht
lemma dawn {hi:i < N}(hw:m < i)(hj:i<j) (w:C→ℝ)
  (hW:Stores H v P B E (b! π) (i+1) (N:=N) ((batt π).reap ∘ Y (i+1) hi) w)(hF:Integrable F (prior G _)) :
   Atlas H v P B E (b! π) δ χ i (N:=N) ((batt π).reap ∘ Y i hi.le) (fun j=>δ i*w j) ∧ (Daylight v (b! π i) ((H.levels.budget i).B) → Stores H v P B E (b! π) i (N:=N) ((batt π).reap ∘ Y i hi.le) (pinion H.S i w)):=by
   let o':=b! π; have hv : μ < i := lt_of_le_of_lt ht.advance hw; have ha (k)(hf:m<k)(he:k≤j):= (ht.clear k hf he).seats _ _ π
   have hE(k)(hf:m<k)(he:k≤j):Shaped v P (E k) (o' k):= (ht.shaped k hf he).seats v (o k) π
   have hπ:Integrable ((batt π).reap ∘ F) (prior G _):= ((batt π).reap.restrictScalars ℝ).integrable_comp hF
   rw [← Concentrate.gust_from _ F hF] at hW ⊢
   have hPin:(H.levels.clock.op i p).ratio.parent ∘ o' (i+1)=o' i:=funext (fun b=>congr_fun (ht.stalk i hw hj) ((batt π).seat b))
   obtain ⟨hA,hT⟩:= onward H δ r D σ χ v P B E o' h μ hr w hv.le hi hW (gust_live H N _ _ _ hπ hi) (ht.leave i hw hj hi) (ht.back i hw.le hj) (hE (i+1) (by omega) hj) hPin
        ((ha i hw hj.le).sectors _ _ (r i) ((stable_size π).trans (ht.ceiling i hw.le)) (H.levels.budget i).B_pos) ((ha (i+1) (by omega) hj).sectors _ _ (r i) ((stable_size π).trans (ht.ceiling i hw.le)) (P' (i+1)).B_pos) (ht.books i hw hj).1 (ht.books i hw hj).2
   rw [gust_step _ _ _ _ _ hi]
   constructor
   · exact hA
   intro hK; exact hT (hK.drake _ _ _ (hE i hw hj.le) (ha i hw hj.le))

lemma walks (hw:m < i)(hi:i≤j)(hN:j<N)(hw0:0 ≤ w0)(hF:Integrable F (prior G _))(hS:Storage H v P B E o root F j j hN.le ε w0): Storage H v P B E o root F j i (hi.trans hN.le) ε w0:=by
   induction hi using Nat.decreasingInduction with
   | self=> exact hS
   | of_succ i hi IH=>
     have hp:= IH (lt_trans hw i.lt_succ_self); obtain ⟨A,x,y,Z,a,w,hZ,hV,hW⟩:= hp.pick
     let o':=fun i:ℕ=>o i ∘ (batt Z).seat; have h' := (ht.clear i hw hi.le).seats _ _ Z; have hk:μ < i:= lt_of_le_of_lt ht.advance hw
     obtain ⟨hC,hR⟩:= dawn H δ r D σ χ v P B E o h μ hr F ε ht hw hi w hW hF; have hh:= stable_size Z
     by_cases hy:Daylight v (o' i) ((P' i).B)
     · exact ⟨A,x,y,Z,a,pinion H.S i w,hZ,warranted H.S w ε _ _ _ i w0 hh hV hW.pay,hR hy⟩
     obtain ⟨C',g,l,ψ,hA,hP,hX,hY⟩:= chief (fun b=> o' i (v,b)) a ((P' i).B^2) hy
     let W j:= δ i*w j; let q (b):= lot H.levels i δ ψ W b /8; have ht'(j):0<W j:=mul_pos (hr.suns i hk.le).hats.1 (hW.pay j)
     have hG l:0 < q l:= div_pos (Anchorage i δ W ψ (hr.suns i hk.le).hats.1 ht' l) (by norm_num)
     have hI:= ht.bill; have hXc:= ht.shelf i hw hi
     refine ⟨C',g,l,Z.alongside ψ, ψ.hit a,q, ?_, ?_, hG,0,?_,by intro j; simp⟩
     · change Z.seat _=root; rw [← hX]; exact hZ
     · refine le_trans (warrant_extra H.S ε (n-Fintype.card A+1) (n) j i w0 _ (by omega) hI.1.le hI.2.1 hw0) ?_
       rw [warrant_new]; exact (mul_le_mul_of_nonneg_left ((worn H.S ε _ _ _ _ w0 hI.1.le hw0).trans hV) (pow_nonneg hI.1.le _)).trans (teamwork H.levels δ w ψ (n) i hI.1 hI.2.1 (hI.2.2 _ hw hi) (hr.suns i hk.le).hats.1 hW.pay hh)
     have hp : ((batt (Z.alongside ψ)).reap ∘ Y i (hi.le.trans hN.le))=(batt ψ).reap ∘ ((batt Z).reap ∘ Y i (hi.le.trans hN.le)):=funext (fun x=> Concentrate.reaper (batt Z) (batt ψ) ((Y i (hi.le.trans hN.le)) x)) -- batt defeq
     rw [hp]; exact congregate v P B E o' h μ hr W _ hC ht' ψ hk (hi.trans hN) ((ht.shaped i hw hi.le).seats _ _ Z) h' (hh.trans (ht.ceiling i hw.le)) hY ht.exchange hXc.1 hXc.2
end
end YM.MergeProof.Canopies
