import YM.Frontier6.Multi.Storage.Itinerary

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
def singletonC (b:O): Concentrate O Unit:= ⟨fun _=>(), fun _=>b, fun _=>rfl⟩
def droplet (b:O): Concentrate (Live V O) V:=⟨Prod.fst, fun i=>(i,b),fun _=>rfl⟩
def dropped : Live V Unit≃ V := Equiv.prodUnique _ _
local notation "T!"=> (dropped (V:=V))

structure Port (hm:m+1≤ N):Prop where
   pays : ∃ (g:V→ Config G (H.S.side (m+1) p)→ℂ)(k:V→ℕ→ Config G (H.S.side (m+1) p)→ℂ),
        Served (R (m+1)) g (fun j=>profile (R (m+1)).activities (k j)) ((droplet root).reap ∘ gust H N p N F (m+1) hm) (fun j=> o (m+1) (j,root)) (fun j=>w0) ((P' (m+1)).supportExponent) 1 ∧
        (∀ j, Dominated (k j))∧ Blade (R (m+1)) (o (m+1) (v,root)) (g v) (profile (R (m+1)).activities (k v)) 0 (1/(2*w0)) ∧ ∀ i,i ≠ v → g i=stepUp (P i) (E (m+1) i) (g v)∧ profile (R (m+1)).activities (k i)=floatUp (P i) (E (m+1) i) (profile (R (m+1)).activities (k v))

lemma buckle (hw:0<w0) (t:ℝ)(hL:w0 ≤ t){hN:m+1 ≤ N} (q : O) (he:root=q) (hp: Parcels H v P B E (fun i=>o i ∘ (batt (singletonC q)).seat) (m+1) (N:=N) ((batt (singletonC q)).reap ∘ Y (m+1) hN) (fun _=>t) 0) : Port H v P E o w0 F root hN:=by
    subst q; obtain ⟨g,k,hS,hM,hL',hB⟩:= hp.shop; let f:=Y (m+1) hN; let X':=batt (V:=V) (singletonC root); let W : V→ℝ:= fun _=>w0; let W₁:Live V Unit→ℝ := fun _=> t
    have hv:=Concentrate.unpacked (w:=W₁) (T!) hS.sold; have hx:(Concentrate.relabel T!).reap ∘ (X'.reap ∘ f)=(droplet root).reap ∘ f:=by
        have hz:X'.alongside (Concentrate.relabel T!)=droplet root:=rfl
        rw [← hz]; exact funext (fun i=> (Concentrate.reaper X' _ _).symm)
    let G':= g ∘ (T!).symm; let K:= k ∘ (T!).symm; change Served _ _ _ ((Concentrate.relabel _).reap ∘ ((X').reap ∘ f)) (fun i=> o (m+1) (i,root)) (fun i=>t) _ _ at hv; rw [hx] at hv
    have ht:0<t:= hw.trans_le hL
    refine ⟨G',K, hv.prune (fun _=>ht) (fun _=>hw) (slighter (fun j:V=> ht) (fun j:V=>hw) (w:=1) (fun j=>le_trans hL (by rw [one_mul])) zero_le_one le_rfl) zero_le_one (by simp) (by norm_num),fun j=> hL' (j, ()),(hB ()).more ?_, fun i hi=>⟨(hM i hi|>.2 ()).1,(hM i hi|>.2 ()).2.1⟩⟩
    exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hL zero_le_two)

variable (ht:Travel H δ r D χ v P B E o m j μ ε N)
include h hr ht
local notation "M!"=> warrant H.S ε ((n)+1) (n) j (m+1)
lemma walking {w:ℝ} (hi:m+1<j)(hN:j<N)(hy:∀ b:O,separation (o (m+1) (v,b)) (o (m+1) (v,root)) ≤ (H.levels.budget (m+1)).B^2)(hw0:0 < w0)(hw:M! w ≥ w0)(hA:0 ≤ w) (hF:Integrable F (prior G _))(hS:Storage H v P B E o root F j j hN.le ε w): Port H v P E o w0 F root (hi.le.trans hN.le):=by
    have hx:m+1+1 ≤ j:= hi; obtain ⟨C',p',n',π,c,w',he,hv,hW⟩:= (walks H δ r D σ χ v P B E o h μ hr w F root ε ht (i:=m+1+1) (by omega) hx hN hA hF hS).pick
    let i:=m+1; let o':=fun i:ℕ=>o i ∘ (batt π).seat; have hi':μ < i:=by exact ht.advance.trans_lt m.lt_succ_self
    obtain ⟨hQ,hR⟩:= dawn H δ r D σ χ v P B E o h μ hr F ε ht m.lt_succ_self hi w' hW hF; have hh:= stable_size π; let ψ:= singletonC c; have hy'(j): separation (o' i (v,j)) (o' i (v,ψ.seat (ψ.hit j))) ≤ (P' i).B^2:= by
       change separation (o i (v,_)) (o i (v,π.seat c)) ≤ _; rw [he]; exact hy _
    let W j:= δ i*w' j; let q (b):= lot H.levels i δ ψ W b /8; have hσ:= (hr.suns i hi'.le).hats.1; have hp j:0<W j:=mul_pos hσ (hW.pay j); have hg : total q=q ():=by simp [total]
    have hI:= ht.bill; have hX:= ht.shelf i m.lt_succ_self hi; apply buckle H v P B E o w0 F root hw0 (q ()) _ root rfl
    · have hA:= congregate v P B E o' h μ hr W _ hQ hp ψ hi' (hi.trans hN) ((ht.shaped i m.lt_succ_self hi.le).seats _ _ π) ((ht.clear i m.lt_succ_self hi.le).seats _ _ π) (hh.trans (ht.ceiling i m.le_succ)) hy' ht.exchange hX.1 hX.2
      have hz : π.alongside ψ=singletonC root:=by have h0 : (π.alongside ψ).seat=(singletonC root).seat:= funext (fun _=> he); unfold Concentrate.alongside singletonC; congr -- test
      rw [← hz]; change Parcels H _ _ _ _ _ _ (N:=N) _ q 0; have hP : ((batt (π.alongside ψ)).reap ∘ Y i (hi.le.trans hN.le))=(batt ψ).reap ∘ ((batt π).reap ∘ Y i (hi.le.trans hN.le)):=funext (fun x=> Concentrate.reaper (batt π) (batt ψ) ((Y i (hi.le.trans hN.le)) x))
      rw [hP]; exact hA
    · rw [← hg]; refine hw.trans ((warrant_extra H.S ε (n-Fintype.card C'+1) _ _ _ w _ (by omega) hI.1.le hI.2.1 hA).trans ?_); rw [warrant_new]; exact (mul_le_mul_of_nonneg_left ((worn H.S ε _ _ _ _ w hI.1.le hA).trans hv) (pow_nonneg hI.1.le _)).trans (teamwork H.levels δ w' ψ (n) i hI.1 hI.2.1 (hI.2.2 i m.lt_succ_self hi) hσ hW.pay hh)
end
end YM.MergeProof.Canopies
