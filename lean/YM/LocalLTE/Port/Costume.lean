import YM.LocalLTE.Port.Caves
import YM.MergeProof.Zing
/-! # transporting inherited K burst to compact hats.

There is no assumption that at passing tests a nonzero certificate is attained. Numerators evaluated with exact internal predicates at EVERY index. We don't allow reducing support from that projection!
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Set Lattice RG Pressure Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus FrameBox Cabana Push
open Progress.DirectedRecipe MergeProof Menu Marker Accent Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{c f : Side}{Q : Rep G f} {S:StepData c f} {σ κ Λ μ' w t v : ℝ}
variable {V I J : Type}[DecidableEq V][Fintype V] {R:Marker.Census V}(B:Bands R Q)(r:V→ℝ) (hr:∀ i,0<r i) (o:V→Site f)
open Extra.Trajectories Next.Foundations
variable {d U:ℕ} {a₀ c₁ a β:ℝ}
local notation "P"=> Q.p
local notation "ν"=> Q.p.threshold
local notation "W₀"=> Config G f
variable (h:B.Active)(hw:B.Radial r a₀ a v c₁)
open Push.AbsoluteSums Push.AbsoluteSums.Animals
-- equality across crate. Keep packets even zero.Ov
local notation "NX"=> Node B
local notation "LX"=> skit B
local notation "q"=>barcode Q.activities
local notation "p!"=> billows B h
local notation "s!"=> sprites B h
variable (hs: HasSlots Q.p Q.activities)(b:Node B→ℝ)(hb:Summable b)(he:∀ i z,‖B.entries i.val.1 i.val.2 z‖≤b i)
    (ht:∀i,0≤b i) (M: skit B × Bool→Menu.Hat R Q)
    (hX:∀ (l:skit B)(i:Bool), let v:=M (l,i); v.M.turn=Wing.gasKey (youngK B l) ∧ v.M.ingredient= scaleQ i ∘ sprites B h l ∧ v.s=l.val.1 ∧ v.charge=ink i)
include hb hs h hX he
-- sum over p local.Inventory.Sx.Per.Census row.F.
omit [Fintype V] in
lemma cinemas (p:Box f)(x: Config G f): Menu.board M p x=∑' i:{i//barcode Q.activities i=p},∑' j,B.tagged i.val j x:=by
    let L:= billows B h; let F (i:Node B):=B.tagged i.val.1 i.val.2 x; let Z (i:ℕ×ℕ):=B.tagged i.1 i.2 x
    let w (v:V):=(1:ℝ); let K:=q
    have hh(i):Poly.price w (F i)≤b i:=by unfold F Bands.tagged; rw [Poly.solo]; simp [Poly.toll,w]; exact he i x
    have hg:Summable F:=(Poly.budgeted (w:=w) (fun _=> zero_lt_one) hb hh).1
    have hF (i:ℕ×ℕ)(hi:∀ k: Node B,k.val≠ i):Z i=0:=by
       have hv: B.entries i.1 i.2=0:=by by_contra h'; exact hi ⟨i,h'⟩ rfl
       unfold Z Bands.tagged; rw [hv]; exact Poly.send_zero _
    let Y(i: Node B):=if (L i).val.2=p then F i else 0; let s (l:skit B):= if l.val.2=p then Marker.Poly.send l.val.1 (sprites B h l x) else 0
    have hYS: Summable Y:= by apply (Poly.budgeted (w:=w) (fun _=>zero_lt_one) hb _).1; intro i; unfold Y; split; exact hh i; rw [Poly.zero_price];exact (Poly.nonnegative (fun _=>zero_lt_one) _).trans (hh i)
    have hW(l:LX):cram L Y l=s l:=by
        unfold cram Y; by_cases hp:l.val.2=p
        · unfold s; rw [if_pos hp]; let Z:= {i:Node B// L i=l}; simp_rw [show ∀ i:Z,L i.val=l from fun i=> i.property, if_pos hp]
          let V i:= Marker.Poly.send l.val.1 i
          let t (i:Node B):= B.entries i.val.1 i.val.2 x; let T:ℂ→L[ℂ] Poly R:= {
               toFun:=Poly.send l.val.1
               map_add':=fun u v=>by ext i;simp; split <;> ring
               map_smul':=fun u v=>(Menu.sent ..).symm
               cont:= Overlay.Bands.sends _ }
          have hv:Summable t:= hb.of_norm_bounded (fun i=> he i x); refine Eq.symm (Eq.trans (T.map_tsum (hv.comp_injective (show Injective (Subtype.val : Z→_) from Subtype.val_injective))) (tsum_congr fun i=>?_))
          exact congr_arg (fun p=> Poly.send p (t i.val)) ((congr_arg (fun p:LX=>p.val.1) i.property).symm)
        unfold s; rw [if_neg hp]; refine (tsum_congr (fun i=>?_ ) : _=∑' _:{i//L i=l},(0:Poly R)).trans tsum_zero; rw [i.property, if_neg hp]
    have hv : (∑' i,Y i)= ∑ l:skit B,s l:= by simp_rw [← hW]; rw [← tsum_fintype (L:=SummationFilter.unconditional _)]; exact (hYS.hasSum.tsum_fiberwise L).tsum_eq.symm
    rw [← show (∑' i,Y i)= ∑' i:{i//barcode Q.activities i=p},∑' j,B.tagged i.val j x from ?_]; rotate_left
    · -- fiber outside p zero.E.r
       let f':={i:ℕ//barcode Q.activities i=p}; let k(i:ℕ×ℕ):= if K i.1=p then Z i else 0
       let e:Node B ↪ ℕ×ℕ:=⟨Subtype.val,Subtype.val_injective⟩; have hi(a)(he:a∉ Set.range e):k a=0:=by
          unfold k; split; swap; · rfl
          exact hF a fun v h=>he ⟨v,h⟩
       have hK(a:Node B): k a.val=Y a:=by change (if K _=p then _ else _)=if K _=p then _ else _; rfl
       rw [← transferred_sum e (g:=Y) hK hi]; let d:f'×ℕ ↪ ℕ×ℕ:= Embedding.prodMap (show f'↪ ℕ from ⟨Subtype.val,Subtype.val_injective⟩) (Embedding.refl ℕ)
       let k' (i:f'×ℕ):= B.tagged i.1.val i.2 x; have he(i):k (d i)=k' i:= if_pos (show K ((d i).1)=p from i.1.property)
       have ht(i)(hp:i∉ Set.range d): k i=0:=if_neg (fun h=>hp ⟨(⟨i.1,h⟩,i.2),rfl⟩)
       have hh:= (transferred_summable d he ht).1 ((transferred_summable (f:=k) (g:=Y) e hK hi).2 hYS)
       rw [transferred_sum d he ht, hh.tsum_prod]
    rw [hv,Menu.patron ..,Fintype.sum_prod_type]; refine Finset.sum_congr rfl fun l _=> ?_
    let t i:= Menu.fragrance (M (l,i)) x p -- order
    have he(i):Menu.fragrance (M (l,i)) x p= (if l.val.2=p then Poly.send l.val.1 ((↑(scaleQ i (sprites B h l x)):ℂ)*ink i) else 0):=by
       let Q:= M (l,i); obtain ⟨hx,hP,hS,hg⟩:= hX l i; unfold Menu.fragrance entry; rw [hx,hS,hg]; dsimp only; rw [(locator B hs l).1]; split; rw [hP]; rfl; rw [zero_mul,Poly.send_zero]
    unfold s; change ∑ i:Bool,_ = _; simp_rw [he]; split
    next h=>
       ext r; rw [Poly.part_sum]; simp_rw [Poly.part_send]; split
       · exact Port.harvestQ _
       · simp
    next hz=> exact Finset.sum_const_zero
-- capacity
omit hb he hX
include hw
omit hs
variable (hh: HasSlots Q.p Q.activities)
include hh
lemma cargoK :∃ F: skit B × Bool→Menu.Hat R Q,(∀ i,originQ R B.origins (F i)∧∃ k,(F i).M.turn=.gasKey k)∧ (∑ i,sumFee (F i) r * Q.p.mass (F i).M.crest (F i).M.weight) ≤ 2*((Fintype.card V)*(v*c₁)) ∧∀ V p,Menu.board F p V=∑' i:{i//barcode Q.activities i=p},∑' j,B.tagged i.val j V := by
    obtain ⟨b,hb,hT,hP⟩:= Port.seatsK B r h hw -- order check
    let X'(p:LX):=p.val.2.1; let k(p:LX):=p.val.1
    have hp:= Port.everyone r hw.pure P X' k (p!) b hP hb
    choose F hO hU hv hy ha hQ using fun (p: LX) i=> Port.sealK B h hh b hp hT p i
    let F': skit B × Bool→ Menu.Hat R Q:=fun i=> F i.1 i.2
    refine ⟨F',fun i=>⟨hO .., _,hU ..⟩,?_,fun V p=>?_⟩
    · have hc:=Port.wholeQ r P X' k (p!) b hP
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hc zero_le_two); rw [Fintype.sum_prod_type, mul_sum]; apply Finset.sum_le_sum; intro i _; let q' (p:Bool):= F' (i,p)
      have h(p:Bool): sumFee (F' (i,p)) r * Q.p.mass (F' (i,p)|>.M.crest) (F' (i,p)|>.M.weight)= Poly.toll r (k i)* Q.p.mass (X' i) (cram (p!) b i):=by
          dsimp only [F',sumFee]; rw [ha,hy,hQ,tintX,mul_one]; unfold Leaf.crest; rw [hU]; exact congr_arg (fun v: Support f=> _*Q.p.mass v _) (congr_arg Prod.fst (locator B hh i|>.1))
      rw [Fintype.sum_bool,h,h];exact le_of_eq (by ring)
    apply Port.cinemas B h hh b hp hT (F') (fun i k=>⟨hU i k,hv i k,hy i k,hQ i k⟩) p V -- order
end YM.LocalLTE.Port
