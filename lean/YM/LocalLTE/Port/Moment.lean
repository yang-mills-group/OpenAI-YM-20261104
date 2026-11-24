import YM.MergeProof.Ember
import YM.MergeProof.Hash
import YM.LocalLTE.Port.Hallows
import YM.Overlay.Pays
/-! # Simultaneous hats in one trajectory (plus UNIT external). Assembly from total logs all SWITCH.Root.V.
Hereafter B.units multiplied separately after push. Every non-constant
factor uses ordinary per-sample calculations, on the same Q dictionary.
choose distinct log addresses for all without packing Ω.R except limited markup κ.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Port
open Function Filter Lattice RG Wilson Finset MeasureTheory
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus FrameBox Cabana Push
open Progress.DirectedRecipe MergeProof Menu Marker Accent Overlay
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge}{c f : Side}{Q : Rep G f} {S:StepData c f} {σ κ Λ μ' w t v : ℝ}
variable {V ι:Type}[DecidableEq V][Fintype V](R: Marker.Census V) (B:Bands R Q) [Fintype ι]
variable (r:V→ℝ)(M:ι → Hat R Q)
    (hQ: Q.Lawful σ Λ μ' κ w) (hr:∀ i,0<r i)
-- ledger will settle θ.E. ψ. physical Packing.Careful census occ flagged.F.B. No funds left rebuild.Any.
variable (U:Config G f)
open Extra.Trajectories
lemma ranksP (hx:∀ i:ℕ,∀ j k, (M j).M.turn=.logKey i → (M k).M.turn=.logKey i → k=j) : jets M U= Marker.Poly.pass (Menu.roll M U):=by
    have ht(i:ℕ)(hi: i∈logDeck M) : Poly.pass (rush M (.logKey i) U)=1+rush M (.logKey i) U:=by
       rw [rolled_up .., show (∑ j:Rock M (.logKey i),amount (rise M (.logKey i) j.val) U)=0 from ?_,add_zero]
       apply sum_eq_zero; intro k _
       let p:= k.val.val; have hh:1<p.card:=k.property; obtain ⟨x,hx',y,hy,hQ⟩:= Finset.one_lt_card.mp hh
       have hu(l)(hl:l∈p): (M l).M.turn=.logKey i:=(mem_filter.mp (k.val.property.2.1 hl)).2
       exact False.elim (hQ (hx _ _ _ (hu y hy) (hu x hx')))
    unfold jets roll; let c i:=rush M (.logKey i) U
    generalize he:logDeck M=P
    have hh (s:Finset ℕ) (h:s⊆P): (∏ i∈s,(1+c i))=Poly.pass (∑ i∈s,c i):=by
       induction s using Finset.induction with
       | empty=> simp
       | insert i s hx ih=> rw [Finset.prod_insert hx,Finset.sum_insert hx, ih ((subset_insert ..).trans h), ← show Poly.pass (c i)= _ from ht i (he.symm ▸ h (mem_insert_self ..)),pass_add]; exact still M _ _; exact (Poly.part_sum ..).trans (sum_eq_zero fun i _=> still M _ _)
    exact hh _ (Finset.Subset.refl _)

include hQ
omit [Fintype V] in
lemma hairs (U:Config G f): let F:= Q.activities; ∀ p:Box f, (Poly.send R.quiet (profile F (fun i=> Complex.ofReal ∘ F.K i) p U))=cram (barcode F) (fun i=> Poly.send R.quiet (↑(F.K i U):ℂ)) p:=by
    intro F p; let f':=barcode F; let v (i:ℕ):=F.K i U; let q:ℕ→Poly R:=fun i=> Poly.send R.quiet (↑(v i))
    have hm: Summable v:= mass_crest F hQ.labels U
    have hF:Summable q:=by
        let w:=fun _:V=> (1:ℝ); have he: Summable fun i=> Poly.price w (q i):=by simp [q]; exact hm.norm
        exact (Poly.budgeted (w:=w) (fun _=>zero_lt_one) he (fun i=> le_rfl)).1
    ext p'; change _=(cram f' q _).part p'; rw [cram, Poly.share, Poly.part_send]
    · split; next hx=>
         unfold profile cram; exact tsum_congr fun i=> by unfold q; rw [Poly.part_send,if_pos hx]; rfl
      next hx=> exact Eq.symm ((tsum_congr fun i=> by unfold q; rw [Poly.part_send,if_neg hx] : ∑' i:{i// f' i=p},(q i.val).part p'=∑' _: {i// f' i=p},(0:ℂ)).trans tsum_zero)
    exact hF.comp_injective Subtype.val_injective
variable (hA : B.Active)
include hr hA
open Extra.Trajectories
variable {a C D β d:ℝ} (hF:B.Radial r a C D d)
-- Units multiplied AFTER.Ph
include hF
lemma captured (hx:∀ i:ℕ,∀ j k, (M j).M.turn=.logKey i → (M k).M.turn=.logKey i → k=j)
    (hl: Menu.roll M U =∑' i,B.ray i U) (ht:∀ p:Box f, board M p U = ∑' i: {i//barcode Q.activities i=p}, ∑' j,B.tagged i.val j U):
    B.density U= Poly.pass (∑ i,Marker.Poly.send (R.fire i) (B.units i))* Merge.Photo.given (S:=S) (fun i=>(M i).M) (fun i=> sumFee (M i) r) R (fun i=> Menu.sing (M i) r) U:=by
    rw [Menu.passIn M _ hQ hr U, ranksP R M U hx, hl]
    let E (i:ℕ):= B.each i U; let k(i:ℕ):=Q.activities.K i U; let F:=barcode Q.activities
    obtain ⟨hy,hQ'⟩:= B.baseBound hA hF hQ.labels U
    have he(p:Box f) : cram F E p=bar Q.activities R U p+board M p U:=by
       let z(i:ℕ):= Poly.send R.quiet (↑(k i):ℂ)
       have h:Summable z:= by
           have hv: Summable fun i=> Poly.price r (z i):=by simp [z]; exact (mass_crest _ hQ.labels U).norm
           exact (Poly.budgeted hr hv (fun i=> le_rfl)).1
       change ∑' i:{i// F i=p},(z i.val+∑' j,B.tagged i.val j U) = _
       rw [Summable.tsum_add]; exact congr_arg₂ (·+·) (hairs R hQ U p|>.symm) (ht p).symm
       · exact h.comp_injective Subtype.val_injective
       have he:Summable E:= (Poly.budgeted hr hQ'.2.1 (fun i=>le_rfl)).1
       exact (((he.sub h).comp_injective (i:=Subtype.val) (show Injective (Subtype.val : {i// F i=p}→ℕ) from Subtype.val_injective))).congr fun i => by change (_ + _) - _ = _; abel
    have hK:B.cluster U=field (fun i=>bar Q.activities R U i+board M i U) (RG.flags Q.p.threshold U):=by rw [show (fun i=>_)= _ from (show (cram F E) = (fun i=>bar Q.activities R U i+board M i U) from funext he).symm]; exact (rock_out _ _ U E hr hQ'.2.1).symm
    unfold Bands.density; rw [hK]; unfold Bands.extra; rw [pass_add, mul_smul_comm,mul_assoc]
    · exact (Poly.part_sum ..).trans (sum_eq_zero fun i _=> by rw [Poly.part_send, if_neg ((R.fire_hot _).symm : R.quiet ≠ R.fire _)])
    rw [Poly.share (B.bulkBound hA hF U|>.1)]; let x(i:ℕ):= B.ray i U; exact (tsum_congr fun i=> (show (x i).part R.quiet=0 from (by unfold x Bands.ray; rw [Poly.part_send,if_neg (fun h=> (hA.proper _).ne_empty (show (B.rays i).val=∅ from (congr_arg Subtype.val h.symm)))]))).trans tsum_zero
end YM.LocalLTE.Port
