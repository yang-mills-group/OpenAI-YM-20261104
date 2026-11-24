import YM.OPE.Laying.Capture
/-! # Mark a fresh roster, and upcoming grouping births -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Book
open Function Filter Finset Lattice RG Wilson Source Extra.Histories Labels Pressure
open Push Local Marker MergeProof Accent Ribbons Menu Overlay ManyCopies Cadet Lecture Muster
open PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Bid Extra.Multi
open Cells MeasureTheory Motion Backup Float Drapery Playout.Rake
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{I J V:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
    [Fintype V][DecidableEq V]{k i j b q p N d T :ℕ}{w x y α x':ℝ}{W r D}
    (L:LogPackage C W r D)(h:C.Makes)
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "μ'"=> (waybill C.path.levels)
local notation "δ₀"=> renal C.path.levels
local notation "η₀"=> near C.path.levels
local notation "ζ"=> fly C.path.levels
local notation "Ξ"=> C.path.rep N p
local notation "ν"=> (fun i=> ((C.path.levels.budget i).supportExponent-3:ℝ))
variable {Θ: Playout C.path p b N V}{A:Fibers I J} {s:Ward (Names V I)} {s':Ward (Names V J)}{W₀:ℕ→I→ℝ}{φ:I→ℕ}
    {u:∀ i:ℕ,I→ Site (C.side i p)} {F:I→ Config G (C.side N p)→ℂ}
    {P:∀ i:ℕ,I→ Cup (C.path.rep N p i)} {z:Finset J}
variable (S:Ledger Θ (j+1) (pullback A s') F P u φ W₀ x (D:(∀ N p m,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))))
variable (U:Release Θ A z s' i j L φ u)
local notation "Γ"=> (fun i=> (Y).clock.hatBeta (i+1))
-- replace widths by constant for all newly minted tickets (future may demand stronger pledge, settled using Mint)
def afterGoal (φ:I→ℕ)(i:ℕ) (A:Fibers I J) (z:Finset J) (k:J) := if k∈z then φ (A.twig k) else i
def afterWidth (W:ℕ→I→ℝ)(i:ℕ)(A:Fibers I J)(z:Finset J)(m:ℕ)(k:J):= if k∈z then W m (A.twig k) else lineRelease A (W i) k
lemma after_shape (A:Fibers I J)(i:ℕ)(z:Finset J)(h:Lenient η₀ φ W₀) : Lenient η₀ (afterGoal φ i A z) (afterWidth W₀ i A z):=by
    have he(k):0<lineRelease A (W₀ i) k:=prod_pos fun j _=> h.ready ..
    constructor
    · intro k m; unfold afterWidth; split; exact h.ready ..; exact he k
    · intro k m hm; by_cases ht:k∈z; · rw [afterGoal,if_pos ht] at hm; rw [afterGoal,if_pos ht,afterWidth,if_pos ht,afterWidth,if_pos ht]; exact h.early _ _ hm
      unfold afterWidth; rw [if_neg ht,if_neg ht]
    intro k m; unfold afterWidth; split; exact h.paid ..
    exact mul_le_of_le_one_left (he k|>.le) (inv_le_one_of_one_le₀ ((Y).fits.delayed (m+1)|>.le))
local notation "φ₀"=> afterGoal φ i A z
local notation "Y'"=> afterWidth W₀ i A z
include U S h
lemma Release.issue (d':J→ℕ)(hb:T>0)(hT:Fintype.card I ≤ T) (hG:G.Simple)(ht:∀ a∉z,C.ref (d' a) ≤ i) (hx':0<x')(hf:x'≤ (cell C.path (i+1) j (T+2) (peer L T j) x)^T)(hc:x'≤x)(hy:0<y)(hz:4*y*Γ i ≤ x')(hk:0<α)(hr:α≤ δ₀ i*η₀ i*y)(hX:α≤x):
    ∃ F', Ledger Θ i s' (grouped_X F A) F' (fun i=> u i ∘ A.twig) φ₀ Y' α D ∧
       (∀ k∈z,∀ m,F' m k=P m (A.twig k)) ∧ ∀ k∉z,Minted C N p i (d' k) (x'*lineRelease A (W₀ i) k) (u i (A.twig k)) (F' i k):=by
    let R':= lineRelease A ∘ W₀
    obtain ⟨P',hP,hQ,hξ⟩:= Release.land L h S U d' hb hT hG ht hx' hf hc hy hz hk hr
    let p'(m):= (fun x'=> P m (A.twig x')); let P''(m:ℕ):= if he:m=i then (show J→Cup (Ξ m) from he.symm ▸ P') else p' m; have hp:P'' i=P':=dif_pos rfl
    have he(k:J)(he':k∈z) m:P'' m k=P m (A.twig k):=by
       by_cases ht:m=i; · subst m; rw [hp]; exact hQ k he'
       exact congr_fun (show P'' m=p' m from dif_neg ht) k
    have hQ(k:J)(he:k∈z): lineRelease A (W₀ i) k=W₀ i (A.twig k):=by unfold lineRelease; rw [(U.lights k he).content,prod_singleton]
    have ha:= S.limit; have hτ:= U.prep; have hΤ:= U.beginning
    have hψ:Lenient η₀ φ₀ Y' := after_shape A i z S.clock
    refine ⟨P'',⟨U.beginning,by omega,U.game,fun k hk ht a=> S.slots k hk (by omega) _, cont F A S.terms,fun k=> ?_,⟨hk,hX.trans S.rate.2⟩,hψ, ?_,fun k=>?_⟩,he,fun k ht=> ?_⟩
    · by_cases he:k∈z
      · rw [afterGoal,if_pos he]; exact ⟨(S.stock _).1,U.sleeper _ (A.sectioned k|>.symm ▸ he)⟩
      rw [afterGoal,if_neg he]; exact ⟨hΤ,le_rfl⟩
    · rw [hp,show lifted Y' α i= _ from ?_]; exact hP
      change lifted Y' α i=lifted (fun i=>lineRelease A (W₀ i)) α i; funext k; unfold lifted afterWidth; dsimp only; split; rename_i ht; rw [hQ _ ht]; rfl
    · by_cases ht:k∈z; swap; · exact ⟨fun m hΛ he'=> (by rw [afterGoal,if_neg ht] at hΛ; omega)⟩ -- simp
      let Q:=fun m=> P m (A.twig k); let O(m):=lifted W₀ x m (A.twig k); let O'(m):=lifted Y' α m k; rw [afterGoal,if_pos ht,show (fun m=>P'' m k) = Q from funext (he k ht)]
      apply Program.within (S.progress (A.twig k)) le_rfl (by omega) (fun k' _ _=> (hψ.scaleRight hk |>.ready k k').le) (fun k' _ _=> ?_)
      unfold lifted afterWidth; rw [if_pos ht]; exact mul_le_mul_of_nonneg_right hX (S.clock.ready ..|>.le)
    rw [hp,show lineRelease A (W₀ i) k=lineRelease A (W₀ (i+1)) k from prod_congr rfl (fun j' hj=> by have hp:=U.prompt j' (fun h=>ht (((A.focuses ..).1 hj) ▸ h)); exact (S.clock.early _ _ (by omega)).trans (S.clock.early _ _ (by omega)).symm) ]; exact hξ k ht

omit U S h
-- reconnect all zero-purse branches without changing copper. including weight zero marked no erasure.
local notation "t'"=> C.localSection d
noncomputable def stampOut (C:Family G) (i d:ℕ)(x:ℝ) :=4*(1+(C.path.levels.params i).columns)*(2*resQuote C i d x)
variable (V':Ledger Θ i s F P u φ W₀ x (D:(∀ N p m,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m))))
    {φ₁:I→ℕ}(X:I→ℝ)(z':Finset I)
local notation "z!" => (lifted W₀ x)
include h V' L
lemma Ledger.rolling (hG:G.Simple) (hc:C.ref 0 ≤ b)(hx:∀ k∈z',b ≤ φ₁ k∧φ₁ k ≤ φ k)(he:∀ k∉z',φ₁ k=φ k)(hk:∀ k∈z',φ k=i)(hU:∀ k∈z',∀ m:ℕ, φ₁ k ≤ m→m < i → u (m+1) k=(C.path.levels.clock.op m p).ratio.embed (u m k))(hX:∀ k∈z', Minted C N p i 0 (X k) (u i k) (P i k) ∧ lifted W₀ x i k*(4*stampOut C i 0 (X k)) ≤ ζ 0 i) : ∃ F', Ledger Θ i s F F' u φ₁ W₀ x D ∧ F' i=P i ∧ ∀ k∉z',∀ m,F' m k=P m k:=by
    have hz:= V'.rate.1; have hN:= V'.limit
    have hΨ(k:I) m (h:m ≤ φ k): z! m k=z! (φ k) k:=(V'.clock.scaleRight hz).early k m h
    have he'(k:I):φ₁ k ≤ φ k:= by by_cases h:k∈z'; exact (hx k h).2; exact (he k h).le
    obtain ⟨E,hE⟩:=Studio.seriesExist (ψ:= μ') L.system ((hc.trans V'.time).trans hN)
    have hh(k:I):∃ p':∀ i:ℕ,Cup (C.path.rep N p i), Program C.path N p (φ₁ k) i (fun i=>u i k) p' (fun m=>lifted W₀ x m k) D V'.limit ∧ p' i=P i k ∧ (k∉z'→ ∀ m,p' m=P m k):=by
        by_cases ht:k∈z'; swap; · rw [he k ht]; exact ⟨fun i=>P i k,V'.progress k,rfl,fun _ _=>rfl⟩
        obtain ⟨t,hu,hR,hL,hF⟩:=(hX k ht).1.bound; let v:= resQuote C i 0 (X k); let s:=stampOut C i 0 (X k); have hy(μ:ℕ)(he:μ ≤ i) : z! μ k=z! i k:= by
            calc _ = z! (φ k) k:= hΨ k _ (by rw [hk k ht]; exact he)
                 _ = _:=by rw [hk k ht]
        have hl:= (hx k ht); have hμ:=hc.trans hl.1
        obtain ⟨p',hP,hA⟩:=Studio.ZeroDegree.unspent (C.localSection 0) (1,false) h.wilson (h.sections 0) hE.echo hμ (hl.2.trans (V'.stock k).2) hN hF hu hR (show (C.labels.level 0).coeffSize t.x+v ≤2*v by linarith only [hL]) (show _ ≤ s from le_rfl) (L.art hμ) (X:=fun i=>u i k) (w:=fun i=>lifted W₀ x i k) (fun _ _ _=> V'.clock.scaleRight hz|>.ready ..) (fun _ _ ht=>(by rw [hy _ ht,hy _ ht.le])) (hU k ht) (fun i' _ h=>by rw [hy i' h]; exact le_trans (hX k ht).2 (flyAnti (C:=C) hG 0 h))
        exact ⟨p',hP,hA,fun h=>(h ht).elim⟩
    choose p' hp' hF hK using hh
    let V(m k):=p' k m; refine ⟨V,⟨V'.time,hN,V'.trial,V'.slots,V'.terms,fun i=> ?_,V'.rate, ?_,?_,hp'⟩,funext hF,(fun k=>hK k) ⟩
    · refine ⟨?_,(he' i).trans (V'.stock i).2⟩; by_cases h:i∈z'; exact (hx i h).1; rw [he _ h]; exact (V'.stock i).1
    · exact ⟨V'.clock.ready,fun k m h=> (V'.clock.early k m (h.trans (he' k))).trans (V'.clock.early k (φ₁ k) (he' k)).symm,V'.clock.paid⟩
    rw [show V i=P i from funext hF]; exact V'.market
end YM.OPE.Log.Book
