import YM.LocalLTE.Ticket.Press
/-!
## Slip transactions for the cost estimator

Cylinders may be accessed by these *same* ports.
Personal program used on incoming
models, body validity for another actual magnitude cannot substitute for the receipts
on that model. Norm uses all links in site sets. Energy bills overbook
some binomial/readout prices; K includes none of the PDF normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Ticket
open Function Filter Lattice Wilson RG Source Labels Extra.Histories Bid
open LocalLTE.Vinca LocalLTE.FrameBox AnalyticBridge VerifiedReset Collection Price PhysicalNext.Repeat Blush
open Push Local Planned.GuardedAtom LocalLTE.River YM.MergeProof
open Finset MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{H:History G}{N m p:ℕ}{k d:ℕ}{F:Labels.Frame G d} (D:SectionData F) (A:Hol G)
local notation "O" => H.rep N p m
local notation "P" => H.rep N p (m+1)
local notation "V₀"=> H.S.side (m+1) p
local notation "V"=> H.S.side m p
local notation "κ" => Real.sqrt (H.levels.clock.forcedAllowance m)
local notation "κ'" => Real.sqrt (H.levels.clock.forcedAllowance (m+1))
-- model book.RQ acceptable for ALL desks incl output capacities not enough for a paid model.As long after.L scheduled sender.
open Extra.Histories.InputColumn
variable (Q: Gateway F A (H.rep N p (m+1)) (H.S.side m p) ) (Q': Pigment A F (H.rep N p (m+1)) (H.S.side m p))
set_option quotPrecheck false
structure Inlet (k:ℝ ) (a U:ℕ ) (W:Coefficient F V₀ ) (τ:ℝ) where
     format : W.Format 0 A (H.rep N p (m+1))
     prices:ℕ→ℝ
     vow:SumBudget (fun i=> (H.rep N p (m+1)).p.mass (W.support i) (prices i)) τ
     truth i:Canvas D k U a (H.rep N p (m+1)).p (W.support i) (W.regular i) (prices i)
variable {R R':Coefficient F (H.S.side (m+1) p)} {k τ η e:ℝ} {a b U u:ℕ}
-- predictor. Does NOT need actual syllabus except padding for skipped slots.Aperture.
variable (R) (X:Syllabus H N p m A R η) (Y: Inlet (H:=H ) (N:=N ) (p:=p ) (m:=m) D A k a U R' τ) (i: F.Index)
noncomputable def rolls : InputColumn.Listing → Coefficient F (H.S.side m p) := consist (if i=0 then Vinca.unitP F H p m else Q'.main i) (fun j=> Q'.gain (R'.support j) (R'.regular j) (Y.prices j) ⟨Y.format.smooth j,Y.format.origin j,Y.format.identity_null j,Y.format.projects j⟩ (Y.truth j|>.value)) (fun j=> idle F ((Vinca.coins H N p m A Q R X i (.inr (.inr j))).support))
noncomputable def issueC := Extra.Histories.merge (code _) (rolls D A Q Q' R X Y i)
-- generic residual receipt.rebased.Std.Snacks.
variable {C:Tariff} (h:Dues D A (H.rep N p (m+1)) (H.rep N p m) Q Q' (Real.sqrt (H.levels.clock.forcedAllowance m)) k a b U u C)
variable (hp:F.coeffSize ((Vinca.unitP F H p m).x) ≤ C.issue)
section
-- exact zero zero.Any footprint.Doesn't presume binding to ensemble cost.
variable {x: ℕ}
private lemma primaryS {s:ℝ} (v:F.Coeff ) (hX:F.coeffSize v≤ s) : Exhibition D k u a A O (Extra.Histories.primary (0:Site V) v) (Extra.Histories.primary 0 v) (Real.sqrt (H.levels.clock.forcedAllowance m)) s 0:=by
   let r:=Extra.Histories.primary (0:Site (H.S.side m p)) v
   let S:Coefficient F (H.S.side m p):=Extra.Histories.primary 0 0
   have ht:0 < κ:= Real.sqrt_pos.mpr (forcedPos ..)
   have hf:Vinca.decrement r r=S:=by simp [decrement,r,S,Extra.Histories.primary]
   have hX' : Patrons D k u a (O).p S 0:= by apply River.patronC _ rfl rfl; simp [S,Frame.coeffSize, Extra.Histories.primary]
   refine ⟨River.patronC hX rfl rfl, primary_format ..,rfl,hf.symm ▸ (primary_format ..),hf.symm ▸ hX'.bill ht, ?_⟩
   change F.coeffSize (decrement r r).x ≤ _; rw [hf]; exact hX'.principal
end
include h hp -- K stored.Caper. P.B.Described supports.E normalized.
lemma balances (uL:ℝ ) (hη:SumBudget (fun i=>(P).p.mass (R.support i) (X.a i)) uL) (hlayout:R.support=R'.support ) (hf:∃ q:ℕ→ℝ,SumBudget (fun i=> (P).p.mass (R.support i) (q i)) e ∧ ∀ i,(P).p.supBounds 0 (R.support i) ((R.regular-R'.regular) i) (q i))
    (hg:Local.ForceCost (P).p (P).activities R.forced ((Real.sqrt (H.levels.clock.forcedAllowance (m+1)))*(e+e))) : Exhibition D k u b A (O) (Vinca.issue H N p m A Q R X i) (issueC D A Q Q' R X Y i) (Real.sqrt (H.levels.clock.forcedAllowance m)) (C.first uL τ e) (C.second uL τ e (Real.sqrt (H.levels.clock.forcedAllowance (m+1)))) :=by
    obtain ⟨q,hq,hq'⟩:= hf; obtain ⟨z,hz,hz'⟩:= hg
    let x' j:= (P).p.mass (R.support j) (X.a j); let y j:= (P).p.mass (R'.support j) (Y.prices j); let u' j:=(P).p.mass (R.support j) (q j); let z' j:=(P).p.mass ((P).activities.forced j).support (z j)
    let u0: InputColumn.Listing → ℝ:= consist C.issue (fun i=> C.advance (x' i) (y i) (u' i)) (fun _=>0); let u1:InputColumn.Listing →ℝ := consist C.rare (fun i=> C.due (x' i) (y i) (u' i)) (fun i=> C.flag*z' i)
    let Q0:= Vinca.coins H N p m A Q R X i; let Q1:= Ticket.rolls D A Q Q' R X Y i
    have hx(j): Exhibition D k u b A (O) (Q0 j) (Q1 j) κ (u0 j) (u1 j):=by
       rcases j with v|j|j
       · change Exhibition _ _ _ _ _ _ (if i=0 then _ else _) (if i=0 then _ else _) _ _ _
         by_cases ht:i=0
         · rw [if_pos ht,if_pos ht]; exact Exhibition.pledge (primaryS (H:=H) (m:=m ) (p:=p ) (N:=N) D A _ hp) le_rfl C.fRare
         rw [if_neg ht, if_neg ht]; exact h.primary i ht
       · let f:=R.regular j; let g:=R'.regular j; let d':=R.support j; let e':=R'.support j; have he:e'=d':=congr_fun hlayout.symm _
         have hX0:RegFit (P) 0 d A d' f:= ⟨X.outfit.smooth j,X.outfit.origin j,X.outfit.identity_null j,X.outfit.projects j⟩
         let γ:= X.a j; let g':=Y.prices j; have hy':RegFit (P) 0 d A e' g := ⟨Y.format.smooth j,Y.format.origin j,Y.format.identity_null j,Y.format.projects j⟩
         have hb': Canvas D k U a (P).p e' g g':=Y.truth j; let α:= Q.reader f d' γ hX0 (X.fields j); let β:= Q'.gain e' g g' hy' hb'.value
         change Exhibition _ _ _ _ _ _ α β _ (C.advance _ ((P).p.mass e' g') _) (C.due _ ((P).p.mass e' g') _); have hk':Canvas D k U a (P).p d' g g':=he ▸ hb'; have hi':RegFit (P) 0 d A d' g:= he ▸ hy'
         rw [show β= Q'.gain d' g g' hi' hk'.value from ?_, he]
         · exact h.gain _ _ _ _ _ _ hX0 hi' (X.fields _) hk' (hq' j) -- reducibility y.
         unfold β; congr 1 -- dependent.V proof. may simp
       change Exhibition _ _ _ _ _ _ (Q0 _) (idle F ((Q0 _).support)) _ 0 (C.flag*z' j); by_cases he:R.forced j=0
       · unfold Q0 Vinca.coins consist; simp only [Sum.elim_inr]; rw [if_pos he]
         have hv : F.coeffSize 0 ≤ 0:=by simp [Frame.coeffSize]
         exact (primaryS (H:=H ) (m:=m ) (p:=p ) (N:=N ) (u:=u ) (a:=b ) (k:=k) D A 0 hv).pledge le_rfl (mul_nonneg C.fFlag (hz.1 j)) -- idle.primary definition.rfl?
       unfold Q0 Vinca.coins consist; simp only [Sum.elim_inr]; rw [if_neg he]; exact h.forced _ _ _ _ he _ _ (fun i=> (hz' j).2 i)
    have hv: HasSum u0 (C.first (∑' j,x' j) (∑' j,y j) (∑' j,u' j)):=by
       have hv:= added (f:=u0) (C.advSeries hη.2.1.hasSum Y.vow.2.1.hasSum hq.2.1.hasSum) hasSum_zero; rw [add_zero] at hv; exact hv
    have ht: HasSum u1 (C.rare+(C.due (∑' j,x' j) (∑' j,y j) (∑' j,u' j)) + C.flag*(∑' j,z' j)):=by rw [add_assoc]; exact added (C.dueSeries hη.2.1.hasSum Y.vow.2.1.hasSum hq.2.1.hasSum) (hz.2.1.hasSum.mul_left C.flag)
    apply (River.auctions _ Q0 Q1 hx hv.summable ht.summable (Real.sqrt_pos.mpr (forcedPos ..))).pledge _ _ -- order. no p
    · rw [hv.tsum_eq]; exact add_le_add le_rfl (C.advance_ge hη.2.2 Y.vow.2.2 hq.2.2)
    rw [ht.tsum_eq]; exact add_le_add (add_le_add le_rfl (C.due_ge hη.2.2 Y.vow.2.2 hq.2.2)) (mul_le_mul_of_nonneg_left hz.2.2 C.fFlag)
end YM.LocalLTE.Ticket
