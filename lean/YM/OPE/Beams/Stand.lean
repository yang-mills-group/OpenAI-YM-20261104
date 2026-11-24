import YM.OPE.Beams.Pretty
/-!
# Re-layout declaration for a reused direct log estimate

Erased class has only one representative, literal. Anchors at (virtual)
zero. No obligation on the pose which was used to get the original child
matching vector. Needed to get polynomial price on its redacted coalesced
participation and on all correction channels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log.Reels
open Function Filter Finset MeasureTheory Lattice RG Wilson Metric Polar
open Trunk Rhythm Payments Shuttle
open scoped Classical Topology ContDiff BigOperators
variable {G:Gauge}{C:Family G}{F:Extraction.Order} {S:Table C.book}(U:Spec.Final C F S)
variable {I J L Z:Type}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]{f:Filter L}
    {T:L→ℝ}{M η P₀:ℝ}{v j k:I}
    {X:L→ I→ E4}{x:L→ (I→ E4)→ J→ E4}
    {H t n m:ℕ}{Q: Rhythm I}
    {R r:L→ℕ→ℝ}{α:ℕ→ℝ}{Y: L→ ℕ}
    (B:Border f T Q.limit R r α)
    (H':Q.Strike H n)(hm:0 ≤ M) (hη:0<η)(hX:∀ᶠ i in f,draft Q (R i) (r i) M η H (X i))
    (p:I→ C.book.Token)
set_option quotPrecheck false
local notation "J'"=> (↑(remaining Q H):Type)
local notation "I'"=> Unit⊕J'
local notation "U'"=> Q.focus H
local notation "i!"=> (Sum.inl ():I')
def banner (Q:Rhythm I)(H:ℕ):Unit⊕ (↑(remaining Q H):Type)→I:= Sum.elim (fun _=>Q.star) Subtype.val
namespace Echo
local notation "a'"=> banner Q H
include H'
lemma afar (i:J') : Q.gap Q.star i.val ≤ n:= (Q.flip ..).trans_le (H'.reserve i.val (mem_sdiff.mp i.property).2)
def specialGap (Q:Rhythm I)(n H:ℕ)(i j:Unit⊕ (↑(remaining Q H):Type)) := if i = .inl () ∧ j=.inl () then n else Q.gap (banner Q H i) (banner Q H j)
-- ISSUE gap star-star bought maybe too SMALL? set to H.J.Not affect.
def shrink : Rhythm (Unit⊕ J') where
  star := Sum.inl ()
  limit:= Q.limit
  age := Sum.elim (fun _=>n) (fun i=>Q.age i.val)
  gap:=specialGap Q n H
  bounded i:=by rcases i with i|i; exact H'.before.le.trans H'.atMost; exact Q.bounded _
  loose i j:= by
     rcases i with ⟨⟨⟩⟩|i <;>rcases j with ⟨⟨⟩⟩|j
     · simp [specialGap]

     · simp [specialGap,banner]; exact afar H' j
     · simp [specialGap,banner]; exact Q.loose ..
     simp [specialGap,banner]; exact Q.loose ..
  flip i j:=by unfold specialGap; rw [Q.flip]; simp only [and_comm]
  fan i j k:=by
     -- tri cases simpler via structure.Fan not invariant diag for own-parent
     rcases i with ⟨⟨⟩⟩|i <;>rcases j with ⟨⟨⟩⟩|j <;>rcases k with ⟨⟨⟩⟩|k
     · simp [specialGap]
     · exact min_le_right ..
     · exact (min_le_left ..).trans (by simpa [specialGap,banner] using (afar H' j))
     · simpa [specialGap,banner] using Q.fan Q.star j.val k.val
     · exact min_le_left ..
     · simpa [specialGap,banner] using Q.fan i.val Q.star k.val
     · simpa [specialGap,banner] using Q.fan i.val j.val Q.star
     simpa [specialGap,banner] using Q.fan i.val j.val k.val

local notation "F'"=> shrink H'
include B hm hη hX
lemma horizon : ∀ᶠ i in f,draft (shrink H') (R i) (r i) (M+M) (η/2) 0 (substituted U' (X i)):=by
    have hp:= H'.exists_.symm.le; have hh:=H'.atMost; have ht:=H'.before
    have he(j:J'):∀ᶠ i in f,η/2*r i (Q.gap Q.star j.val)< ‖X i j.val‖:= B.ear hp hm hX j.val (mem_sdiff.mp j.property).2 rfl (lt_of_le_of_lt (afar H' j) ht) hη
    filter_upwards [hX,eventually_all.mpr he, (eventually_all_finset (Iic Q.limit)).mpr (fun i hi=> (B.ahead (mem_Iic.mp hi)|>.pos.and ((B.rates i (mem_Iic.mp hi)).pos))), eventually_all.mpr (fun j:J'=> B.in_order (le_trans (afar H' j) ht.le) hh)] with i hv hh ht hi
    let R' t:= M*R i t; have hH(i'): 0≤ M→ i' ≤ Q.limit → 0 ≤ R' i':= fun h hp=> mul_nonneg h (ht i' (mem_Iic.mpr hp)|>.1.le); let x:= X i; let F:= substituted U' (X i); have hx(j k:I'):j≠k → (shrink H').gap j k= Q.gap (banner Q H j) (banner Q H k):= fun h=> if_neg (show ¬ (j=i! ∧ k=i!) from (fun hp=> h (hp.1.trans hp.2.symm))); have hy(j:J'): Q.star≠j.val:=fun h=> (mem_sdiff.mp j.property).2 (h ▸ (Q.on_focus).2 (Q.yes ..));
    have hw(j:J'): ‖x j.val‖ ≤ (M+M)*R i (Q.gap Q.star j.val):= by
       linarith only [hv.hostel,norm_sub_norm_le (x j.val) (x Q.star), hv.pair _ _ (hy j),norm_sub_rev (X i j.val) (X i Q.star), mul_le_mul_of_nonneg_left (hi j|>.2) hm]
    refine ⟨fun j k h=>?_ ,fun j k h=>?_,?_⟩
    · rw [hx j k h]; rcases j with ⟨⟨⟩⟩|j <;> rcases k with ⟨⟨⟩⟩|k <;> (try contradiction) <;> unfold substituted <;> dsimp only [banner, beside, chunk,sole,Sum.elim]
      · simpa using hw k
      · rw [Q.flip]; simpa using hw j
      linarith only [hv.pair _ _ (Subtype.val_injective.ne (fun he=> h (congr_arg Sum.inr he))), hH _ hm (GapHomebound (Q:=Q) j.val k.val)]
    · rw [hx j k h]; rcases j with ⟨⟨⟩⟩|j <;> rcases k with ⟨⟨⟩⟩|k <;> (try contradiction) <;> unfold substituted <;> dsimp only [banner, beside, chunk,sole,Sum.elim]
      · simpa using hh k
      · rw [Q.flip]; simpa using hh j
      let w:= Q.gap j.val k.val; have hv':0<r i w:=ht w (mem_Iic.mpr (GapHomebound ..))|>.2; exact (by linarith only [hv.reserve _ _ (Subtype.val_injective.ne (fun he=> h (congr_arg Sum.inr he))), mul_pos hη hv'])
    change ‖(0:E4)‖≤ _; rw [norm_zero]; exact mul_nonneg (add_nonneg hm hm) (ht _ (mem_Iic.mpr (Nat.zero_le _))|>.1.le)
local notation "Πa"=> priceSet
omit B hm hη hX in
lemma anew (v:C.book.Token)(r:ℕ→ℝ): priceSet (shrink H') univ (beside (sole v) (chunk (remaining Q H) p)) r= r n ^ v.fst* priceSet Q (remaining Q H) p r:=by
    unfold priceSet; rw [Fintype.prod_sum_type]; change (∏ i:Unit,r n ^ v.fst)*(∏ i: J',r (Q.age i.val)^(p i.val).fst)= _; simp only [prod_const,card_univ,Fintype.card_unique,pow_one]; congr 1; exact prod_coe_sort (remaining Q H) (fun i=>r (Q.age i)^(p i).fst)
omit B hm hη hX H' in
lemma full (s:Finset I)(r:ℕ→ℝ): priceSet Q univ p r=priceSet Q s p r * priceSet Q (univ\ s) p r:=by unfold priceSet; rw [mul_comm,prod_sdiff (subset_univ s)]
variable [f.NeBot] {W r' D} (P':LogPackage C W r' D)
variable (w: Mode U.sector.derivatives) {φ:Filter (ℕ×ℕ)} [φ.NeBot] (h:φ ≤ F.fuse)
    (L':Services C F S)(V:MatrixTicket (C:=C) S U.sector.derivatives φ){X':Prescription U.sector.derivatives}(hY:X'.Coherent)
    {z:L→ E4}
include U P' h V L' hY
lemma shifted (v:C.book.Token)(hz:∀ᶠ i in f,‖z i‖≤R i 0*M): Wallet f T (fun i=> (R i n ^ v.fst * priceSet Q (remaining Q H) p (R i)/ R i 0 ^ w.fst :ℝ) • X'.ope w (substituted (Q.focus H) (X i)) (beside (sole v) (chunk (remaining Q H) p)) (z i)):=by
    simp_rw [← anew (p:=p) H']; apply direct U (hh:=Nat.zero_le _) (hm:=add_nonneg hm hm) (hη:=half_pos hη) (hX:= horizon B H' hm hη hX) _ w h L' P' V hY (Q:=shrink H') (X:=_) (show Border f T (shrink H'|>.limit) R r α from B); filter_upwards [hz,(B.ahead (Nat.zero_le _)).pos] with i hi hp using (hi.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hm) hp.le))
end Echo
end YM.OPE.Log.Reels
