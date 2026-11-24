import YM.RegulatorIR.Budget.TraceBound

/-!
Core loop estimate.

1. A closure or inversion cycle attaches the output to the singular sites
of the inversion quotient; obtain a bound with no overall period-volume,
using only a negative power counting cost at those sites. This is for the
*labelled projections* of field-dependent vacuum actions, not bounding the
raw extensive scalar.

2. A localized source diagram paying this cycle has remoteness gain, allowing
small restriction error when period is large. Keep the no-field output here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget
open Set Function Tuple Deck Layer Packet Motion Spatial Tariff
open scoped NNReal ENNReal Topology BigOperators Classical
variable {X Y:Type}{P l:ℝ}{r:ℕ}(A:Deck P X Y)(hp:0<P)(hl:0<l)
variable {a d:ℝ≥0∞} (u b:ℕ) {T:Packet X (r+2)}{K:Layer X X}

private lemma spanned (x:Tuple X r)(p:X×X)(W:Tariff X): W.road p.1 p.2≤ W.diameter (linked x p):=by
 have h:= W.diameter_ge (linked x p) 0 (0:Fin (r+1)).succ
 rw [link_first,link_second] at h; exact h

lemma loop_error_cost (h:Layer.Sym A A K)(H:A.Ready T)(hc:Layer.row K (native l hl (u+b)) A.pos A.pos a)(ha:a≠⊤)
    (hT:localQ ((native l hl ((u+b)+(u+b))).uses A.pos) T d)(hd:d≠⊤) (i:Fin r) :
   markQ ((Premium.remnant P hp l hl u).uses A.atO) (loop (A.deckSum T) (wrapL A A K)-A.deckSum (loop T K)) ≤ a*d *∑' y, (amount l b (singular P (A.atO y)))⁻¹ := by
 let K' := wrapL A A K
 let E: Packet Y r:= loop (A.deckSum T) K'-A.deckSum (loop T K); let Z:=repeatK A K'-K
 let B := (Premium.remnant P hp l hl u).uses A.atO; let k:=u+b; let D:= (native l hl k).uses A.pos; let V:= (native l hl (k+k)).uses A.pos
 have he (j:Y) : let R:=amount l b (singular P (A.atO j));
     Stalk.scopeQ (fun x:Tuple Y r=>x i) E B.width j ≤ a*d*R⁻¹:=by
    let m:=A.place j
    intro R
    have hR : R≠0:= ne_of_gt (zero_lt_one.trans_le (amount_unit hl _ (singular_nonneg ..))); have hR': R≠⊤:= by unfold R amount; finiteness
    suffices hr:Stalk.scopeQ (fun x:Tuple Y r=>x i) E B.width j*R≤a*d by
       exact le_trans (Eq.ge (show (Stalk.scopeQ _ E B.width j * R) * R⁻¹=Stalk.scopeQ (fun x:Tuple Y r=>x i) E B.width j from by rw [mul_assoc,ENNReal.mul_inv_cancel hR hR',mul_one])) (mul_le_mul_left hr _)
    have he (x:Hold i j): E x.val= Stalk.collect (A.projectedHold i m) ((A.dyed (loop T Z)) ∘ Subtype.val) (⟨x.val,x.property.trans (A.placed _).symm⟩:Hold i (A.orbit m)):=
       (loop_gap_lodge A K' h H hT hd (row_to_sup hc) ha (row_to_sup (row_cost A A K hp hl (u+b) hc)) ha x.val i m ((A.placed _).trans x.property.symm)).trans (A.parcel (loop T Z) i m ⟨x.val,x.property.trans (A.placed _).symm⟩)
    let g:Hold i m → Hold i (A.orbit m) := A.projectedHold i m
    let f : Hold i m → ℝ := fun z=>A.dyed (loop T Z) z.val
    have HE : Stalk.scopeQ (fun x:Tuple Y r=>x i) E B.width j≤ quota f (fun z=>B.width (A.project z.val)):= by
      let d' : Hold i j ≃ Hold i (A.orbit m):= Equiv.subtypeEquiv (Equiv.refl _) fun z=> by simp [m,A.placed]
      unfold Stalk.scopeQ
      rw [funext he]; exact le_trans (quota_perm d' (Stalk.collect g f) (fun z=>B.width z.val)).le (Stalk.quota_collect g f _)
    apply (mul_le_mul_left HE R).trans
    rw [quota_eq _ (fun z: Hold i m=>loop T Z z.val) _ (fun z=>A.dyed_cost ..),← quota_raised]
    apply (inside_quota (fun z:Hold i m=>curve T Z z.val) _).trans
    refine le_trans ?_ (mul_le_mul_right (hT i.succ.succ m) a)
    unfold Stalk.scopeQ quota
    rw [← price_hold (fun x=> ‖T x‖ₑ*V.diameter x) i m, ← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum; intro x; rw [← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro w
    dsimp only; let t:= linked x.val w
    have hv: R=amount l b (singular P (A.pos (x.val i))):=by rw [show x.val i=m from x.property]; rfl
    rw [hv, curve,enorm_mul,mul_comm ‖Z ..‖ₑ]
    let g:=‖T t‖ₑ; let X':=‖Z w.1 w.2‖ₑ; let Y':= D.diameter t
    let S:=amount l k (singular P (A.pos w.2))
    have hh :X'*S ≤ a*D.road w.1 w.2 := wrong_image A h hl k hc ha hp ..
    have he' := hh.trans (mul_le_mul_right (spanned x.val w D) _)
    apply (mul_le_mul_right (length_trace A hp hl u b x.val w i) (g*X')).trans
    change g*X'*(Y'*S)≤ a*(g*V.diameter t)
    rw [show V.diameter t=Y'*Y' from diam_plus ..,mul_mul_mul_comm]
    exact (mul_le_mul_right he' _).trans_eq (by ring)
 change quota E _≤a*d*_
 rw [← Stalk.total (fun x:Tuple Y r=>x i),← ENNReal.tsum_mul_left]
 exact ENNReal.tsum_le_tsum he

lemma loop_source_cost (h:Layer.Sym A A K)(hc:Layer.row K (native l hl b) A.pos A.pos a)(ha:a≠⊤)(x:Room)
    (hT: markQ ((Premium.rooted (native l hl ((u+b)+b)) x).uses A.pos) T ≤ d)(hd:d≠⊤):
   markQ ((Premium.rooted (onFold P hp l hl u) x).uses A.atO) (loop (A.scroll T) (wrapL A A K)-A.scroll (loop T K)) * amount l b (singular P x) ≤ a*d := by
 let K':= wrapL A A K; let Z:= repeatK A K'-K
 let B:= (Premium.rooted (onFold P hp l hl u) x).uses A.atO
 let V:= (Premium.rooted (native l hl ((u+b)+b)) x).uses A.pos
 let D:= (Premium.rooted (native l hl b) x).uses A.pos
 let C:= (Premium.rooted (native l hl (u+b)) x).uses A.pos; let W:= (native l hl b).uses A.pos
 let F:=loop T Z
 have hs: Summable T:= quota_summable (w:=V.width) (fun z=>V.width_unit z) (ne_top_of_le_ne_top hd hT)
 let R:=amount l b (singular P x)
 rw [loop_gap_scroll A K' hs (row_to_sup hc) ha (row_to_sup (row_cost A A K hp hl b hc)) ha]; unfold markQ scroll
 apply (mul_le_mul_left (Stalk.quota_collect A.project (A.dyed F) B.width) _).trans
 rw [quota_eq _ F _ (fun z=> A.dyed_cost ..),← quota_raised]
 apply (inside_quota (curve T Z) _).trans
 refine le_trans ?_ (mul_le_mul_right hT _)
 change (∑' z,quota (curve T Z z) fun _=> B.width (A.project z)*R) ≤ a*quota T V.width
 unfold quota; rw [← price_link (T:=fun z=> ‖T z‖ₑ * V.width z), ← ENNReal.tsum_mul_left]
 apply ENNReal.tsum_le_tsum; intro z; rw [← ENNReal.tsum_mul_left];apply ENNReal.tsum_le_tsum;intro p; dsimp only
 rw [curve,enorm_mul,mul_comm ‖Z ..‖ₑ]; let t:=linked z p
 have hh:= (show ‖Z p.1 p.2‖ₑ * amount l b (singular P (A.pos p.2)) ≤ a * W.road p.1 p.2 from wrong_image A h hl b hc ha hp ..).trans (mul_le_mul_right (le_trans (spanned z p W) (D.width_diameter t)) a)
 apply (mul_le_mul_right (tariff_center A hp hl ..) (‖T t‖ₑ * ‖Z ..‖ₑ)).trans
 rw [mul_mul_mul_comm]
 apply (mul_le_mul_right hh _).trans
 rw [show V.width t=C.width t * D.width t from width_plus ..]; exact le_of_eq (by ring)
end YM.RegulatorIR.Budget
