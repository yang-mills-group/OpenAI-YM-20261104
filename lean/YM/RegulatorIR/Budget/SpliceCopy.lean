import YM.RegulatorIR.Budget.Splice

/-!
Projection through a joined pair in the log/marked recursions. Source
anchors and vacuum anchors use the same identity but *different* sets of
lifted tuples. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget
open Function Layer Motion Tuple Packet Deck
open scoped NNReal ENNReal Topology BigOperators Classical
variable {X Y Z:Type} {P:ℝ} {r s:ℕ} (A:Deck P X Y)

namespace Deck
lemma shift_cons (y:X)(p:Tuple X r): A.polish (Fin.cons y p : Tuple X _) = A.orient y*A.polish p:=by simp [polish,Fin.prod_univ_succ]
lemma attach (p:Tuple X r)(q:Tuple X s): A.polish (Fin.append p q)= A.polish p * A.polish q:=by
 unfold polish; rw [Fin.prod_univ_add]; simp
private def endLift (q:Tuple Y s)(x:X): Stalk A.project q≃Nest A (Fin.cons (A.orbit x) q) 0 x:= by
 refine Equiv.ofBijective (fun v=>⟨Fin.cons x v.val, by change A.orbit ∘ _= _; rw [comp_cons,show A.orbit ∘ v.val=q from v.property],rfl⟩) ⟨?_,?_⟩
 · rintro v u he; exact Subtype.ext (by
      have h:=congr_arg (@Fin.tail s (fun _=> X)) (show Fin.cons (α:=fun _=>X) x v.val=Fin.cons x u.val from congr_arg Subtype.val he); simpa using h)
 rintro ⟨v,h,h'⟩; let z:=Fin.tail v
 have hv : A.project z=q := funext fun i=>by
     have hh:=congr_fun h i.succ
     rw [Fin.cons_succ] at hh; exact hh
 exact ⟨⟨z,hv⟩,Subtype.ext ((congr_arg (fun y=> (Fin.cons y z:Tuple X _)) h'.symm).trans (Fin.cons_self_tail ..))⟩
lemma based {U:Packet X (s+1)} (h:A.Ready U)(q:Tuple Y s)(x:X):
    A.deckSum U (Fin.cons (A.orbit x) q)=∑' v:Stalk A.project q, A.dyed U (Fin.cons x v.val) := by
 rw [A.deck_pivot h (Fin.cons (A.orbit x) q) 0 x rfl]; unfold Deck.lodge
 exact ((A.endLift q x).tsum_eq _).symm
end Deck

lemma splice_ready {T:Packet X (r+1)} (h:A.Ready T) {U:Packet X (s+1)} (hh:A.Ready U): A.Ready (splice T U):=by
 apply (A.ready_iff _).mpr; intro d x
 obtain ⟨⟨p,q⟩,hp⟩:= (Fin.appendEquiv r s).surjective x; subst x
 change splice T U (_ ∘ Fin.append p q)= d.sign^(r+s)* splice T U (Fin.append p q)
 rw [Tuple.comp_append,splice_at,splice_at,← tsum_mul_left,← (A.wind d).tsum_eq]; apply tsum_congr; intro a
 unfold lace; rw [← Tuple.comp_cons,← Tuple.comp_cons,(A.ready_iff T).mp h,(A.ready_iff U).mp hh]
 rw [pow_succ,pow_succ,mul_mul_mul_comm,mul_mul_mul_comm (d.sign^r), Motion.sign_sq, pow_add]; ring

namespace Copies
variable (T:Packet X (r+1))(U:Packet X (s+1)) (q:Tuple Y s) (z:Z→Tuple X r)

def zig (w:Z×X) := T (Fin.cons w.2 (z w.1))
def zigO (w:Z×X):= A.dyed T (Fin.cons w.2 (z w.1))
lemma zig_norm (w: Z×X) : ‖zigO A T z w‖ₑ=‖zig T z w‖ₑ:= A.dyed_cost ..

def hang (w:Tuple X s)(x):= A.dyed U (Fin.cons x w : Tuple X (s+1))
def twine (t:(Z × X) × Stalk A.project q) := zigO A T z t.1 * hang A U t.2.val t.1.2

lemma trip_cost {a b:ℝ≥0∞}{H:Tariff X}(hr: quota (zig T z) 1 ≤ a) (hU:localQ H U b):
   quota (twine A T U q z) 1 ≤ a*b := by
 apply le_trans ?_ (mul_le_mul_left hr _)
 rw [quota_base, quota_base, ENNReal.tsum_prod',← ENNReal.tsum_mul_right]
 apply ENNReal.tsum_le_tsum; intro k
 dsimp only [twine]; simp_rw [enorm_mul,ENNReal.tsum_mul_left,zig_norm]; apply mul_le_mul_right
 apply le_trans ?_ (hU 0 k.2)
 unfold Stalk.scopeQ quota; rw [← (Tuple.still k.2).tsum_eq]
 apply le_trans _ (ENNReal.tsum_comp_le_tsum_of_injective (Subtype.val_injective (p:=fun a=>A.project a=q)) _)
 apply ENNReal.tsum_le_tsum; intro u; unfold hang; rw [A.dyed_cost]
 exact le_trans (mul_one ‖U (Fin.cons k.2 u.val)‖ₑ).ge (mul_le_mul_right (H.diameter_unit (Fin.cons k.2 u.val)) _)

lemma open_tree {T':Packet Y (r+1)} (p:Tuple Y r) {a b:ℝ≥0∞}{H:Tariff X}(ha:a≠⊤)(hb:b≠⊤)(hr:quota (zig T z) 1≤a)(hU:localQ H U b)(h:A.Ready U)
    (hrp:∀ y:Y,T' (Fin.cons y p) = Stalk.collect (fun w: Z×X=>A.orbit w.2) (zigO A T z) y):
 splice T' (A.deckSum U) (Fin.append p q)=∑' w:Z × Stalk A.project q, A.dyed (splice T U) (Fin.append (z w.1) w.2.val):=by
 let I:=Stalk A.project q; let f:= twine A T U q z
 have hV:Summable f:=quota_summable (w:=1) (fun _=>le_rfl) (ne_top_of_le_ne_top (ENNReal.mul_ne_top ha hb) (trip_cost A T U q z hr hU))
 let K (w:Z×X):=zigO A T z w*A.deckSum U (Fin.cons (A.orbit w.2) q)
 have hz (w:Z×X) : K w=∑' u:I,f (w,u) := by unfold K;rw [A.based h,← tsum_mul_left]; rfl
 have hk : Summable K:= hV.prod.congr fun v=> (hz v).symm
 let M : (Z × X) × I≃ (Z × I) × X := Equiv.prodAssoc Z X I |>.trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm ..)) |>.trans (Equiv.prodAssoc ..).symm
 calc
   _ = ∑' y:Y, Stalk.collect (fun w: Z×X=>A.orbit w.2) K y := by
        rw [splice_at]; apply tsum_congr;intro y; unfold lace; rw [hrp]; unfold Stalk.collect;rw [← tsum_mul_right]; apply tsum_congr;intro a; unfold K;rw [show A.orbit a.val.2=y from a.property]
   _ = ∑' i,K i:= Stalk.collected_sum _ hk
   _ = ∑' i,f i:= by simp_rw [hz]; exact hV.tsum_prod.symm
   _ = ∑' w:(Z×I),∑' x:X,f (M.symm (w,x)) := by rw [← M.symm.tsum_eq]; exact (hV.comp_injective M.symm.injective).tsum_prod
   _ = _ := by
       apply tsum_congr; intro a; unfold dyed; rw [splice_at,← tsum_mul_right]; apply tsum_congr; intro y
       change A.dyed T (Fin.cons y (z a.1)) * A.dyed U (Fin.cons y a.2.val) = _
       unfold dyed lace; rw [A.attach,A.shift_cons,A.shift_cons]; have h : A.orient y * A.orient y=1 := A.sign_sq _
       generalize A.orient y=x at *; generalize A.polish (z a.1)=X'
       generalize T (Fin.cons y (z a.1))=t
       generalize U (Fin.cons y a.2.val)=u
       calc
        _ = (t*u)*(X'*A.polish a.2.val)*(x*x) := by ring
        _ = _:=by rw [h,mul_one]
end Copies
end YM.RegulatorIR.Budget
