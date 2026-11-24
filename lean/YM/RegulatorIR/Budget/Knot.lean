import YM.RegulatorIR.Budget.SplicePeriod

/-! Binary heat gluing with all errors in the same norms. In particular a
mark attached to the inherited point defect pays an IR gain in addition to
the final weight about the external cluster. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget
open Function Tuple Motion Layer Deck Packet Tariff Spatial
open scoped BigOperators Topology NNReal ENNReal Classical
variable {X Y : Type} {P l:ℝ} {r s:ℕ}

namespace Packet
variable (K:Layer X X)

def knot (T:Packet X (r+1))(U:Packet X (s+1)) : Packet X (r+s):= splice T (ray 0 U K)
lemma knot_ready {K:Layer X X} (A : Deck P X Y){T:Packet X (r+1)}{U:Packet X (s+1)}(h:A.Ready T)(he:A.Ready U)(hg:Layer.Sym A A K): A.Ready (knot K T U) := splice_ready A h (ray_ready A _ he hg)
lemma knot_local {K:Layer X X}{T:Packet X (r+1)}{U:Packet X (s+1)}{A:Tariff X}{c d v:ℝ≥0∞}(hc:row K A id id c)(hh:row (swap K) A id id c)(h:localQ A T d)(he:localQ A U v) : localQ A (knot K T U) (d*(v*c)) := splice_local _ _ h (ray_local _ _ hc hh he)
lemma knot_mark {K:Layer X X}(T:Packet X (r+1)){U:Packet X (s+1)}{A:Tariff X}(B:Premium A){c d:ℝ≥0∞}(hc:row K A id id c)(hh:row (swap K) A id id c)(he:localQ A U d) : markQ B (knot K T U) ≤ markQ B T*(d*c):=
 splice_mark _ _ (ray_local _ _ hc hh he)
-- when inherited defect on second, but first is unmarked vacuum (anchored bounds), still need allocation
lemma flip_width {A:Tariff X}(B:Premium A)(p:Tuple X r)(q:Tuple X s) : B.width (Fin.append p q)=B.width (Fin.append q p):= by
 have H {r s:ℕ} (p:Tuple X r)(q:Tuple X s): B.width (Fin.append p q)≤ B.width (Fin.append q p) := by
    apply B.width_le ((diameter_swap ..).le.trans (B.width_diameter _));intro i
    induction i using Fin.addCases <;> rename_i i
    · simpa using B.width_ge (Fin.append q p) (Fin.natAdd s i)
    simpa using B.width_ge (Fin.append q p) (Fin.castAdd r i)
 exact le_antisymm (H ..) (H ..)
lemma knot_remnant {K:Layer X X}{T:Packet X (r+1)}(U:Packet X (s+1)){A:Tariff X}(B:Premium A){c d:ℝ≥0∞}(hh:row (swap K) A id id c)(he:localQ A T d) : markQ B (knot K T U) ≤ markQ B U*c*d:=by
 unfold knot
 let V:= ray 0 U K
 have h:markQ B (splice T V)=markQ B (splice V T):=by
   unfold markQ quota
   rw [← (Fin.appendEquiv r s).tsum_eq,← ((Equiv.prodComm (Tuple X r) (Tuple X s)).trans (Fin.appendEquiv s r)).tsum_eq];apply tsum_congr; intro i
   change ‖splice T V (Fin.append i.1 i.2)‖ₑ * _ = ‖splice V T (Fin.append i.2 i.1)‖ₑ * _
   exact congr_arg₂ (·*·) (congr_arg _ (twist T V i.1 i.2)) (flip_width B i.1 i.2)
 exact le_trans h.le ((splice_mark _ _ he).trans (mul_le_mul_left (ray_mark _ _ hh) _))
lemma knot_copy {K:Layer X X}(A:Deck P X Y){T:Packet X (r+1)}{U:Packet X (s+1)}{H:Tariff X}{a b c:ℝ≥0∞}(hk:Layer.Sym A A K)(hr:row K H id id c)(hw:row (swap K) H id id c)
  (h:A.Ready T)(hh:A.Ready U) (ht:localQ H T a)(hu:localQ H U b)(ha:a≠⊤)(hb:b≠⊤)(hc:c≠⊤)[Fintype Y](i:Fin (r+s)):
  knot (wrapL A A K) (A.deckSum T) (A.deckSum U)= A.deckSum (knot K T U):=by
 unfold knot; rw [← ray_period A _ hu hr hb hc hk hh]
 exact funext fun p=>splice_projection A (ray_ready A _ hh hk) (ray_local _ _ hr hw hu) (by finiteness) h ht ha p i
lemma knot_copy_mark {K:Layer X X}(A:Deck P X Y){T:Packet X (r+1)}{U:Packet X (s+1)}{H:Tariff X}{b c:ℝ≥0∞}(hk:Layer.Sym A A K)(hr:row K H id id c)(hw:row (swap K) H id id c)
  (hh:A.Ready U) (ht:quota T 1 ≠ ⊤)(hu:localQ H U b)(hb:b≠⊤)(hc:c≠⊤)[Fintype Y]:
  knot (wrapL A A K) (A.scroll T) (A.deckSum U)=A.scroll (knot K T U) :=by unfold knot; rw [← ray_period A _ hu hr hb hc hk hh]; exact splice_marked A (ray_ready A _ hh hk) (ray_local _ _ hr hw hu) (by finiteness) ht

end Packet

section Fare
variable (P)(hp:0<P)(l:ℝ)(hl:0<l)(x:X→Room)(a:Room)(u b:ℕ)

lemma defect_width (j : ℕ) (z:Tuple X r): ((Premium.remnant P hp l hl j).uses x).width z=((Premium.remnant P hp l hl 1).uses x).width z^j := (Premium.width_pow _ _ _ _ _ (fun _ _=>pow_amount ..) (fun _=>pow_amount ..) _).symm
lemma source_width (j : ℕ)(z:Tuple X r) : ((Premium.rooted (onFold P hp l hl j) a).uses x).width z=((Premium.rooted (onFold P hp l hl 1) a).uses x).width z^j := (Premium.width_pow _ _ _ _ _ (fun _ _=>pow_amount ..) (fun _=>pow_amount ..) _).symm
lemma joint_fare (p:Tuple X r)(q:Tuple X s)(v:X):
   ((Premium.rooted (onFold P hp l hl u) a).uses x).width (Fin.append p q)*amount l b (singular P a) ≤
     ((Premium.rooted (onFold P hp l hl (u+b)) a).uses x).width (Fin.cons v p)* ((Premium.remnant P hp l hl (u+b)).uses x).width (Fin.cons v q):=by
 let I m:= (Premium.rooted (onFold P hp l hl m) a).uses x
 let E m:= (Premium.remnant P hp l hl m).uses x
 apply le_trans ?_ (le_of_eq (show (I u).width (Fin.cons v p)*(I b).width (Fin.cons v p)*((E u).width (Fin.cons v q)*(E b).width (Fin.cons v q))=((I (u+b)).width (Fin.cons v p) *(E (u+b)).width (Fin.cons v q)) from ?_))
 · rw [mul_mul_mul_comm]
   apply mul_le_mul'
   · refine (Tuple.shared_mark p q v _ (I u)).trans (mul_le_mul_right ((E u).width_diameter (Fin.cons v q)) _)
   have h := (I b).width_ge (Fin.cons v p) 0; rw [Fin.cons_zero] at h
   have he:= (E b).width_ge (Fin.cons v q) 0; rw [Fin.cons_zero] at he
   apply (Premium.travel (Premium.remnant P hp l hl b) a (x v)).trans; rw [mul_comm]; exact mul_le_mul' h he
 dsimp only [I,E]
 rw [source_width P hp l hl x a (u+b), source_width P hp l hl x a u,source_width P hp l hl x a b,
     defect_width P hp l hl x (u+b),defect_width P hp l hl x u,defect_width P hp l hl x b,pow_add,pow_add]

lemma remnant_splice (T:Packet X (r+1))(U:Packet X (s+1)) :
    markQ ((Premium.rooted (onFold P hp l hl u) a).uses x) (splice T U)* amount l b (singular P a) ≤
     markQ ((Premium.rooted (onFold P hp l hl (u+b)) a).uses x) T* markQ ((Premium.remnant P hp l hl (u+b)).uses x) U:=by
 unfold markQ
 let I:=(Premium.rooted (onFold P hp l hl (u+b)) a).uses x
 let E:=(Premium.remnant P hp l hl (u+b)).uses x
 let B:=(Premium.rooted (onFold P hp l hl u) a).uses x
 rw [← quota_raised,← quota_perm (Fin.appendEquiv r s)]
 change quota (fun z:Tuple X r × Tuple X s => splice T U (Fin.append z.1 z.2)) _≤_
 simp_rw [splice_at]
 apply (inside_quota (fun (z:Tuple X r × Tuple X s) w=>lace T U z.1 z.2 w) _).trans
 let f : Tuple X r × Tuple X s → X → Tuple X (r+1) × Tuple X (s+1):= fun z w=>(Fin.cons w z.1,Fin.cons w z.2)
 have hf : Injective (Function.uncurry f) := by
   rintro ⟨⟨p,q⟩,a⟩ ⟨⟨u,v⟩,b⟩ hh
   have h:Tuple.glueEquiv X r (a,p)= Tuple.glueEquiv X r (b,u):= congr_arg Prod.fst hh
   have he:Tuple.glueEquiv X s (a,q)= Tuple.glueEquiv X s (b,v):=congr_arg Prod.snd hh
   rcases Prod.mk.inj ((Tuple.glueEquiv X r).injective h) with ⟨rfl,rfl⟩; rw [(Prod.mk.inj ((Tuple.glueEquiv X s).injective he)).2]
 unfold quota
 let G : Tuple X (r+1) × Tuple X (s+1) → ℝ≥0∞:= fun z=>(‖T z.1‖ₑ * I.width z.1)*(‖U z.2‖ₑ * E.width z.2)
 change (∑' (z:Tuple X r × Tuple X s) (y:X), ‖lace T U z.1 z.2 y‖ₑ*(B.width (Fin.append z.1 z.2)* amount l b (singular P a))) ≤ _
 rw [← ENNReal.tsum_prod]
 apply le_trans _ (le_trans (ENNReal.tsum_comp_le_tsum_of_injective hf G) ?_)
 · apply ENNReal.tsum_le_tsum; rintro ⟨⟨p,q⟩,v⟩
   change ‖lace T U p q v‖ₑ * (B.width _*_)≤ (‖T (Fin.cons v p)‖ₑ*_) * (‖U _‖ₑ*_)
   rw [lace,enorm_mul]; exact (mul_le_mul_right (joint_fare P hp l hl x a u b p q v) _).trans_eq (mul_mul_mul_comm ..)
 rw [ENNReal.tsum_prod']; simp_rw [G,ENNReal.tsum_mul_left,ENNReal.tsum_mul_right]; exact le_rfl

lemma crossed_mark (T:Packet X (r+1))(U:Packet X (s+1)) (K:Layer X X){c : ℝ≥0∞}(hc:row (swap K) (onFold P hp l hl (u+b)) x x c):
    markQ ((Premium.rooted (onFold P hp l hl u) a).uses x) (knot K T U)* amount l b (singular P a) ≤
      markQ ((Premium.rooted (onFold P hp l hl (u+b)) a).uses x) T* (markQ ((Premium.remnant P hp l hl (u+b)).uses x) U*c):=
 (remnant_splice P hp l hl x a u b T (ray 0 U K)).trans (mul_le_mul_right (ray_mark 0 U (A:=((onFold P hp l hl (u+b)).uses x)) hc) _)
end Fare
end YM.RegulatorIR.Budget
