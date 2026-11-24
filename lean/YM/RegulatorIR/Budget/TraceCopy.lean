import YM.RegulatorIR.Budget.Covariance

/-! Complete lifting algebra for loop discrepancy. No hidden shortest path
replacement. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget
open Set Function Tuple Deck Layer Packet Motion Spatial
open scoped NNReal ENNReal Topology BigOperators Classical
variable {X Y Z : Type} {r : ℕ} {P:ℝ} (A: Deck P X Y)

namespace Copies
section Schema
-- either select all lifts of the output (tested series) or anchor one leg (bulk)
variable (T:Packet X (r+2)) (v:Tuple Y r) (f: Z→Tuple X r)
def pick : Z × (X×X) → (Y × Y):= fun i=>(A.orbit i.2.1,A.orbit i.2.2)
def aboard (i:Z × (X×X)) := T (linked (f i.1) i.2)
def assist (K:Layer X X) (i:Z × (X×X)) := curve T K (f i.1) i.2 * A.polish (f i.1)
variable (h: Summable (aboard T f))
include h
lemma assistable (K : Layer X X){u:ℝ≥0∞}(hh:Layer.height K u)(hc:u≠⊤): Summable (assist A T f K):=by
 apply quota_summable (w:=1) (fun _=> le_rfl)
 rw [quota_base]
 have he : u * ∑' i,‖aboard T f i‖ₑ ≠ ⊤ := ENNReal.mul_ne_top hc (tsum_enorm_ne_top_iff_summable_norm.mpr (by simpa only [Real.norm_eq_abs] using summable_abs_iff.mpr h))
 apply ne_top_of_le_ne_top he
 rw [← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro i; unfold assist curve
 rw [enorm_mul,enorm_mul,Deck.polish_cost,mul_one]; exact mul_le_mul_left (hh ..) _
lemma returnCost (K : Layer X X) {u:ℝ≥0∞}(hh:Layer.height K u)(hc:u≠⊤):
   (∑' z,A.dyed (loop T K) (f z))=∑' i,assist A T f K i :=by
 rw [(assistable A T f h K hh hc).tsum_prod]
 unfold assist dyed loop; simp_rw [tsum_mul_right]
lemma cost_sub (K H:Layer X X){u v:ℝ≥0∞}(hq:Layer.height K u)(hp:Layer.height H v)(hc:u ≠ ⊤)(hd:v ≠ ⊤):
   (∑' z,A.dyed (loop T K) (f z)) - (∑' z,A.dyed (loop T H) (f z)) = ∑' z,A.dyed (loop T (K-H)) (f z) := by
 have he : Layer.height (K-H) (u+v):=by
   intro x y
   change ‖K x y-H x y‖ₑ≤u+v
   rw [sub_eq_add_neg]
   apply (enorm_add_le ..).trans; rw [enorm_neg]; exact add_le_add (hq ..) (hp ..)
 rw [returnCost A T f h K hq hc,returnCost A T f h H hp hd,returnCost A T f h _ he (by finiteness)]
 rw [← (assistable A T f h K hq hc).tsum_sub (assistable A T f h H hp hd)]
 apply tsum_congr; intro i; change _ = _ * _ ; simp_rw [assist,curve,Pi.sub_apply, sub_mul]
lemma schema (U : Packet Y (r+2)) (K:Layer Y Y) {c:ℝ≥0∞}(H:Layer.height K c)(hc:c≠⊤) (hh:∀ i:Y×Y, U (linked v i)=
     Stalk.collect (pick A) (fun p:Z × (X × X)=> A.dyed T (linked (f p.1) p.2)) i) :
     loop U K v=∑' z,A.dyed (loop T (repeatK A K)) (f z):= by
   rw [returnCost A T f h _ (repeat_cap A H) hc]
   rw [← Stalk.collected_sum (pick A) (assistable A T f h _ (repeat_cap A H) hc)]
   unfold loop; apply tsum_congr; intro p
   rw [curve,hh]; unfold Stalk.collect; rw [← tsum_mul_left]
   apply tsum_congr; intro i; obtain ⟨⟨z,x,y⟩,rfl⟩:=i
   unfold pick dyed assist curve repeatK; dsimp only; rw [A.link_polish]; ring
end Schema
section Holds
def decompression (v : Tuple Y r) i a p : Stalk (pick A (Z:=Nest A v i a)) p ≃ Nest A (linked v p) i.succ.succ a:=by
 refine Equiv.ofBijective (fun s=> ⟨linked s.val.1.val s.val.2,?_,?_⟩) ⟨?_,?_⟩
 · change A.orbit ∘ linked _ _= _;rw [map_link, show A.orbit ∘ s.val.1.val=v from s.val.1.property.1]; exact congr_arg _ s.property
 · rw [link_here]; exact s.val.1.property.2
 · rintro ⟨⟨x,p⟩,hp⟩ ⟨⟨y,q⟩,hq⟩ he
   have he := (linkEquiv r X).injective (show linkEquiv r X (x.val,p)=linkEquiv r X (y.val,q) from Subtype.mk.inj he)
   exact Subtype.ext (Prod.ext (Subtype.ext (Prod.mk.inj he).1) (Prod.mk.inj he).2)
 rintro ⟨x,h,k⟩
 obtain ⟨⟨z,y⟩,rfl⟩:= (linkEquiv r X).surjective x
 change A.orbit ∘ linked z y= linked v p at h
 rw [map_link] at h
 have he := (linkEquiv r Y).injective (show linkEquiv r Y (A.orbit ∘ z,(A.orbit y.1,A.orbit y.2)) = linkEquiv r Y (v,p) from h)
 have hh:= Prod.mk.inj he
 change linked z y i.succ.succ = a at k; rw [link_here] at k
 exact ⟨⟨(⟨z,hh.1,k⟩,y),hh.2⟩,rfl⟩

def compression (v:Tuple Y r) p: Stalk (pick A (Z:=Stalk A.project v)) p ≃ Stalk A.project (linked v p):= by
 refine Equiv.ofBijective (fun s=>⟨linked s.val.1.val s.val.2,?_⟩) ⟨?_,?_⟩
 · change A.orbit ∘ linked _ _ = _; rw [map_link,show A.orbit ∘ s.val.1.val = v from s.val.1.property]; exact congr_arg _ s.property
 · rintro ⟨⟨x,p⟩,hp⟩ ⟨⟨y,q⟩,hq⟩ he
   have he := (linkEquiv r X).injective (show linkEquiv r X (x.val,p)=linkEquiv r X (y.val,q) from Subtype.mk.inj he)
   exact Subtype.ext (Prod.ext (Subtype.ext (Prod.mk.inj he).1) (Prod.mk.inj he).2)
 rintro ⟨x,hx⟩
 obtain ⟨⟨z,y⟩,rfl⟩:= (linkEquiv r X).surjective x
 change A.orbit ∘ linked z y = linked v p at hx
 rw [map_link] at hx
 have hh:= Prod.mk.inj ((linkEquiv r Y).injective hx)
 exact ⟨⟨(⟨z,hh.1⟩,y),hh.2⟩,rfl⟩
lemma nest_summable {T:Packet X (r+2)} {s:Tariff X}{b:ℝ≥0∞}(h:localQ s T b)(hc:b ≠ ⊤) (u:Tuple Y r) (i:Fin r)(a:X) : Summable (aboard T (Subtype.val : Nest A u i a→_)):= by
 have ht: Summable (T ∘ (Subtype.val : Hold i.succ.succ a →_)) := quota_summable (w:=fun z=>s.diameter z.val) (fun z=> s.diameter_unit z.val) (ne_top_of_le_ne_top hc (h ..))
 let e : A.Nest u i a → Hold i a := fun z=>⟨z.val,z.property.2⟩
 have he:Injective e:= fun x y h=> Subtype.ext (Subtype.mk.inj h)
 have hW:= he.prodMap (Function.injective_id (α:=X×X))
 exact ht.comp_injective ((linkHold i a).injective.comp hW)
lemma stalk_summable {T:Packet X (r+2)} (h:Summable T) (u:Tuple Y r) : Summable (aboard T (Subtype.val : Stalk A.project u→_)):=
 h.comp_injective ((linkEquiv r X).injective.comp (Subtype.val_injective.prodMap (Function.injective_id (α:=X×X))))
end Holds
end Copies
end YM.RegulatorIR.Budget
