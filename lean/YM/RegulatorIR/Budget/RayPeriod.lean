import YM.RegulatorIR.Budget.Ray

/-! Trees along one moved leg. Every lift along an open ray already occurs
once in the independent periodization; no traversal error. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget
open Function Motion Layer Spatial Tuple Packet Deck
open scoped BigOperators Classical Topology ENNReal NNReal
variable {X Y : Type} {P:ℝ}{r:ℕ} (A:Deck P X Y)

namespace Deck
lemma renew_polish (z:Tuple X r)(i:Fin r)(x) : A.orient x * A.polish (update z i x)= A.orient (z i)*A.polish z:=by
 unfold polish
 rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),← Finset.mul_prod_erase (s:=Finset.univ) (f:=fun j=> A.orient (z j)) (Finset.mem_univ i),update_self, ← mul_assoc,← mul_assoc,A.sign_sq,A.sign_sq]
 congr 1; apply Finset.prod_congr rfl
 intro a h; rw [update_of_ne (Finset.ne_of_mem_erase h)]

def runway (q:Tuple Y r)(i:Fin r)(x:Stalk A.orbit (q i))(y:X): Nest A q i x.val ≃ Nest A (update q i (A.orbit y)) i y where
 toFun v:= ⟨update v.val i y, (Function.comp_update A.orbit v.val ..).trans (by rw [show A.orbit ∘ v.val=q from v.property.1]), update_self ..⟩
 invFun v:= ⟨update v.val i x.val, (Function.comp_update A.orbit v.val ..).trans (by rw [show A.orbit ∘ v.val= _ from v.property.1,update_idem,show A.orbit x.val=q i from x.property, update_eq_self]), update_self ..⟩
 left_inv v:=Subtype.ext (by change update (update v.val i y) i x.val=v.val; rw [update_idem]; exact (congr_arg _ v.property.2.symm).trans (Function.update_eq_self ..))
 right_inv v:=Subtype.ext (by change update (update v.val i x.val) i y=v.val; rw [update_idem]; exact (congr_arg _ v.property.2.symm).trans (Function.update_eq_self ..))
end Deck

lemma ray_ready (i:Fin r) {T:Packet X r}(h:A.Ready T){K:Layer X X}(hh:Layer.Sym A A K): A.Ready (ray i T K):=by
 apply (A.ready_iff _).mpr; intro v x
 unfold ray; rw [← (A.wind v).tsum_eq,← tsum_mul_left]; apply tsum_congr; intro a
 unfold swivel; rw [Function.comp_apply,hh,← Function.comp_update,(A.ready_iff T).mp h]; ring

lemma local_ray_fold (i:Fin r){T:Packet X r}{K:Layer X X}{s:Tariff X}{b c:ℝ≥0∞}(h:localQ s T b)(hc:row K s id id c)
    (hb:b≠⊤)(hd:c≠⊤)(q:Tuple Y r)(x:Stalk A.orbit (q i)) :
    A.lodge (ray i T K) q i x.val= ∑'y:X,Layer.paint A A K x.val y * A.lodge T (update q i (A.orbit y)) i y :=by
 let I:= Nest A q i x.val
 let e:I→Hold i x.val:=fun a=>⟨a.val,a.property.2⟩
 have he:Injective e:= fun x y h=> Subtype.ext (Subtype.mk.inj h)
 let F (z:Hold i x.val)(y:X):=swivel i T K z.val y * A.polish z.val
 have hf : Summable (Function.uncurry F) := by
   apply quota_summable (w:=fun u => s.diameter u.1.val) (fun _=>s.diameter_unit _)
   apply ne_top_of_le_ne_top (b:=c*b) (ENNReal.mul_ne_top hd hb)
   have hx (z:Hold i x.val) y: ‖F z y‖ₑ=‖swivel i T K z.val y‖ₑ:= by unfold F; rw [enorm_mul,A.polish_cost,mul_one]
   change ∑' w : Hold i x.val × X, ‖F w.1 w.2‖ₑ*s.diameter w.1.val ≤ _
   simp_rw [hx]; rw [ENNReal.tsum_prod']; exact ray_anchored i T hc h x.val
 let G (w:I)(y:X):= F (e w) y
 have hg : Summable (Function.uncurry G) := by
    change Summable (Function.uncurry F ∘ Prod.map e (id : X → X))
    exact hf.comp_injective (he.prodMap Function.injective_id)
 unfold lodge dyed ray; simp_rw [← tsum_mul_right]
 change (∑' z:I,∑'y:X,G z y) = _
 rw [← hg.tsum_comm]; apply tsum_congr; intro y
 rw [← tsum_mul_left,← (A.runway q i x y).tsum_eq]; apply tsum_congr; intro z
 change K (z.val i) y * T (update z.val i y)* A.polish z.val= paint A A K x.val y * (T (update z.val i y)*A.polish _)
 have hx:z.val i=x.val:=z.property.2; have hu:= A.renew_polish z.val i y;rw [hx] at hu
 unfold paint; rw [hx]
 change _ = (_*(_*_)) * (_*A.polish (update z.val i y))
 calc
   _ = K x.val y*T (update z.val i y)* A.polish z.val * (A.orient x.val * A.orient x.val) := by rw [A.sign_sq,mul_one]
   _ = K x.val y*T (update z.val i y) * A.orient x.val * (A.orient x.val * A.polish z.val) := by ring
   _ = _ := by rw [← hu]; ring

lemma ray_period (i:Fin r){T:Packet X r}{K:Layer X X}{s:Tariff X}{b c:ℝ≥0∞}(h:localQ s T b)(hc:row K s id id c)
    (hb:b≠⊤)(hd:c≠⊤)(hh:Layer.Sym A A K)(he:A.Ready T)[Fintype Y] :
    A.deckSum (ray i T K)=ray i (A.deckSum T) (wrapL A A K):=by
 ext1 q; let v := A.place (q i); let x : Stalk A.orbit (q i):= ⟨v,A.placed ..⟩
 rw [A.deck_pivot (ray_ready A i he hh) q i v (A.placed ..),local_ray_fold (x:=x) A i h hc hb hd]; unfold ray
 let M y := A.deckSum T (update q i y)
 have hr y:A.lodge T (update q i (A.orbit y)) i y=M (A.orbit y):=(A.deck_pivot he _ i _ (by rw [Function.update_self])).symm
 simp_rw [hr]
 have hz: Summable (paint A A K v):= quota_summable (w:=fun i=>s.road v i) (fun _=>s.unit _ _) <|
    by apply ne_top_of_le_ne_top hd;rw [quota_eq _ (K v) _ (fun j=>shade ..)]; exact hc v
 let t (y:X):= paint A A K v y*M (A.orbit y)
 have hV: Summable t:= by
   have hy (p:Y): Summable (fun i:X=> if A.orbit i=p then paint A A K v i*M p else 0):= by
      apply (hz.mul_right (M p)).indicator { i | A.orbit i=p} |>.congr
      intro i; rw [Set.indicator_apply]; rfl
   have H := summable_sum (s:=Finset.univ) (f:=fun (p:Y) (i:X)=> if A.orbit i=p then paint A A K v i*M p else 0) (fun p _=> hy p)
   apply H.congr; intro y; simp [t]
 rw [← Stalk.collected_sum A.orbit hV]; apply tsum_congr; intro y
 unfold swivel
 rw [show wrapL A A K (q i) y= Stalk.collect A.orbit (paint A A K v) y from rfl]; unfold Stalk.collect
 rw [← tsum_mul_right]; apply tsum_congr; intro z; unfold t; rw [show A.orbit z.val=y from z.property]
end YM.RegulatorIR.Budget
