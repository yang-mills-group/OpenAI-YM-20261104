import YM.RegulatorIR.Budget.RayPeriod

/-!
Reassembling a marked (tested) vertex. This argument keeps both internal
positions. No symmetrization or orbit-cancellation factor is applied to the
mark before projecting.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Budget
open Function Tuple Layer Spatial Motion Packet Deck
open scoped NNReal ENNReal Topology BigOperators Classical
variable {X Y : Type} {r : ℕ} {P:ℝ}
namespace Deck
variable (A:Deck P X Y)
theorem lodge_bound {T:Packet X r}(H:Tariff X)(q:Tuple Y r)(i:Fin r)(b:X):
    ‖A.lodge T q i b‖ₑ ≤ Stalk.scopeQ (fun x:Tuple X r=>x i) T H.diameter b:=by
 apply enorm_tsum_le_tsum_enorm.trans
 let e: Nest A q i b → Hold i b:= fun v=> ⟨v.val,v.property.2⟩
 have h:Injective e:=fun _ _ h=>Subtype.ext (Subtype.mk.inj h)
 apply le_trans _ (quota_restrict e h (fun z=>T z.val) (fun z=>H.diameter z.val))
 apply ENNReal.tsum_le_tsum; intro i; unfold Function.comp
 rw [A.dyed_cost]
 exact le_trans (mul_one ‖T i.val‖ₑ).ge (mul_le_mul_right (H.diameter_unit i.val) _)

def sorted (q:Tuple Y r)(i:Fin r) : Stalk A.project q → Stalk A.orbit (q i) :=fun v=>⟨v.val i,congr_fun v.property i⟩
def nesting (q:Tuple Y r)(i:Fin r)(b:Stalk A.orbit (q i)):Nest A q i b.val≃Stalk (A.sorted q i) b where
 toFun z:=⟨⟨z.val,z.property.1⟩,Subtype.ext z.property.2⟩
 invFun z:=⟨z.val.val,z.val.property,congr_arg Subtype.val z.property⟩
 left_inv _:= rfl
 right_inv _:=rfl
lemma sortedSum {T:Packet X r}(h:quota T 1≠⊤)(q:Tuple Y r)(i:Fin r):
    A.scroll T q=∑' b:Stalk A.orbit (q i), A.lodge T q i b.val :=by
 let d: Stalk A.project q→ℝ:=fun z=>A.dyed T z.val
 have hd:Summable (A.dyed T):= quota_summable (w:=1) (fun _=>le_rfl) (by rw [quota_eq _ T 1 (fun _=> A.dyed_cost ..)]; exact h)
 change (∑' z, d z)=_; rw [← Stalk.collected_sum (A.sorted q i) (show Summable d from hd.comp_injective Subtype.val_injective)]
 apply tsum_congr; intro b; exact ((A.nesting q i b).tsum_eq (fun v=>d v.val)).symm
end Deck

lemma ray_scroll (A:Deck P X Y)(i:Fin r){T:Packet X r}{K:Layer X X}{b c:ℝ≥0∞}{s:Tariff X}{d:Premium s}
   (hh:Layer.Sym A A K) (h:markQ d T≤b) (hr:row K s id id c)(hc:row (swap K) s id id c)(hb:b≠⊤)(he:c≠⊤) :
    A.scroll (ray i T K)=ray i (A.scroll T) (wrapL A A K):= by
 have hx : quota T 1 ≠ ⊤:= ne_top_of_le_ne_top hb (le_trans (quota_mono T fun _=> d.width_unit _) h)
 have hv: quota (ray i T K) 1≠⊤:= ne_top_of_le_ne_top (ENNReal.mul_ne_top hb he) (le_trans (quota_mono _ fun _=>d.width_unit _) ((ray_mark i T hc).trans (mul_le_mul_left h _)))
 have hB := local_mono s (local_paid d T) h
 ext1 q; rw [A.sortedSum hv q i]
 let C y := A.lodge T (update q i (A.orbit y)) i y
 let P x y : ℝ := paint A A K x y*C y
 have hH (v:Stalk A.orbit (q i)): A.lodge (ray i T K) q i v.val= ∑' y,P v.val y:= local_ray_fold A i hB hr hb he q v
 have hs: Summable fun p:Stalk A.orbit (q i) × X=>P p.1.val p.2:=by
    apply quota_summable (w:=1) (fun _=> le_rfl)
    apply ne_top_of_le_ne_top (b:=c*b) (by finiteness)
    rw [quota_base,ENNReal.tsum_prod', ENNReal.tsum_comm]; dsimp only
    apply le_trans _ (mul_le_mul_right h _); unfold markQ; rw [← Stalk.total (fun x:Tuple X r=>x i),← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum; intro y; unfold P
    simp_rw [enorm_mul,shade A A K, ENNReal.tsum_mul_right]
    apply mul_le_mul'
    · apply le_trans _ (quota_restrict (Subtype.val : Stalk A.orbit (q i)→X) Subtype.val_injective ((swap K) y) (fun x=>s.road y x) |>.trans (hc y)); apply ENNReal.tsum_le_tsum; intro a
      exact le_trans (mul_one ‖K a.val y‖ₑ).ge (mul_le_mul_right (s.unit y a.val) _)
    exact (A.lodge_bound s _ _ _).trans (quota_mono _ fun v=>d.width_diameter v.val)
 let f : Stalk A.orbit (q i) → X →ℝ:= fun x y=>P x.val y
 have hp : Summable (Function.uncurry f):=hs
 simp_rw [hH]; rw [show (∑' v:Stalk A.orbit (q i),∑' y,P v.val y)=(∑' y,∑' v:Stalk A.orbit (q i), f v y) from hp.tsum_comm.symm, ← Stalk.collected_sum A.orbit ?_]; rotate_left
 · exact hs.prod_symm.prod
 unfold ray; apply tsum_congr; intro y
 let M:=update q i y; let B:=Stalk A.orbit y; let S:= Stalk A.orbit (M i)
 let g : B≃ S:= Equiv.subtypeEquiv (Equiv.refl _) fun z=>by simp [M]
 unfold Stalk.collect; rw [swivel,A.sortedSum hx M i,← g.tsum_eq, ← tsum_mul_left]
 apply tsum_congr; intro a
 have h : C a.val=A.lodge T M i (g a).val :=by change A.lodge T _ _ _=A.lodge _ _ _ a.val; rw [show A.orbit a.val=y from a.property]
 let K':= wrapL A A K
 change (∑' z:Stalk A.orbit (q i),paint A A K z.val a.val*C a.val)= K' (q i) y*_
 rw [tsum_mul_right,h]
 apply congr_arg (fun w:ℝ=> w*_)
 have hv' : Layer.Sym A A (swap K):= fun d x y=> hh d y x
 unfold K'; rw [other A A K hh]
 have hg : wrapL A A (swap K) y (q i)= forwardCost A A (swap K) a.val (q i):= (leib A hv' a (q i)).symm
 rw [hg]; unfold forwardCost Stalk.collect; apply tsum_congr; intro z; unfold paint swap; rw [mul_comm (A.orient z.val)]
where
 leib (A:Deck P X Y){F:Layer X X}(hf:Sym A A F){x:Y}(a:Stalk A.orbit x)(p:Y): forwardCost A A F a.val p=wrapL A A F x p:= (Layer.from_proj A A F hf _ p).trans (by rw [show A.orbit a.val=x from a.property])
end YM.RegulatorIR.Budget
