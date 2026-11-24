import YM.RegulatorIR.Cluster.Many

/-! The independent fields may themselves be composite; one step
on an arbitrary tree. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Cluster
open Function Set Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Uniform Gradient Step Diagram Collapsed Composite
open scoped ENNReal NNReal Topology BigOperators Classical
variable {W Z : Type}{X Y V U: W→ Type} {p i u n a b k r:ℕ} {L:Meter W}{d l:W→ℝ}{hl:∀ i,0<l i}
  {S:Z→W→ Set Room}{v: Z→W→ℝ≥0∞}{m:Z→ℕ}{T: Z→(w:W)→Orders (X w)}

variable (F:Batch X Y V U)(C:(w:W)→ Orders (X w))(G:Fund p L hl (Zone F) (u+b) (now F C) F.lineL)(H: Beam L (home hl (Zone F) u) F.forecast)

def carryOne (J:Composite Z)(m:Z→ℕ)(T:Z→(w:W)→Orders (X w))(w):= (F.grid w).each (J.accounts m) (C w) (J.product (fun i=>T i w))
def solo (J:Composite Z)(m:Z→ℕ)(T:Z→(w:W)→Orders (X w))(w):= J.product (fun i=>(F.grid w).each (m i) (C w) (T i w))
include H G
-- need beam H at u, support_run a split
lemma carries (J:Composite Z)(s:Shaped L hl (Gate F) S v d (u+b) p T m J): Folds p L (estate hl (Exit F) (fun i=> J.border i S) u) (fun i=>J.rent i v) (carryOne F C J m T):=by
 apply support_run F C (s.gather.tower (show u ≤ u+b by omega)) G H (by omega)
lemma parallelB (J:Composite Z)(s:Shaped L hl (Gate F) S v d (u+b) p T m J): Folds p L (estate hl (Exit F) (fun i=> J.border i S) u) (fun i=> J.rent i v) (solo F C J m T):=by
 induction J with
 | atom i=> exact carries F C G H _ s
 | pair A B ih ih'=>
    have ht:= Folds.lesser (T:=fun i=> (pair A B).border i S) u (fun i=> (s.left.estate_shape i).1) (fun _=> subset_union_left ..) (ih s.left)
    exact Folds.times ht (Folds.lesser u (fun i=>(s.right.estate_shape i).1) (fun _=>subset_union_right ..) (ih' s.right))

def drop (J:Composite Z)(m:Z→ℕ)(T:Z→(w:W)→Orders (X w))(w):= carryOne F C J m T w- solo F C J m T w
lemma any_joins (J:Composite Z)(s: Shaped L hl (Gate F) S v d (u+b) p T m J): Folds p L (estate hl (Exit F) (fun i=> J.border i S) u) (fun i=> J.rent i v*(amount (l i) b (d i))⁻¹) (drop F C J m T):=by
 induction J with
 | atom i=>
     intro t ht r; simp only [drop,carryOne,solo,Composite.accounts,product,sub_self,Pi.zero_apply]; exact Claim.zeroQ
 | pair A B ih ih'=>
    have hv (i:W): drop F C (pair A B) m T i=
       (carryOne F C (pair A B) m T i-accord (carryOne F C A m T i) (carryOne F C B m T i))+accord (drop F C A m T i) (carryOne F C B m T i)+accord (solo F C A m T i) (drop F C B m T i):=by
      simp_rw [drop];rw [accord_subL,accord_subR]; rw [show solo F C (pair A B) m T i=accord (solo F C A m T i) (solo F C B m T i) from rfl]; abel
    intro e he r; let P := estate hl (Exit F) (fun i=> (pair A B).border i S) u
    simp_rw [hv, Pi.add_apply]; apply Claim.add; swap
    · have hr := Folds.times (Folds.lesser (T:=fun i=>(pair A B).border i S) u (fun i=> (s.left.estate_shape i).1) (fun _=>subset_union_left ..) (parallelB F C G H A s.left)) (Folds.lesser u (fun i=> (s.right.estate_shape i).1) (fun _=>subset_union_right ..) (ih' s.right))
      convert hr e he r using 1; ext1 i; exact mul_assoc ..
    change Claim L P (fun i=> (pair A B).rent i v*(amount (l i) b (d i))⁻¹) _; apply Claim.add (B:=P) (u:=fun i=> (pair A B).rent i v*(amount (l i) b (d i))⁻¹) (separate F C s.step_width G H e he r)
    have hx:= Folds.times (Folds.lesser (T:=fun i=>(pair A B).border i S) u (fun i=> (s.left.estate_shape i).1) (fun _=>subset_union_left ..) (ih s.left)) (Folds.lesser u (fun i=> (s.right.estate_shape i).1) (fun _=>subset_union_right ..) (carries F C G H B s.right))
    convert hx e he r using 1
    ext1 i; exact mul_right_comm (A.rent i v) (B.rent i v) (amount (l i) b (d i))⁻¹
end YM.RegulatorIR.Cluster
