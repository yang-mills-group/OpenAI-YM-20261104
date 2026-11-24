import YM.RegulatorIR.Budget.Order

/-! Linear transmission on one leg (also usable when embedding input/output
labels into two parts of one space). Estimates for free translation and marks. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Budget
open Function Motion Layer Spatial Tuple Packet
open scoped BigOperators Classical Topology ENNReal NNReal
variable {X Y: Type}{r:ℕ}

namespace Tuple
-- use Function.update; universal changes of pivot
lemma move_diameter (A:Tariff X)(z:Tuple X r)(i:Fin r)(x:X): A.diameter z ≤ A.diameter (update z i x) * A.road (z i) x:=by
 have he (p q:Fin r) (hh:q≠i) : A.road (z p) (z q) ≤ A.diameter (update z i x)*A.road (z i) x:=by
    have hz:= A.diameter_ge (update z i x) p q; rw [update_of_ne hh] at hz
    by_cases hp:p=i
    · subst p; rw [update_self] at hz; exact le_trans (A.tri (z i) x (z q)) (le_trans (mul_le_mul_right hz _) (le_of_eq (mul_comm ..)))
    rw [update_of_ne hp] at hz; exact le_trans (mul_one (A.road (z p) (z q))).ge (mul_le_mul' hz (A.unit ..))
 apply A.diameter_le
 · exact one_le_mul (A.diameter_unit _) (A.unit ..)
 intro p q; by_cases hq:q=i
 · by_cases hp:p=i
   · subst p; subst q; rw [A.own]; exact one_le_mul (A.diameter_unit _) (A.unit ..)
   rw [A.symm]; exact he _ _ hp
 exact he _ _ hq
lemma move_width {A:Tariff X} (B:Premium A)(z:Tuple X r)(i:Fin r)(x:X): B.width z ≤ B.width (update z i x)*A.road (z i) x:=by
 apply B.width_le ((move_diameter ..).trans (mul_le_mul_left (B.width_diameter _) _))
 intro j; have hj:= B.width_ge (update z i x) j
 by_cases he:j=i
 · subst j; rw [update_self] at hj; exact le_trans (B.travel (z i) x) (mul_le_mul_left hj _)
 rw [Function.update_of_ne he] at hj; exact le_trans (mul_one (B.mark (z j))).ge (mul_le_mul' hj (A.unit ..))

/-- Exchange the tuple and replacement slot roles. -/
def exchange (i:Fin r) : Equiv.Perm (Tuple X r × X) where
 toFun p:=(update p.1 i p.2,p.1 i)
 invFun p:=(update p.1 i p.2,p.1 i)
 left_inv p:= by simp
 right_inv p:= by simp

def exchangeHold (x:X) {i j : Fin r}(h:i≠j):Equiv.Perm (Hold i x × X):=by
 let M (p : Hold i x × X) : Hold i x × X:=(⟨update p.1.val j p.2,by change update p.1.val j p.2 i=x; rw [Function.update_of_ne h]; exact p.1.property⟩,p.1.val j)
 have hm (p) : M (M p)=p := by
    apply Prod.ext
    · apply Subtype.ext; change update (update p.1.val j p.2) j (p.1.val j)=p.1.val; simp
    change update p.1.val j p.2 j = p.2;simp
 exact ⟨M,M,hm,hm⟩

def held_change (i:Fin r)(x y:X): Hold i x ≃ Hold i y where
 toFun a:=⟨update a.val i y, update_self ..⟩
 invFun a:= ⟨update a.val i x,update_self ..⟩
 left_inv a:=Subtype.ext (by change update (update a.val i y) i x= _; rw [update_idem]; exact (congr_arg (fun z=>update a.val i z) (Eq.symm a.property)).trans (update_eq_self ..))
 right_inv a:=Subtype.ext (by change update (update a.val i x) i y= _; rw [update_idem]; exact (congr_arg (fun z=>update a.val i z) (Eq.symm a.property)).trans (update_eq_self ..))
end Tuple
namespace Packet
section Ray

variable (i:Fin r) (T:Packet X r) {K: Layer X X} {A : Tariff X} {c d:ℝ≥0∞}

def swivel (K : Layer X X)(z : Tuple X r)(y:X) := K (z i) y*T (update z i y)
def ray (K:Layer X X): Packet X r:=fun z=>∑' y,swivel i T K z y

lemma ray_anchored (h:row K A id id c)(ht:localQ A T d)(x:X):
   (∑' z:Hold i x,quota (swivel i T K z.val) (fun _=> A.diameter z.val))≤ c*d :=by
 apply le_trans _ (mul_le_mul_left (h x) d); unfold quota
 rw [← ENNReal.tsum_mul_right, ENNReal.tsum_comm (f:=fun (z:Hold i x) y=> ‖swivel i T K z.val y‖ₑ*A.diameter z.val)]
 apply ENNReal.tsum_le_tsum; intro y; let F:=‖K x y‖ₑ*A.road x y
 have he : (∑' z:Hold i x, ‖swivel i T K z.val y‖ₑ * A.diameter z.val) ≤ (∑' z:Hold i y, F * (‖T z.val‖ₑ*A.diameter z.val)) :=by
    rw [← (held_change i x y).tsum_eq]; apply ENNReal.tsum_le_tsum; intro z
    let q:=update z.val i y
    have hh:z.val i=x:=z.property
    rw [swivel,enorm_mul, hh]; change _≤F*(‖T q‖ₑ*A.diameter q)
    apply (mul_le_mul_right (move_diameter A z.val i y) _).trans_eq
    unfold F q; rw [hh]; ring
 apply he.trans
 rw [ENNReal.tsum_mul_left]; exact mul_le_mul_right (ht ..) _

lemma ray_elsewhere (h:row (swap K) A id id c)(ht:localQ A T d)(x:X)(j:Fin r)(hz:j ≠ i) :
   (∑' z:Hold j x,quota (swivel i T K z.val) (fun _=> A.diameter z.val))≤ d*c:=by
 apply le_trans _ (mul_le_mul_left (ht j x) _)
 rw [← quota_prod (fun (z:Hold j x) y=> swivel i T K z.val y) _]; unfold quota Stalk.scopeQ
 rw [← (exchangeHold x hz).tsum_eq]
 change (∑' z:Hold j x × X, ‖swivel i T K (update z.1.val i z.2) (z.1.val i)‖ₑ * A.diameter (update z.1.val i z.2)) ≤ _
 rw [ENNReal.tsum_prod']; unfold quota; rw [← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum; intro z
 dsimp only; simp_rw [swivel,update_self,update_idem,Function.update_eq_self,enorm_mul]
 let X':= ‖T z.val‖ₑ * A.diameter z.val
 apply le_trans ?_ (mul_le_mul_right (h (z.val i)) X')
 unfold quota; rw [← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro y
 have hv:= move_diameter A (update z.val i y) i (z.val i); rw [Function.update_idem,Function.update_eq_self, update_self,A.symm] at hv
 apply (mul_le_mul_right hv _).trans_eq; unfold X'; dsimp only [id,swap]; ring
lemma ray_local (h:row K A id id c)(hh:row (swap K) A id id c)(ht:localQ A T d) : localQ A (ray i T K) (d*c):=by
 intro k x
 apply (inside_quota (fun z:Hold k x=>swivel i T K z.val) _).trans
 by_cases he:k=i
 · subst k; exact (ray_anchored i T h ht x).trans_eq (mul_comm ..)
 exact ray_elsewhere i T hh ht x k he
lemma ray_charge {B:Premium A}(hh:row (swap K) A id id c):
   quota (fun z:Tuple X r×X=>swivel i T K z.1 z.2) (fun p=>B.width p.1) ≤ markQ B T*c:=by
 rw [← quota_perm (Tuple.exchange i)]; unfold markQ quota
 change (∑' z:Tuple X r×X, ‖swivel i T K (update z.1 i z.2) (z.1 i)‖ₑ*B.width (update z.1 i z.2)) ≤ _
 rw [ENNReal.tsum_prod',← ENNReal.tsum_mul_right]; refine ENNReal.tsum_le_tsum (fun z=>?_)
 dsimp only; simp_rw [swivel,Function.update_self,Function.update_idem,Function.update_eq_self,enorm_mul]
 let X':= ‖T z‖ₑ * B.width z
 apply le_trans ?_ (mul_le_mul_right (hh (z i)) X'); unfold quota; rw [← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro y
 have hv:=move_width B (update z i y) i (z i)
 rw [Function.update_idem,Function.update_eq_self,update_self,A.symm] at hv
 apply (mul_le_mul_right hv _).trans_eq; unfold X'; dsimp only [id,swap]; ring
lemma ray_mark {B:Premium A} (h:row (swap K) A id id c):markQ B (ray i T K) ≤ markQ B T*c:=
 (inside_quota (swivel i T K) B.width).trans (quota_prod (swivel i T K) (fun z _=>B.width z)).symm.le|>.trans (ray_charge i T h)
end Ray
end Packet
end YM.RegulatorIR.Budget
