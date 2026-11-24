import YM.QCDContinuum.Sources.Cargo
/-! # Operations and prices on Cargo at arbitrary positive or nonnegative radii.
No count-dependent loss for product and infinite sum estimates. Topology-only
homogeneous estimates using Π-sup norm just for fixed-marker-set summability.
Adapted from YM.Marker.Weight and additions for vector elements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Marker.Cargo
open Function Finset
open scoped Topology BigOperators Classical
variable {V A k:Type*}[DecidableEq V]{R:Census V}
local notation "C"=> Cargo R A
section normedAdd
variable [NormedAddCommGroup A]
instance : NormedAddCommGroup (Cargo R A):= inferInstanceAs (NormedAddCommGroup (R.Mode→A))
instance [NormedField k][NormedSpace k A]: NormedSpace k (Cargo R A):= inferInstanceAs (NormedSpace k (R.Mode→A))
instance [CompleteSpace A]:CompleteSpace (Cargo R A):=inferInstanceAs (CompleteSpace (R.Mode→A))
def get [NormedField k][NormedSpace k A] (x : R.Mode) : Cargo R A →L[k] A where
  toFun a := a.part x
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl
  cont := continuous_apply x
@[fun_prop] lemma part_cont (x:R.Mode) : Continuous fun a : Cargo R A=> a.part x:= continuous_apply x
lemma together {B:Type*}[TopologicalSpace B](f:B→ Cargo R A)(h:∀ i,Continuous (fun b => (f b).part i)): Continuous f:= continuous_pi h
def toll (w:V→ℝ)(x : R.Mode):= ∏ i∈(x.1), w i
def price (w:V→ℝ)(a:Cargo R A):= ∑ i,toll w i * ‖a.part i‖
variable {w:V→ℝ} (hw:∀ i,0 ≤ w i)
lemma multiplier (a b c : R.Mode) (h : Poly.merges a b c) : toll w c=toll w a*toll w b := by unfold toll; rw [← h.2,Finset.prod_union h.1]
omit hw
@[fun_prop] lemma price_cont (w : V → ℝ) : Continuous fun a : Cargo R A => price w a := by unfold price; fun_prop
@[simp] lemma solo (x : R.Mode) (v : A) : price w (send x v)=toll w x*‖v‖ := by
  unfold price; rw [sum_eq_single x]
  · simp
  · intro i _ h; simp [h]
  simp
@[simp] lemma quiet_toll : toll w R.quiet=1 := by simp [toll,Census.quiet]
@[simp] lemma solo_toll (x : V) : toll w (R.fire x)=w x := by simp [toll,Census.fire]
@[simp] lemma zero_price : price w (0 : Cargo R A)=0 := by unfold price; simp
@[simp] lemma adapted [NormedField k][NormedSpace k A] (x : Cargo R A) (c : k) : price w (c • x)=‖c‖* price w x := by simp [price,Finset.mul_sum,norm_smul,mul_left_comm]
include hw
lemma worth (x : R.Mode) : 0 ≤ toll w x := prod_nonneg fun i _ => hw i
lemma nonnegative (x : Cargo R A) : 0≤price w x := sum_nonneg fun i _ => mul_nonneg (worth hw i) (norm_nonneg _)
lemma member (x : R.Mode) (a : Cargo R A) : toll w x*‖a.part x‖≤price w a :=
    Finset.single_le_sum (fun i _ ↦ mul_nonneg (worth hw i) (norm_nonneg (a.part i))) (mem_univ _)
lemma addition (a b : Cargo R A) : price w (a+b) ≤ price w a+price w b := by
  unfold price; rw [← Finset.sum_add_distrib]; refine sum_le_sum fun i _ => ?_; rw [←mul_add,part_plus]; exact
    mul_le_mul_of_nonneg_left (norm_add_le _ _) (worth hw i)
lemma batch {X : Type*} (T : Finset X) (a : X → Cargo R A) : price w (∑ i∈ T,a i) ≤ ∑ i ∈ T, price w (a i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i t hi h => rw [sum_insert hi,sum_insert hi]; exact (addition hw ..).trans (by gcongr)
-- price at w=1 dominates sup, don't incur loss for absolute convergence
omit hw in
lemma majorant (a : Cargo R A): ‖a‖ ≤ price (fun _=>1) a :=by
   change ‖a.part‖ ≤ _; apply (pi_norm_le_iff_of_nonneg (nonnegative (fun _=> zero_le_one) a)).mpr; intro i; simpa only [toll,prod_const_one,one_mul] using member (fun _=>zero_le_one) i a
omit hw
lemma share {I:Type*}{t:I→Cargo R A} [NormedField k][NormedSpace k A] (h:Summable t) (x:R.Mode):(∑' i,t i).part x=∑' i,(t i).part x:= (get x (k:=k)).map_tsum h -- `k` not in conclusion
lemma sum_le {I:Type*}{t:I→Cargo R A}(h:Summable t) {v:I→ℝ}(hg:Summable v){w:V→ℝ}(hr:∀ i,0≤w i)(hv:∀ i,price w (t i) ≤ v i):price w (∑' i,t i) ≤ ∑' i,v i:= le_of_tendsto_of_tendsto' ((price_cont w).continuousAt.tendsto.comp h.hasSum) hg.hasSum (fun s:Finset I=>(batch hr s t).trans (sum_le_sum fun i _=>hv i))
end normedAdd
section commRing
variable [CommRing A]
@[simp] lemma one_part (x : R.Mode) : (1 : Cargo R A).part x=if x=R.quiet then 1 else 0 := part_send ..
lemma part_mul (a b : Cargo R A) (i) : (a*b).part i=∑ x,∑ y,if Poly.merges x y i then a.part x*b.part y else 0 := product a b i
def bead (R:Census V): A →+* Cargo R A where
  toFun := send R.quiet
  map_one' :=rfl
  map_add' a b :=by ext i; simp; split <;> simp
  map_zero' := send_zero _
  map_mul' a b:= by ext i; rw [part_send]; change _ = (Cargo.prod _ _).part i; rw [cart]; simp [eq_comm]
lemma product_bead {k:Type*}[CommRing k][Algebra k A] (a:Cargo R A)(c:k): bead R ((algebraMap k A) c) * a=c • a:=by
  ext i; rw [part_mul, sum_eq_single R.quiet]
  · simp [bead, Algebra.smul_def]
  · intro j _ hj; simp [bead,hj]
  simp
instance instAlg {k:Type*}[CommRing k][Algebra k A]:Algebra k (Cargo R A) where
  algebraMap := (bead R).comp (algebraMap k A)
  commutes' _ _:=mul_comm ..
  smul_def' a b:=(product_bead b a).symm
end commRing
section normed
variable [NormedCommRing A]
instance : ContinuousMul (Cargo R A) := by
  constructor; change Continuous (fun a : Cargo R A × Cargo R A => (a.1*a.2).part)
  apply continuous_pi; intro i; simp only [part_mul]; refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun y _ => ?_
  split <;> fun_prop
lemma cart_spec (x y z:R.Mode)(a b:A):(send x a * send y b).part z=if Poly.merges x y z then a*b else 0:=cart x y z a b
lemma yes (x y z:R.Mode)(a b:A)(h:Poly.merges x y z): send x a * send y b=send z (a*b):=by
    ext i; rw [cart_spec,part_send]
    split_ifs with he hh hh
    · rfl
    · exact False.elim (hh (Subtype.ext (he.2.symm.trans h.2)))
    · exact False.elim (he (hh.symm ▸ h))
    rfl
lemma no (x y:R.Mode)(a b:A)(h:∀ z,¬Poly.merges x y z):send x a * send y b=0:=by ext i; rw [cart_spec,if_neg (h _),part_nil]
lemma single_mul {w:V→ℝ}(hw:∀ i,0≤w i) (x y:R.Mode)(a b:A):price w (send x a * send y b)≤ toll w x*‖a‖*(toll w y*‖b‖):=by
  by_cases h : ∃ z, Poly.merges x y z
  · obtain ⟨z,h⟩ := h; rw [yes x y z a b h, solo,multiplier _ _ _ h]
    calc _ ≤ _*_* (‖a‖*‖b‖):= mul_le_mul_of_nonneg_left (norm_mul_le _ _) (mul_nonneg (worth hw _) (worth hw _))
         _ = _:=by ring
  rw [no x y a b (not_exists.mp h), zero_price]
  exact mul_nonneg (mul_nonneg (worth hw _) (norm_nonneg _)) (mul_nonneg (worth hw _) (norm_nonneg _))
variable {w:V→ℝ}(hw:∀ i,0≤w i)
include hw
lemma multiplication (a b : Cargo R A) : price w (a*b) ≤ price w a*price w b := by
  conv_lhs => rw [← studs a,← studs b,sum_mul]
  apply le_trans (batch hw ..); unfold price; rw [sum_mul]
  refine sum_le_sum fun i _ => ?_
  rw [mul_sum,mul_sum]; exact (batch hw ..).trans (sum_le_sum fun j _ ↦ single_mul hw ..)
variable [NormOneClass A]
omit hw in
@[simp] lemma one_price : price w (1 : Cargo R A)=1 := by change price w (send R.quiet 1)=1; simp
lemma multiple {X : Type*} (T : Finset X) (a : X → Cargo R A) : price w (∏ i∈ T,a i) ≤ ∏ i∈T, price w (a i) := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i t hi h => rw [prod_insert hi,prod_insert hi]; exact (multiplication hw ..).trans (mul_le_mul_of_nonneg_left h (nonnegative hw _))
lemma powers (a : Cargo R A) (k : ℕ) : price w (a^k) ≤ price w a^k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ,pow_succ]; exact (multiplication hw ..).trans (mul_le_mul_of_nonneg_right ih (nonnegative hw _))
end normed
end YM.Marker.Cargo
