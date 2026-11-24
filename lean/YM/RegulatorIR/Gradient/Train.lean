import YM.RegulatorIR.Diagram.Heat
import YM.RegulatorIR.Uniform.Claim

/-! Composition for nonlinear invariant changes of links. Based on *homogeneous*
input rows (degree `i+1` for coefficient `i` in a rescaled connection formed
from exponential coordinates). Product test over fields keeps real orientations.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Gradient
open Budget Budget.Packet Budget.Layer Budget.Tuple Budget.Tariff Diagram Function Finset Uniform
open scoped Topology ENNReal BigOperators Classical
variable {X Y Z : Type}{r : ℕ}

def charge (g:Fin r→ℕ):=∑ i,g i
def turns (r k:ℕ): Finset (Fin r→ℕ):=(Fintype.piFinset fun _=> Finset.range (k+1)).filter fun g=> charge g=k
lemma turns_iff (g:Fin r→ℕ)(k): g ∈ turns r k↔ charge g=k := by
 rw [turns,Finset.mem_filter,Fintype.mem_piFinset]
 refine ⟨And.right,fun h=>⟨fun i=>mem_range.mpr ?_,h⟩⟩
 rw [←h]; apply Nat.lt_succ_of_le; exact Finset.single_le_sum (fun v _ => Nat.zero_le (g v)) (Finset.mem_univ i)

abbrev Curve (X Y:Type) := X→ (i:ℕ)→Packet Y (i+1)
variable (q:Curve X Y)
namespace Train
variable (g:Fin r→ℕ)

def stations := Fintype.equivFinOfCardEq (α:= (i:Fin r) × Fin (g i+1)) (show Fintype.card _= r + charge g from by rw [Fintype.card_sigma]; simp [charge,sum_add_distrib,Nat.add_comm])
abbrev Car (Y:Type) := (i:Fin r)→Tuple Y (g i+1)
def setting (Y:Type) : Tuple Y (r+charge g) ≃ Car g Y where
 toFun x i j:= x (stations g ⟨i,j⟩)
 invFun x i:= x ((stations g).symm i).fst ((stations g).symm i).snd
 left_inv x:=by ext a; simp
 right_inv x:=by ext a b; exact congr_arg (fun i:(i:Fin r) × Fin (g i+1)=>x i.1 i.2) ((stations g).symm_apply_apply ⟨a,b⟩)
lemma fromCar (y:Tuple Y (r+charge g)) i j:setting g Y y i j=y (stations g ⟨i,j⟩):= rfl

def trips (x:Tuple X r) (k: Car g Y): ℝ:=∏ i,q (x i) (g i) (k i)
def tracked (x:Tuple X r):Packet Y (r+charge g) := fun y=> trips q g x (setting g Y y)
def series (T:Packet X r): Packet Y (r+charge g) := fun z=>∑' x,T x * tracked q g x z
variable {A:Tariff Z} (B: Premium A)(p:X→Z)(m:Y→Z)

lemma across_bill (x:Tuple X r)(z:Tuple Y (r+charge g)) : (B.uses m).width z ≤ (B.uses p).width x * ∏ i:Fin r, ((Premium.rooted A (p (x i))).uses m).width (setting g Y z i):=by
 let v:=setting g Y z; let f i:= ((Premium.rooted A (p (x i))).uses m).width (v i)
 have he (i:Fin r):1 ≤ f i:= Premium.width_unit ..
 have h (i:Fin r)(j:Fin (g i+1)): A.road (p (x i)) (m (v i j))≤ f i:= Premium.width_ge ..
 let C:= (B.uses p).width x
 let H:= (A.uses p).diameter x
 have ht : 1≤ C:= Premium.width_unit ..
 let V:=∏ i,f i
 change (B.uses m).width z ≤ C*V
 apply Premium.width_le
 · apply Tariff.diameter_le _ (one_le_mul ht (Finset.one_le_prod (fun i _=>he i))); intro a b
   obtain ⟨⟨i,u⟩,rfl⟩:= (stations g).surjective a
   obtain ⟨⟨j,w⟩,rfl⟩:= (stations g).surjective b
   change A.road (m (v i u)) (m (v j w)) ≤ _
   by_cases hc:i=j
   · subst j
     apply le_trans (a:=A.road ..) (c:=C*V) ((Tariff.diameter_ge (A.uses m) (v i) u w).trans ((Premium.width_diameter ..): (A.uses m).diameter _≤ f i))
     rw [mul_comm]; exact le_trans (mul_one (f i)).ge (mul_le_mul' (Finset.single_le_prod' (fun v _=>he v) (Finset.mem_univ _)) ht)
   have hh : A.road (p (x i)) (p (x j))≤ C:= ((A.uses p).diameter_ge x i j).trans ((B.uses p).width_diameter x)
   have hv : f i * f j≤V := by unfold V; rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]; exact mul_le_mul_right (Finset.single_le_prod' (fun i _=> he i) (Finset.mem_erase.mpr ⟨Ne.symm hc,Finset.mem_univ _⟩)) _
   apply le_trans _ (mul_le_mul_right hv C)
   apply (A.tri (m (v i u)) (p (x i)) (m (v j w))).trans
   nth_rw 1 [A.symm (m _)]; exact (mul_le_mul' (h ..) ((A.tri (p (x i)) (p (x j)) (m (v j w))).trans (mul_le_mul' hh (h j w)))).trans_eq (by ac_rfl)
 intro i
 obtain ⟨⟨a,u⟩,rfl⟩:= (stations g).surjective i
 apply (B.travel (m (v a u)) (p (x a))).trans
 rw [A.symm (m _)]
 apply mul_le_mul' (show B.mark (p (x a))≤ C from Premium.width_ge ..); exact (h a u).trans (Finset.single_le_prod' (fun i _=>he i) (Finset.mem_univ _))

lemma tsum_family {S:Fin r → Type} (f:(i:Fin r)→ S i→ℝ≥0∞) :
    (∑' z : (i:Fin r)→ S i, ∏ i,f i (z i))=∏ i,(∑'v,f i v):= by
 induction r with
 | zero=>rw [tsum_fintype];simp
 | succ r ih=>
    let G := Fin.consEquiv S
    rw [← G.tsum_eq]; simp_rw [Fin.prod_univ_succ]
    rw [ENNReal.tsum_prod']
    simp_rw [G, Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ, ENNReal.tsum_mul_left,ih,ENNReal.tsum_mul_right]

lemma units (x:Tuple X r)(z:Car g Y) : ‖trips q g x z‖ₑ=∏ i,‖q (x i) (g i) (z i)‖ₑ:=by
 unfold trips; suffices h : ∀ s:Finset (Fin r), ‖∏ i∈s,q (x i) (g i) (z i)‖ₑ=∏ i∈s,‖q (x i) (g i) (z i)‖ₑ by exact h _
 intro s; induction s using Finset.induction_on with
 | empty=>simp
 | insert i s h ih=>rw [Finset.prod_insert h,Finset.prod_insert h,enorm_mul,ih]

lemma charge_reserve (c:Fin r→ℝ≥0∞)(x:Tuple X r) (h:∀ i, markQ ((Premium.rooted A (p (x i))).uses m) (q (x i) (g i)) ≤ c i):
   markQ (B.uses m) (tracked q g x) ≤ (B.uses p).width x*(∏ i,c i):=by
 let W i := (Premium.rooted A (p (x i))).uses m
 let R:= (B.uses p).width x
 unfold markQ quota; rw [← (setting g Y).symm.tsum_eq]
 apply le_trans _ (mul_le_mul_right (Finset.prod_le_prod' (s:=univ) (f:=fun i=>markQ (W i) (q (x i) (g i))) (fun i _ => h i)) R)
 change _ ≤ R * ∏ i,(∑' v : Tuple Y _,‖q (x i) (g i) v‖ₑ*(W i).width v)
 rw [← tsum_family,← ENNReal.tsum_mul_left]; apply ENNReal.tsum_le_tsum; intro z
 unfold tracked; rw [Equiv.apply_symm_apply, units]; apply (mul_le_mul_right (across_bill g B p m x ((setting g Y).symm z)) _).trans_eq
 simp_rw [Equiv.apply_symm_apply,Finset.prod_mul_distrib]; dsimp only [R,W]; ac_rfl
lemma batch_charge (T:Packet X r)(c:Fin r→ℝ≥0∞) (h:∀ i x, markQ ((Premium.rooted A (p x)).uses m) (q x (g i))≤ c i):
  quota (fun z:Tuple X r × Tuple Y (r+charge g)=>T z.1 * tracked q g z.1 z.2) (fun z=>(B.uses m).width z.2)≤ markQ (B.uses p) T * ∏ i,c i:=by
 rw [quota_prod (fun (x:Tuple X r) y=>T x*tracked q g x y) (fun _ y=> (B.uses m).width y)]
 unfold markQ quota; rw [← ENNReal.tsum_mul_right]; apply ENNReal.tsum_le_tsum
 intro x; simp_rw [enorm_mul,mul_assoc,ENNReal.tsum_mul_left]
 exact mul_le_mul_right (charge_reserve q g B p m c x (fun i=>h i _)) _
lemma char_budget (T:Packet X r)(c:Fin r→ℝ≥0∞)(h:∀ i x,markQ ((Premium.rooted A (p x)).uses m) (q x (g i))≤ c i): markQ (B.uses m) (series q g T) ≤ markQ (B.uses p) T * ∏ i,c i:=by
 apply (inside_quota (fun z x=>T x*tracked q g x z) _).trans
 apply le_trans _ (batch_charge q g B p m T c h)
 unfold quota; rw [ENNReal.tsum_prod']; exact ENNReal.tsum_comm.le
end Train

end YM.RegulatorIR.Gradient
