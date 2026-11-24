import YM.FormalOPE.RG10.Capture.Shrink

/-! # Compile root-cell norms from whole product cluster estimates

No assumption of stationary scalar on each cell or changing normalization convention. Root
averaging with the given full measure **in physical units**. Read genuine test address exactly,
using all positions & merging all incoming kernels. Port cost through horizon order for the result
is paid with one estimate over this very `cell` (here modeled as measure per cell of the selected
lattice partition) before adding any other incident budgets. Choose a measure respecting symmetries
as needed on the finite period instance; not claiming full regulator/horizon compatibility from this
type of measure alone. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Capture
open PowerSeries Function Finset MeasureTheory Filter Route Transit
open scoped Topology BigOperators Classical
variable {X : Type} [MeasurableSpace X] {T U : ℕ→ Type} {α β J : Type*}
    [∀ i,Fintype (T i)]
variable (W : Scale X U) (S : Locale T X α β) (i : ℕ)
structure Cover (W : Scale X U) (S : Locale T X α β) (i : ℕ) where
  cell (z : T i) : Measure X
  finite z : IsFiniteMeasure (cell z)
  centered z : ∀ᵐ x∂(cell z), x∈S.park i z
  account z : (cell z).real Set.univ=(W.μ i)^4

variable {W S i}
namespace Cover
variable (C : Cover W S i) (z : T i) (F : Measure X)
attribute [local instance] Cover.finite
def volume : Measure X := ∑ z : T i,C.cell z
local notation "μz" => C.cell z
variable (v : Finset J) (f : J→ Channel (U i)) (g : J→ X→ℂ)

def versions (φ : α) (j : J) (x : X) := S.test φ x*g j x
omit [MeasurableSpace X] [∀ i,Fintype (T i)] in
lemma specialized (φ : α) (x : X) : collection v f (versions (S:=S) g φ) x=S.test φ x • collection v f g x := by
  unfold collection versions; rw [Finset.smul_sum]; simp_rw [mul_smul]
-- use proof μ = entire when comparing; not free implicit millimeters

def material : Skin T U α i := fun z φ => nominal (((W.μ i)^4)⁻¹) • smeared (C.cell z) v f (versions (S:=S) g φ) -- precedence fix

def Legible := ∀ z : T i,∀ j∈v, Integrable (g j) (C.cell z) ∧ ∀ (φ: α), Integrable (versions (S:=S) g φ j) (C.cell z)
variable (h : Legible C v g)
include h
lemma earns (φ : α) (j) (hj:j∈v) : Integrable (versions (S:=S) g φ j) C.volume := integrable_finsetSum_measure.mpr fun z _=> (h z j hj).2 φ

lemma stamp_eq (p : ℕ) (φ : α) : fingerprint φ W p i i (material C v f g)=smeared C.volume v f (versions (S:=S) g φ) := by
  unfold fingerprint material;
  dsimp only [LinearMap.coe_mk,AddHom.coe_mk]; rw [← Finset.smul_sum,smul_smul, price, div_self (W.positive _).ne',one_pow,one_mul,
    ← product_nom,mul_inv_cancel₀ (pow_ne_zero _ (W.positive _).ne'), nominal_un, one_smul];
  unfold smeared; rw [sum_comm]; refine Finset.sum_congr rfl fun j hj=>?_;
  rw [volume, MeasureTheory.integral_finsetSum_measure (fun z _=>(h z j hj).2 φ), Finset.sum_smul] -- inspect

omit h
variable (n k : ℕ)
local notation "ι" => (W.μ i)^4
local notation "L" => box v f k
local notation "π" => W.eyes i (W.tape.sphere (S.point i z) 0)
def qFee (a : Letters (U i)) (x : X) : ℂ := (↑((W.μ i)^4)⁻¹:ℂ)* aboard (collection v f g x) k a -- fix coercion
include h
omit [∀ i,Fintype (T i)] in
private lemma portCost (φ) (l) :
    (∫ x, S.test φ x*qFee (W:=W) v f g k l x ∂μz) = aboard (material C v f g z φ) k l := by
  have hm x: S.test φ x*qFee (W:=W) v f g k l x= (↑(ι⁻¹) :ℂ)*aboard (collection v f (versions (S:=S) g φ) x) k l := by
    rw [specialized,qFee]; unfold aboard; rw [coeff_smul,MvPolynomial.coeff_smul, smul_eq_mul]; push_cast; ring
  simp_rw [hm]; rw [integral_const_mul, aboard_average .., material,nominal,tower];
  · unfold aboard; rw [coeff_smul,MvPolynomial.coeff_smul,smul_eq_mul]
  exact fun j hj => (h z j hj).2 φ

def develop : Strip S U i where
  number := Fintype.card ↥(box v f k)
  base _ := μz
  print _ := S.blank
  field j := ((Fintype.equivFin ↥(box v f k)).symm j).val
  currency j := qFee (W:=W) v f g k ((Fintype.equivFin ↥(box v f k)).symm j).val
local notation "ϙ" => develop C z v f g k
omit [∀ i,Fintype (T i)] in
private lemma priceable (a) : Integrable (qFee (W:=W) v f g k a) μz := (aboard_pays μz v f g (fun j hj=> (h z j hj).1) _ _).const_mul _
omit [∀ i,Fintype (T i)] in
lemma fitting : Strip.Meets S i z ϙ := by
  refine ⟨fun _=>priceable C z v f g h k _,fun _=>C.centered z, fun j φ=>?_⟩;
  let a:= (ϙ).field j
  change Integrable (fun x => S.differential i S.blank φ x * ((↑((W.μ i)^4)⁻¹:ℂ)* aboard (collection v f g x) k a)) μz
  have he x : S.differential i S.blank φ x * aboard (collection v f g x) k a = aboard (collection v f (versions (S:=S) g φ) x) k a := by rw [specialized]; unfold aboard; rw [coeff_smul,MvPolynomial.coeff_smul,smul_eq_mul, S.first]; rfl
  simp_rw [mul_left_comm _ (↑((W.μ i)^4)⁻¹:ℂ),he]; exact (aboard_pays μz v f _ (fun j hj => (h z j hj).2 φ) k a).const_mul _
omit [∀ i,Fintype (T i)] in
lemma declared (φ) : PowerSeries.coeff k (material C v f g z φ)=(ϙ).strings S i φ := by
  unfold Strip.strings
  let P:= PowerSeries.coeff k (material C v f g z φ)
  let A (j : ↥(box v f k)):= MvPolynomial.monomial j.val (MvPolynomial.coeff j.val P : ℂ)
  suffices P= ∑ j : ↥(box v f k),A j by
    rw [← Equiv.sum_comp (Fintype.equivFin ↥(box v f k)).symm A] at this
    apply this.trans; apply Finset.sum_congr rfl; intro j hj; unfold A; congr 1
    exact (show Strip.readAt S i ϙ φ j=aboard (material C v f g z φ) k ((ϙ).field j) from by unfold Strip.readAt; rw [show (ϙ).print j=S.blank from rfl,S.first]; exact portCost C z v f g h k φ _).symm -- inspect
  unfold A; rw [Finset.sum_coe_sort L (fun a=> MvPolynomial.monomial a (MvPolynomial.coeff a P))];
  nth_rw 1 [P.as_sum]; apply Finset.sum_subset;
  · intro j hj; apply not_not.mp; intro ht; apply MvPolynomial.mem_support_iff.mp hj
    unfold P; rw [material,nominal,tower,coeff_smul,MvPolynomial.coeff_smul,MvPolynomial.notMem_support_iff.mp ?_, smul_zero]; exact fun hx=>ht (plays v f k _ hx)
  intro a _ hb; simp [MvPolynomial.notMem_support_iff.mp hb]

omit [∀ i,Fintype (T i)] in
lemma sent {C' : ℝ} (hp : ∀ᵐ x∂ μz, worth π n (PowerSeries.coeff k (collection v f g x)) ≤ C') :
    Strip.worthAt W S i z ϙ n ≤ C' := by
  let A (a : Letters (U i)):= ∫ x, ‖qFee (W:=W) v f g k a x‖ ∂ μz
  let μ:=C.cell z
  have ht : 0 < W.μ i:= W.positive _
  have hm (x : X) (a : Letters (U i)) : ‖qFee (W:=W) v f g k a x‖=ι⁻¹* ‖aboard (collection v f g x) k a‖ := by unfold qFee; simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
  suffices (∑ a∈L,fare π n a * A a) ≤ C' by
    rw [← Finset.sum_coe_sort,← Equiv.sum_comp (Fintype.equivFin ↥(box v f k)).symm (fun (a:↥L) => fare π n a.val * A a.val)] at this -- inspect
    exact this
  unfold A; simp_rw [← MeasureTheory.integral_const_mul];
  rw [← integral_finsetSum ..];
  · have he x : (∑ a∈L,fare π n a * ‖qFee (W:=W) v f g k a x‖) = ι⁻¹* worth π n (coeff k (collection v f g x)) := by
      rw [box_value v f k π n (collection v f g x) (plays v f k (fun j=>g j x)), Finset.mul_sum]; exact sum_congr rfl fun a _ => by rw [hm x a,mul_left_comm]
    simp_rw [he]; rw [integral_const_mul];
    apply (mul_le_mul_of_nonneg_left (integral_mono_ae (box_income μz v f g (fun j hj=> (h z j hj).1) _ π n) (integrable_const C') hp) (by positivity)).trans
    rw [integral_const,C.account, smul_eq_mul, inv_mul_cancel_left₀ (by positivity)] -- inspect
  exact fun a _=> (priceable C z v f g h k a).norm.const_mul _
omit [∀ i,Fintype (T i)] in
lemma fits {r} {K : ℝ} (he : ∀ z:T i, ∀ᵐ x∂(C.cell z), W.value i n r (W.tape.sphere (S.point i z) 0) (collection v f g x) ≤ K) : Fits W S i (material C v f g) n r K := by
  intro j hj z; refine ⟨develop C z v f g j, declared C z v f g h j, fitting C z v f g h j,sent C z v f g h n j ?_⟩;
  filter_upwards [he z] with x hx; exact (current _ _ _ (W.alive _ _) _ j hj).trans hx
end Cover
end YM.FormalOPE.RG10.Capture
