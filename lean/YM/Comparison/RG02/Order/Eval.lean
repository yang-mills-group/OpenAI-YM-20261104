import YM.Comparison.RG02.Order.Vacancy

/-!
# Evaluate polarized grade, track polynomial truncation exactly

Work only with explicit fixed `r` and the *same* normalization/coupling. Taylor in `g`, with
error terms post-multiplication kept before taking estimates. This portion does not assert
smallness or convergence of any reparametrized density. Unit issues near a large volume remain
real even if algebraic vacuum identities hold.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Order
open Finset Function YM.Marker YM.Multi Join YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories (connected connected_quiet pass_connected part_sub)
open YM.Comparison.RG02.Cumulants
open scoped BigOperators Classical
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}

/-- Evaluating at a scalar point spends truncation, not an algebra map. -/
def value (g : ℂ) (x : Grade R r) := ∑ i∈range (r+1), g^i • observe R r x i
lemma vpart (g : ℂ) (x : Grade R r) (s : R.Mode) : (value g x).part s=
    ∑ i∈range (r+1),g^i * (observe R r x i).part s := by unfold value; simp [Poly.part_sum]

def valueL (R : Census V) (r : ℕ) (g : ℂ) : Grade R r →ₗ[ℂ] Poly R where
   toFun := value g
   map_add' x y := by simp only [value,observe_add,smul_add,sum_add_distrib]
   map_smul' a x := by simp only [value,observe_smul, Finset.smul_sum,RingHom.id_apply]; exact sum_congr rfl fun i _=>smul_comm ..

/-- Evaluate a polynomial over the marker algebra. This part *is* an algebraic
    operation; the rendering/truncation lost high orders. -/
def formula (g : ℂ) : Truncated R →+* Poly R := Polynomial.eval₂RingHom (RingHom.id _) (Poly.bead R g)
omit [Fintype V] in
lemma formula_mul (g : ℂ) (p q : Truncated R) : formula g (p*q)=formula g p*formula g q := map_mul _ _ _
omit [Fintype V] in
lemma formula_monomial (g : ℂ) (i : ℕ) (a : Poly R) :
    formula g (Polynomial.monomial i a) = g^i • a := by
  change Polynomial.eval _ _=_; rw [Polynomial.eval_monomial,← map_pow, mul_comm, Poly.product_bead]
omit [Fintype V] in
lemma formula_const (g : ℂ) (a : Poly R) : formula g (Polynomial.C a)=a := by
  change Polynomial.eval _ _= _; rw [Polynomial.eval_C]
omit [Fintype V] in
lemma formula_smul (g t : ℂ) (p : Truncated R) : formula g (t•p)=t•formula g p := by
  have he : t•p = Polynomial.C (Poly.bead R t)*p := by
    ext i; rw [Polynomial.coeff_smul, Polynomial.coeff_C_mul, Poly.product_bead]
  rw [he, map_mul,formula_const,Poly.product_bead]
lemma short_value (p : PTable R) (g : ℂ) : formula g (PowerSeries.trunc (r+1) p)=value g (series R r p) := by
  change Polynomial.eval₂ (RingHom.id _) _ _=_
  rw [PowerSeries.eval₂_trunc_eq_sum_range]; refine sum_congr rfl fun i hi=>?_
  rw [observation _ _ _ (Nat.le_of_lt_succ (mem_range.mp hi)), ← Poly.product_bead, map_pow]
  exact mul_comm ..
lemma value_render (g : ℂ) (p : Grade R r) : value g p=formula g (render p) := by
  unfold value render; rw [short_value]; apply Finset.sum_congr rfl; intro i hi;
  rw [observation _ _ _ (by simpa using hi), collect_coeff]

lemma value_denom (x : Grade R r) (g : ℂ) :
    value g (denominator x)=Poly.bead R ((value g x).part R.quiet) := by
  ext u; rw [show Poly.bead R ((value g x).part R.quiet)=Poly.send R.quiet ((value g x).part R.quiet) from rfl];
  simp_rw [vpart,denominator, observe_bottom, pure_marks, Poly.part_send];
  by_cases h:u=R.quiet <;> simp [h]

lemma stamp_value (p : Truncated R) (g : ℂ) : value g (stamp R r p)=
    ∑ i∈p.support with i≤r, g^i • p.coeff i := by
  rw [← series_poly, value];
  have hx : ∑ i∈range (r+1), g^i • observe R r (series R r p) i = ∑ i∈range (r+1),g^i • p.coeff i := by
    apply sum_congr rfl; intro i hi; rw [observation _ _ _ (by simpa using hi), Polynomial.coeff_coe]
  rw [hx]; symm; apply sum_subset
  · intro i hi; exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hi).2)
  intro i hi hm; have he := show ¬ i∈p.support from fun hp=>hm (mem_filter.mpr ⟨hp,by simpa using hi⟩)
  rw [Polynomial.notMem_support_iff.mp he, smul_zero]

/-- Numerical price will eventually involve the relation to running `g_m`. Keep signed terms
    here. No implicit power recovered after multiplying large polynomials. -/
def omitted (r : ℕ) (g : ℂ) (p : Truncated R) :=
    ∑ i∈p.support with ¬ i≤r, g^i • p.coeff i

omit [Fintype V] in
lemma formula_sum (p : Truncated R) (g : ℂ) : formula g p=∑ i∈p.support, g^i • p.coeff i := by
  change Polynomial.eval _ _ = _; rw [Polynomial.eval_eq_sum]; change ∑ i∈p.support,p.coeff i*_ = _
  apply sum_congr rfl; intro i hi; rw [← Poly.product_bead, map_pow]; exact mul_comm ..
lemma formula_omits (r : ℕ) (p : Truncated R) (g : ℂ) : formula g p=value g (stamp R r p)+ omitted r g p := by
  rw [formula_sum,stamp_value]; exact (sum_filter_add_sum_filter_not ..).symm

def subtotal (w : V → ℝ) (r : ℕ) (z : ℝ) (p : Truncated R) :=
    ∑ i∈p.support with ¬ i≤r, z^(i-(r+1))*Poly.price w (p.coeff i)
omit [Fintype V] in
lemma tail_bound (w : V→ℝ) (hw : ∀ i,0<w i) (r : ℕ) (z : ℝ) (p : Truncated R) (g : ℂ) (hg : ‖g‖≤z) :
    Poly.price w (omitted r g p) ≤ ‖g‖^(r+1)*subtotal w r z p := by
  apply le_trans (Poly.batch hw _ _) ?_
  simp_rw [subtotal, Finset.mul_sum]; apply sum_le_sum; intro i hi
  have hx := (mem_filter.mp hi).2
  rw [Poly.adapted,norm_pow,← mul_assoc, show ‖g‖^i=‖g‖^(r+1)*‖g‖^(i-(r+1)) by rw [← pow_add,show r+1+(i-(r+1))=i by omega]]
  gcongr; exact Poly.nonnegative hw _

lemma value_multiply (p q : Grade R r) (x : Symmetric p) (y : Symmetric q) (g : ℂ) :
    value g p*value g q = value g (p*q)+omitted r g (render p * render q) := by
  rw [value_render g p,value_render g q, ← map_mul,formula_omits r _ g,map_mul,rerender x,rerender y]

end YM.Comparison.RG02.Order
