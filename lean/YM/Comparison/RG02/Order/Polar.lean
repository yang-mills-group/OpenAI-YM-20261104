import YM.Comparison.RG02.Order.Join
import Mathlib.RingTheory.PowerSeries.Trunc

/-!
# Polarized bookkeeping coupler

Some vertices start with negative explicit powers and will become legitimate only after
factoring their valuation. Once assigning these grades in `gᵢ` (not beta offset, not loop order),
perform all-order (i.e. each prescribed finite order r) comparison using these operations.
The *allowed* marker family stays fixed and the marker exponentiations (quiet/vacuum and multiple
source perturbed inverses) keep the censored multiplication. Use ordinary `Monomial n` of g power,
no n! in those coefficients; the unsplitting back to such Taylor coefficients from inside the
joint moment/log computation is `observe` (divide by n!).
Nothing numerical estimated. Interface also to later Taylor-aware reports with `PowerSeries`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Order
open Finset Function YM.Marker YM.Multi Join YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories (connected connected_quiet pass_connected part_sub)
open YM.Comparison.RG02.Cumulants
open scoped BigOperators Classical
variable {V : Type} [DecidableEq V] [Fintype V] (R : Census V) (r : ℕ)

def indices (r : ℕ) : Census (Fin r) where
  choices := Finset.univ
  blank := mem_univ _
  solo _ := mem_univ _
  down _ _ _ := mem_univ _
abbrev Index (r : ℕ) := (indices r).Mode
abbrev Board := Join.room R (indices r)
abbrev Grade := Poly (Board R r)
abbrev PTable := PowerSeries (Poly R)
abbrev Truncated := Polynomial (Poly R)

def axis : Grade R r := injectRight _ _ (lambda (indices r) 1)

def stamp : Truncated R →+* Grade R r := Polynomial.eval₂RingHom (injectLeft R (indices r)).toRingHom (axis R r)
lemma stamp_expr (f : Truncated R) :
    stamp R r f = f.eval₂ (injectLeft R (indices r)).toRingHom (axis R r) := rfl
lemma stamp_x : stamp R r Polynomial.X=axis R r := by rw [stamp_expr]; exact Polynomial.eval₂_X ..
lemma stamp_C (c : Poly R) : stamp R r (Polynomial.C c)=injectLeft R (indices r) c := by rw [stamp_expr]; exact Polynomial.eval₂_C ..
lemma stamp_monomial (c : Poly R) (n : ℕ) :
    stamp R r (Polynomial.monomial n c) = injectLeft R (indices r) c * axis R r ^ n := by rw [stamp_expr]; exact Polynomial.eval₂_monomial ..
lemma axis_power (n : ℕ) :
    axis R r ^ n = injectRight R (indices r) (lambda _ 1 ^ n) := (map_pow _ _ _).symm
lemma split_monomial (c : Poly R) (n : ℕ) (t : R.Mode) (u : Index r) :
    (stamp R r (Polynomial.monomial n c)).part (Join.pair t u) =
      if u.val.card=n then (n.factorial:ℂ)* c.part t else 0 := by
  rw [stamp_monomial,axis_power,Join.separate,factorial_lambda]
  split_ifs <;> simp [mul_comm]

lemma split_coeff (f : Truncated R) (t : R.Mode) (u : Index r) :
    (stamp R r f).part (Join.pair t u)=(u.val.card.factorial:ℂ)*(f.coeff u.val.card).part t := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add,Poly.part_plus, hp,hq,Polynomial.coeff_add,Poly.part_plus,mul_add]
  | monomial i a =>
    rw [split_monomial,Polynomial.coeff_monomial]; by_cases he : u.val.card=i
    · simp [he]
    simp [he, Ne.symm he]
lemma order_limit (u : Index r) : u.val.card≤r := (card_le_univ u.val).trans_eq (card_fin _)
private lemma series_part (x : PTable R) (t : R.Mode) (u : Index r) :
    (stamp R r (PowerSeries.trunc (r+1) x)).part (Join.pair t u) =
      (u.val.card.factorial:ℂ)*(PowerSeries.coeff u.val.card x).part t := by
  rw [split_coeff,PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_of_le (order_limit r u))]

def series : PTable R →+* Grade R r where
  toFun x := stamp R r (PowerSeries.trunc (r+1) x)
  map_zero' := by rw [map_zero,map_zero]
  map_one' := by rw [PowerSeries.trunc_one,map_one]
  map_add' _ _ := by rw [map_add,map_add]
  map_mul' x y := by
    rw [← map_mul]; refine both_parts (fun s t => ?_)
    rw [series_part,split_coeff,PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc (d:=t.val.card) x y (Nat.lt_succ_of_le (order_limit r t)),
      ← Polynomial.coe_mul, Polynomial.coeff_coe]

lemma polarization (x : PTable R) (t : R.Mode) (u : Index r) : (series R r x).part (Join.pair t u)=
      (u.val.card.factorial:ℂ)*(PowerSeries.coeff u.val.card x).part t := series_part ..
lemma series_poly (f : Truncated R) : series R r ↑f=stamp R r f := by
  apply both_parts; intro s t; rw [split_coeff,polarization,Polynomial.coeff_coe]
lemma series_x : series R r PowerSeries.X=axis R r := by rw [← Polynomial.coe_X,series_poly,stamp_x]
lemma series_C (x : Poly R) : series R r (PowerSeries.C x)= injectLeft R (indices r) x := by
  rw [← Polynomial.coe_C,series_poly,stamp_C]

lemma asks {n : ℕ} (h : n≤r) : ∃ t : Index r,t.val.card=n := by
  obtain ⟨u,-,he⟩ := exists_subset_card_eq (s:=univ (α:=Fin r)) (by simpa using h); exact ⟨⟨u,mem_univ u⟩,he⟩

def pick (r n : ℕ) : Index r := if h : n ≤ r then Classical.choose (asks r h) else (indices r).quiet
lemma picked {n : ℕ} (h : n≤r) : (pick r n).val.card=n := by rw [pick,dif_pos h]; exact Classical.choose_spec (asks r h)

/-- The `pick r n` term is convention; all surviving symmetric estimates can use ANY index
 set of that cardinality. Pad to zero above r. This is the normalized coefficient (Taylor
 degree n, *not* repeated coupling derivative). `n=0` - no divide on marks. -/
def observe (x : Grade R r) (n : ℕ) : Poly R := if n≤r then ((n.factorial:ℂ)⁻¹) •
    Poly.inject (fun t=> x.part (Join.pair t (pick r n))) else 0
lemma observation (p : PTable R) {n : ℕ} (h : n≤r) :
    observe R r (series R r p) n = PowerSeries.coeff n p := by
  have hf : (n.factorial:ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [observe,if_pos h]; ext s
  change (n.factorial:ℂ)⁻¹ * ((series R r p).part (Join.pair s (pick r n)))=_
  rw [polarization, picked r h, inv_mul_cancel_left₀ hf]

theorem trunc_complete (x y : PTable R) :
    series R r x = series R r y ↔ PowerSeries.trunc (r+1) x=PowerSeries.trunc (r+1) y := by
  constructor
  · intro h; ext i; simp_rw [PowerSeries.coeff_trunc]; split
    next h' => rw [← observation R r x (n:=i) (by omega),← observation R r y (n:=i) (by omega),h]
    rfl
  exact fun h=> congrArg (stamp R r) h

-- arithmetic compatible subalgebra (equals being invariant under coupler permutations).
def Symmetric {R : Census V} {r : ℕ} (x : Grade R r) := ∃ p : PTable R, series R r p=x

variable {R r}
namespace Symmetric
lemma known (p : PTable R) : Symmetric (series R r p) := ⟨p,rfl⟩
lemma each (x : Truncated R) : Symmetric (stamp R r x) := ⟨(x:PTable R),series_poly ..⟩
lemma neutral : Symmetric (0 : Grade R r) := ⟨_,map_zero _⟩
lemma one : Symmetric (1 : Grade R r) := ⟨_,map_one _⟩
lemma add {x y : Grade R r} (h : Symmetric x) (he : Symmetric y) : Symmetric (x+y) := by
  obtain ⟨p,rfl⟩ := h; obtain ⟨q,rfl⟩ := he; rw [← map_add]; exact known _
lemma neg {x : Grade R r} (h : Symmetric x) : Symmetric (-x) := by
  obtain ⟨p,rfl⟩:=h; rw [← map_neg]; exact known _
lemma sub {x y : Grade R r} (h : Symmetric x) (he : Symmetric y) : Symmetric (x-y) := by rw [sub_eq_add_neg]; exact h.add he.neg
lemma mul {x y : Grade R r} (h : Symmetric x) (he : Symmetric y) : Symmetric (x*y) := by
  obtain ⟨p,rfl⟩ := h; obtain ⟨q,rfl⟩ := he; rw [← map_mul]; exact known _
lemma pow {x : Grade R r} (h : Symmetric x) (j : ℕ) : Symmetric (x^j) := by
  obtain ⟨p,rfl⟩ := h; rw [← map_pow]; exact known _
lemma scalar (z : ℂ) : Symmetric (algebraMap ℂ (Grade R r) z) :=
  ⟨_, (series_C R r (algebraMap ℂ (Poly R) z)).trans ((injectLeft R (indices r)).commutes _)⟩
lemma smul (z : ℂ) {x : Grade R r} (h : Symmetric x) : Symmetric (z • x) := by
  rw [Algebra.smul_def]; exact (scalar z).mul h
lemma sum {ι:Type*} (u : Finset ι) (f : ι→Grade R r) (hf : ∀ i∈u, Symmetric (f i)) :
    Symmetric (∑ i∈u,f i) := by
  induction u using Finset.induction with
  | empty => rw [Finset.sum_empty]; exact neutral
  | insert i u hi ih => rw [Finset.sum_insert hi]; exact (hf i (mem_insert_self ..)).add (ih (fun j hj=>hf j (mem_insert_of_mem hj)))
lemma pass {x : Grade R r} (h : Symmetric x) : Symmetric x.pass := sum _ _ fun i _=> (h.pow i).smul _
lemma log {x : Grade R r} (h : Symmetric x) (hx : x.part (Board R r).quiet=1) : Symmetric (connected x) := by
  rw [log_formula hx]; exact sum _ _ fun i _=> (((one (R:=R) (r:=r)).sub h).pow _).smul _
lemma observe_part {x : Grade R r} (h : Symmetric x) (i : R.Mode) (t : Index r) :
    (t.val.card.factorial:ℂ)*(observe R r x t.val.card).part i = x.part (Join.pair i t) := by
  obtain ⟨p,rfl⟩:=h; rw [observation _ _ _ (order_limit ..), polarization]
end Symmetric


def collect (x : Grade R r) := PowerSeries.mk (observe R r x)
lemma collect_coeff (x : Grade R r) (i) : PowerSeries.coeff i (collect x)=observe R r x i := PowerSeries.coeff_mk ..

def render (x : Grade R r) := PowerSeries.trunc (r+1) (collect x)
lemma collect_eq (x : Grade R r) : collect x = ↑(render x) := by
  ext i; rw [Polynomial.coeff_coe,render,PowerSeries.coeff_trunc]; split
  next h => rfl
  next h=> rw [collect_coeff,observe, if_neg (by omega)]

lemma render_coeff (x : Grade R r) (i : ℕ) : (render x).coeff i=observe R r x i := by
  rw [← collect_coeff, collect_eq x, Polynomial.coeff_coe]
lemma observed {x : Grade R r} (i : R.Mode) {j : ℕ} (hj : j ≤ r) :
    (j.factorial:ℂ)*(observe R r x j).part i=x.part (Join.pair i (pick r j)) := by
  rw [observe,if_pos hj]
  change (j.factorial:ℂ)*((j.factorial:ℂ)⁻¹*x.part _)=_
  have h : (j.factorial:ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  rw [mul_inv_cancel_left₀ h]
lemma symmetric_test {x : Grade R r} (he : ∀ i : R.Mode,∀ t u : Index r,t.val.card=u.val.card → x.part (Join.pair i t)=x.part (Join.pair i u)) :
    Symmetric x := by
  refine ⟨collect x,both_parts (fun i t=> ?_)⟩
  rw [polarization,collect_coeff,observed i (order_limit ..),he i _ _ (picked _ (order_limit ..))]

lemma recollect {x : Grade R r} (h : Symmetric x) : series R r (collect x)=x := by
  apply both_parts; intro t u; rw [polarization, collect_coeff, h.observe_part]
lemma rerender {x : Grade R r} (h : Symmetric x) : stamp R r (render x)=x := by rw [← series_poly,← collect_eq,recollect h]
lemma series_render (f : PTable R) : render (series R r f)=PowerSeries.trunc (r+1) f := by
  apply Polynomial.ext; intro i; rw [render_coeff,PowerSeries.coeff_trunc]; split
  next h => rw [observation _ _ _ (show i≤r by omega)]
  next h=> rw [observe, if_neg (by omega)]
lemma render_mul {x y : Grade R r} (h : Symmetric x) (k : Symmetric y) :
    render (x*y)=PowerSeries.trunc (r+1) (collect x*collect y) := by
  rw [← series_render, map_mul,recollect h,recollect k]

-- explicit finite arithmetic compatibility, incl polynomial evaluation on scalar vacancies
lemma stamp_scalar (a : ℂ) (u : Truncated R) :
    stamp R r (Polynomial.C (algebraMap ℂ (Poly R) a) * u) = a • stamp R r u := by
  rw [map_mul,stamp_C, (injectLeft R (indices r)).commutes a, Algebra.smul_def]
lemma series_smul (a : ℂ) (x : PTable R) :
    series R r (a • x)=a • series R r x := by
  apply both_parts; intro t u; simp_rw [Poly.part_smul,polarization,PowerSeries.coeff_smul,Poly.part_smul]; ring
lemma observe_add (x y : Grade R r) (i : ℕ) :
    observe R r (x+y) i=observe R r x i+observe R r y i := by
  unfold observe; split
  next h =>
    ext t; rw [Poly.part_plus, Poly.part_smul,Poly.part_smul,Poly.part_smul];
    change _*(x.part _+ y.part _)= (i.factorial:ℂ)⁻¹*x.part _ + (i.factorial:ℂ)⁻¹*y.part _
    rw [mul_add]
  next h => exact (add_zero _).symm
lemma observe_smul (x : Grade R r) (a : ℂ) (i : ℕ) :
    observe R r (a•x) i=a•observe R r x i := by
  unfold observe; split
  next h =>
    ext t; simp only [Poly.part_smul]; change _*(a * x.part _)=a*((i.factorial:ℂ)⁻¹*x.part _); rw [mul_left_comm]
  next h=> rw [smul_zero]

def observeL (i : ℕ) : Grade R r →ₗ[ℂ] Poly R where
   toFun x := observe _ _ x i
   map_add' x y := observe_add x y i
   map_smul' a x := observe_smul x a i

lemma sym_coeff (x y : Grade R r) (h : Symmetric x) (k : Symmetric y) :
    x=y ↔ ∀ i ≤ r, observe R r x i = observe R r y i := by
  constructor
  · rintro rfl; simp
  intro hs; refine both_parts (fun i t => ?_); rw [← h.observe_part, ← k.observe_part, hs _ (order_limit ..)]
end YM.Comparison.RG02.Order
