import YM.Comparison.RG02.Order.Polar

/-!
# Vacuum projections onto pure coupling grades

Identify the *total* moments, source-normalized moments, and connected and
field-independent (marked and unmarked) charged exponents. At any finite expansion order r. Keep
the conditional denominator (series after a fixed vacancy leading coefficient factor) **before**
passing to marked logs. `bottom` projects out nonempty physical marks but leaves all the pure
couplings (including extensive/unmarked but field- and background-dependent terms). The real
`R.v`, determinant etc will be in a separate scalar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Order
open Finset Function YM.Marker YM.Multi Join YM.Primitives.GCC.Anchor
open YM.Extra.Trajectories (connected connected_quiet pass_connected part_sub)
open YM.Comparison.RG02.Cumulants
open scoped BigOperators Classical
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} {r : ℕ}

def blank (R : Census V) : Poly R →ₐ[ℂ] ℂ where
  toFun x := x.part R.quiet
  map_one' := by simp
  map_zero' := rfl
  map_mul' := Poly.quiet_mul
  map_add' _ _ := rfl
  commutes' z := by change (Poly.send R.quiet z).part R.quiet=z; simp
omit [Fintype V] in
lemma blank_score (x : Poly R) : blank R x=x.part R.quiet := rfl

def bottom (R : Census V) (r) : Grade R r →ₐ[ℂ] Grade R r :=
  (injectRight R _).comp (projectRight R _)
def blanked (R : Census V) : Poly R →+* Poly R := (algebraMap ℂ (Poly R)).comp (blank R).toRingHom
omit [Fintype V] in
lemma pure_marks (x : Poly R) (t : R.Mode) : (blanked R x).part t=if t=R.quiet then x.part R.quiet else 0 := Poly.part_send ..
lemma bottom_value (x : Grade R r) (t : R.Mode) (u : Index r) :
    (bottom R r x).part (Join.pair t u)=if t=R.quiet then x.part (Join.pair R.quiet u) else 0 := right_part ..
lemma bottom_quiet (x : Grade R r) : (bottom R r x).part (Board R r).quiet=x.part (Board R r).quiet := by
  rw [← pair_quiet, bottom_value, if_pos rfl]
lemma bottom_map (p : PTable R) : bottom R r (series R r p) = series R r (PowerSeries.map (blanked R) p) := by
  apply both_parts; intro t u; by_cases h : t=R.quiet
  all_goals simp only [polarization, bottom_value,PowerSeries.coeff_map,pure_marks, h,↓reduceIte,mul_zero]
lemma observe_bottom (x : Grade R r) (n : ℕ) : observe R r (bottom R r x) n= blanked R (observe R r x n) := by
  unfold observe; split
  next h =>
    ext t
    simp_rw [pure_marks,Poly.part_smul]
    change _ * ((bottom R r x).part _) = _
    rw [bottom_value]; split_ifs with he; rfl; rw [mul_zero]
  next h=> rw [map_zero]

lemma bottom_repeat (x : Grade R r) : bottom R r (bottom R r x)=bottom R r x := by
  simp only [bottom,AlgHom.comp_apply,project_inject_right]

lemma Symmetric.vacant {x : Grade R r} (h : Symmetric x) : Symmetric (bottom R r x) := by
  obtain ⟨p,rfl⟩:=h; rw [bottom_map]; exact Symmetric.known _

/-- Represents the *full* output using the leading unmarked scalar as prefactor. -/
def UnitLeading (x : Grade R r) : Prop := x.part (Board R r).quiet=1
/-- Relative to the leading scalar, requires UnitLeading before use. Full unmarked coupling
    corrections (e.g., inverse determinant etc.) are still in x. -/
def denominator (x : Grade R r) := bottom R r x
def ratio (x : Grade R r) := x*inverseMass (denominator x)
def logVac (x : Grade R r) := connected (denominator x)
def logMarked (x : Grade R r) := connected (ratio x)

lemma bottom_inverse {x : Grade R r} (h : UnitLeading x) :
    bottom R r (inverseMass x)=inverseMass (bottom R r x) := by
  rw [geometric_inverse x h, geometric_inverse _ ((bottom_quiet x).trans h)];
  simp
lemma ratio_quiet {x : Grade R r} (h : UnitLeading x) : UnitLeading (ratio x) := by
  have hd : (denominator x).part (Board R r).quiet=1 := (bottom_quiet x).trans h
  unfold UnitLeading ratio; rw [Poly.quiet_mul,h,one_mul]
  exact Poly.pass_part _ (by rw [Poly.part_neg, connected_quiet hd, neg_zero])
lemma ratio_pure {x : Grade R r} (h : UnitLeading x) : bottom R r (ratio x)=1 := by
  rw [ratio, map_mul,denominator,bottom_inverse (show UnitLeading _ from (bottom_quiet x).trans h)];
  rw [bottom_repeat]; exact right_inverse ((bottom_quiet x).trans h)
lemma recovers {x : Grade R r} (h : UnitLeading x) : denominator x*ratio x=x := by
  rw [ratio,← mul_assoc,mul_comm (denominator x),mul_assoc,right_inverse (show (denominator x).part (Board R r).quiet=1 from (bottom_quiet x).trans h),mul_one]
lemma ratio_unique {x y : Grade R r} (h : UnitLeading x) (hz : denominator x*y=x) : y=ratio x := by
  calc
    _ = (denominator x*inverseMass (denominator x))*y := by rw [right_inverse (show (denominator x).part (Board R r).quiet=1 from (bottom_quiet x).trans h), one_mul]
    _ = (denominator x*y)*inverseMass (denominator x) := by ring
    _ = _ := by rw [hz]; rfl

lemma log_vacant {x : Grade R r} (h : UnitLeading x) : bottom R r (logVac x)=logVac x := by
  have hv := (bottom_quiet x).trans h
  unfold logVac denominator; rw [log_map (bottom R r) bottom_quiet hv,bottom_repeat]
lemma log_marked {x : Grade R r} (h : UnitLeading x) : bottom R r (logMarked x)=0 := by
  unfold logMarked; rw [log_map (bottom R r) bottom_quiet (ratio_quiet h),ratio_pure h]
  rw [log_formula (show (1 : Grade R r).part (Board R r).quiet=1 from by simp)]
  simp [unipotentLog]
lemma log_full {x : Grade R r} (h : UnitLeading x) : connected x=logVac x+logMarked x := by
  nth_rw 1 [← recovers h]
  exact connected_mul ((bottom_quiet x).trans h : (denominator x).part (Board R r).quiet = 1) (ratio_quiet h)

lemma sym_inverseMass {x : Grade R r} (h : UnitLeading x) (k : Symmetric x) :
    Symmetric (inverseMass x) := Symmetric.pass (k.log h|>.neg)
lemma sym_ratio {x : Grade R r} (h : UnitLeading x) (k : Symmetric x) : Symmetric (ratio x) :=
  k.mul (sym_inverseMass ((bottom_quiet x).trans h) k.vacant)
lemma sym_logMarked {x : Grade R r} (h : UnitLeading x) (k : Symmetric x) : Symmetric (logMarked x) :=
  (sym_ratio h k).log (ratio_quiet h)
lemma sym_logVac {x : Grade R r} (h : UnitLeading x) (k : Symmetric x) : Symmetric (logVac x) :=
  k.vacant.log ((bottom_quiet x).trans h)

end YM.Comparison.RG02.Order
