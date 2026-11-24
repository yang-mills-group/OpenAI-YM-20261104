import YM.WilsonMS.Stencil.InkLeg
/-!
# Why the radial survey ALSO works at the required leading rank, when links
use the midpoint convention in the MS comparison.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonMS.Webs.Midpt
open Function Filter Finset Set MeasureTheory XSpace
open Lattice RG Maxwell Source Labels Maxwell.Free Wilson
open MS MS.Local MS.Local.Physical MS.Plane MS.Koszul MS.Theater MS.Tone
open MS.Menus MS.Land MS.Local.BV MS.Cylinder MS.Book MS.Native MS.Puff.Actors MS.Landau.Detect
open MS.Native.Sew MS.Native.Studio MS.Native.Wilsonian MS.Native.Chart MS.Native.Draft
  MS.Cylinder.Lab MS.Cylinder.Taylor
open Work Drops Tensor YM.Analysis G03
open scoped Classical Topology ContDiff BigOperators RealInnerProductSpace Matrix.Norms.Frobenius
variable {G : Gauge} {H : Source.Hol G} {p : Labels.Pol G} {d j h : ℕ} (A : Survey G H d)
local notation "E" => Edge Cover
local notation "U" => Lot G E

def station (e : E) (t : ℝ) :=
  castPos e.1 + t • basis e.2

def value (X : Feet G h) (e : E) (t : ℝ) :=
  Tensor.diagonal (X.val e.2) (station e t)

lemma continuous_line (X : Feet G h) (e : E) : Continuous (value X e) :=
  (diag_smooth _ ω).continuous.comp
    (by
      unfold station
      fun_prop)

def prime (G : Gauge) (n : ℕ) : Feet G n →ₗ[ℝ] Lot G E
    where
  toFun X e := ∫ t : ℝ in 0..1, value X e t
  map_add' X
    Y :=
    funext fun i =>
      intervalIntegral.integral_add ((continuous_line X i).intervalIntegrable _ _)
        ((continuous_line Y i).intervalIntegrable _ _)
  map_smul' c X := by
    funext i
    change (∫ t : ℝ in 0..1, c • value X i t) = c • _
    rw [intervalIntegral.integral_smul]

lemma slopes (X : Head G (h + 1)) (e : E) :
    prime G h (gradS G h X) e =
      Tensor.diagonal (X.val ()) (castPos (e.1 + step e.2)) -
        Tensor.diagonal (X.val ()) (castPos e.1) := by
  let D := Tensor.diagonal (X.val ())
  let f (t : ℝ) := D (station e t)
  have he (t : ℝ) : value (gradS G h X) e t = fderiv ℝ D (station e t) (basis e.2) :=
    congr_fun (workL (basis e.2) X ()) _
  have hv (t : ℝ) : HasDerivAt f (value (gradS G h X) e t) t := by
    rw [he]
    apply
      (show HasFDerivAt D _ (station e t) from
            ((diag_smooth _ ω).differentiable (by simp) _).hasFDerivAt).comp_hasDerivAt
        _
    unfold station
    simpa only [Pi.add_apply, one_smul, zero_add] using!
      (hasDerivAt_const t (castPos e.1)).add ((hasDerivAt_id' t).smul_const (basis e.2))
  change (∫ t : ℝ in 0..1, value (gradS G h X) e t) = _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hv t)
      ((continuous_line _ _).intervalIntegrable _ _)]
  simp only [f, station, castPos_step, one_smul, zero_smul, add_zero, D]

lemma wash (X : Head G (h + 1)) : probeSlots A (prime G h (gradS G h X)) = 0 := by
  ext1 j
  change CurlOn _ _ = 0
  unfold CurlOn
  rw [G03.square_sum]
  simp_rw [slopes]
  rw [add_right_comm (Slot.offset _)]
  abel

lemma dust (X : Feet G h) : probeSlots A (prime G h (carve G h X)) = probeSlots A (prime G h X) := by
  rw [carveΩ, map_sub, map_smul, map_sub, map_smul, wash, smul_zero, sub_zero]

def ticked (h : j + 2 ≤ d) (v : Labels.Taylor G j) : Snap G d :=
  Pi.single ⟨j, by omega⟩ v

lemma ticks_at (hx : j + 2 ≤ d) (x : Labels.Taylor G j) : expand d (ticked hx x) = Pi.single j x := by
  funext i
  by_cases H : i = j
  · subst i
    simp only [expand, dif_pos (show j < d - 1 by omega), ticked, Pi.single_eq_same]
  rw [Pi.single_eq_of_ne H]
  unfold expand ticked
  split
  rename_i he
  rw [Pi.single_eq_of_ne (show (⟨i, he⟩ : Fin (d - 1)) ≠ ⟨j, by omega⟩ from Fin.ne_of_val_ne H)]
  rfl

lemma restore_edge (hx : j + 2 ≤ d) (x : Labels.Taylor G j) :
    access (ticked hx x) = prime G (j + 1) (step_in G j x) := by
  ext1 ⟨a, i⟩
  rw [G03.edge_sum, Finset.sum_eq_single_of_mem j (by simp [show j < d - 1 by omega])]
  · rw [ticks_at, Pi.single_eq_same]
    rfl
  intro y _ hi
  rw [ticks_at, Pi.single_eq_of_ne hi]
  change (∫ t : ℝ in 0..1, (0 : G.Color)) = 0
  simp

lemma readOne (hx : j + 2 ≤ d) (x : Labels.Taylor G j) :
    A.extract (probeSlots A (prime G (j + 1) (step_in G j x))) = ticked hx x := by
  rw [← restore_edge hx]
  exact A.linear_jet _

lemma read_lift (hx : j + 2 ≤ d) (X : Feet G (j + 1)) :
    A.extract (probeSlots A (prime G (j + 1) X)) = ticked hx (yard G j X) := by
  rw [← readOne A hx (yard G j X), taxiY, dust]

lemma read_top (x : Feet G (h + 1)) (i : Fin (Labels.dim G h)) (hx : h + 2 ≤ d) :
    evaluateL A ⟨h, i⟩ (prime G (h + 1) x) = (axes G h).repr (yard G h x) i := by
  change Survey.component _ (A.extract (probeSlots A _)) = _
  rw [read_lift A hx, Survey.component_point, ticks_at, Pi.single_eq_same]

lemma read_bottom (x : Feet G 0) : probeSlots A (prime G 0 x) = 0 := by
  rw [← dust A x, show carve G 0 x = 0 from (Submodule.mem_bot ℝ).mp (weightT G ▸ house x), map_zero,
    map_zero]

lemma read_void (i : Labels.Key G) (hx : i.1 + 2 ≤ d) {j : ℕ} (x : Feet G j) (hz : j ≤ i.1) :
    evaluateL A i (prime G j x) = 0 := by
  change Survey.component _ (A.extract (probeSlots A _)) = _
  cases j with
  | zero => rw [read_bottom, map_zero, map_zero]
  | succ j =>
    rw [read_lift A (by omega), Survey.component_point, ticks_at, Pi.single_eq_of_ne (by omega),
      map_zero, Finsupp.zero_apply]

def lookPt (X : Feet G j) := fun (e : E) => value X e (1 / 2)

lemma trace_vanish (a b : Axis) (he : a ≠ b) (p : FourP) (v : G.Color) (y : E4) :
    Tensor.diagonal ((speak j a p v).val b) y = 0 := by
  unfold speak
  rw [away j _ _ he.symm]
  rfl

lemma on_print (a : Axis) (p : FourP) (v : G.Color) (y : E4) :
    Tensor.diagonal ((speak j a p v).val a) y = (Theater.amount j * inner ℝ (fixF p) y ^ j) • v := by
  unfold Tensor.diagonal speak
  rw [wearing]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_smul]
variable (a : Axis) (p : FourP) (v : G.Color)

def tip₀ (n i : ℕ) (s : ℝ) :=
  amount n / amount i * n.choose i * ((s - 1 / 2) * p a) ^ (n - i)

lemma point (n : ℕ) (e : E) (s : ℝ) :
    value (speak n a p v) e s =
      ∑ j ∈ Finset.range (n + 1), tip₀ a p n j s • lookPt (speak j a p v) e := by
  unfold value lookPt
  by_cases he : a = e.2
  swap
  · rw [trace_vanish _ _ he]
    exact
      (Finset.sum_eq_zero fun j _ => by
          unfold value
          rw [trace_vanish _ _ he, smul_zero]).symm
  rcases e with ⟨u, w⟩
  dsimp only at he
  subst w
  dsimp only
  rw [on_print]
  unfold value
  dsimp only
  simp_rw [on_print, smul_smul, ← Finset.sum_smul]
  apply congr_arg (· • v)
  let F := fixF p
  let B := station (u, a) (1 / 2)
  rw [show station (u, a) s = B + (s - 1 / 2) • basis a from ?_]
  swap
  · unfold station B
    change (castPos u + s • basis a) = (castPos u + (1 / 2 : ℝ) • basis a) + (s - 1 / 2) • basis a
    module
  rw [inner_add_right, real_inner_smul_right, lean_axis, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold tip₀
  have hv := amt_p i
  unfold B
  field_simp

def shiftC (n i : ℕ) :=
  ∫ s : ℝ in 0..1, tip₀ a p n i s

lemma mean_identity (n : ℕ) :
    prime G n (speak n a p v) =
      lookPt (speak n a p v) + ∑ i ∈ Finset.range n, shiftC a p n i • lookPt (speak i a p v) := by
  ext1 e
  change (∫ s : ℝ in 0..1, value _ e s) = _
  simp_rw [point,
    intervalIntegral.integral_finsetSum (s := Finset.range (n + 1)) (f := fun i (s : ℝ) =>
      tip₀ a p n i s • lookPt (speak i a p v) e)
      (fun i _ =>
        Continuous.intervalIntegrable
          (by
            unfold tip₀
            fun_prop)
          _ _),
    intervalIntegral.integral_smul_const, Finset.sum_range_succ]
  rw [show (∫ s : ℝ in 0..1, tip₀ a p n n s) = 1 from ?_, one_smul, Pi.add_apply, Finset.sum_apply,
    add_comm]
  swap
  · unfold tip₀
    simp [(amt_p n).ne']
  rfl

lemma sends (i : Labels.Key G) (hi : i.1 + 2 ≤ d) (j : ℕ) (hz : j ≤ i.1 + 1) :
    evaluateL A i (prime G j (speak j a p v)) = evaluateL A i (lookPt (speak j a p v)) := by
  rw [mean_identity, map_add, map_sum, Finset.sum_eq_zero, add_zero]
  intro l he
  rw [map_smul, ← sends i hi l _, read_void A i hi _ _, smul_zero]
  all_goals
    first
    | exact v
    | ( obtain ht := Finset.mem_range.mp he
        omega)
termination_by j
decreasing_by
  obtain hx := Finset.mem_range.mp he
  omega
end YM.WilsonMS.Webs.Midpt
