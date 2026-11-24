import YM.Integration.NativePaidRootFieldColumns
import YM.Integration.NativeNormalizedBondTest
import YM.Push.STATIONARY_UNIFORM.Array
import YM.Work.F01

/-!
The actual stationary ray retains both the coarse identity and the copied
coarse field subtracted from RootField. The copy is bounded by the entire
parent pullback, whose exact multiplicity is card(Site L) = L^4.
The original one-bond test has exactly one real color coordinate. Thus the
complete Array.paint coordinate sum costs 1 + L^4 + the RootField column.
The same original stamp pays this by a fixed sixth power of log(hatBeta).
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.NativePaidStationaryArray
open Function Finset Lattice RG Precision Tree Exterior Matrix Laurent Bloch
open RG08 RG08.Line RG08.Supplies
open Push.Uniform Comparison.RG02 PhysicalNext.Repeat.Legato
open scoped BigOperators Classical

variable {G : Gauge}

private theorem sum_comp_le {α β : Type*} [Fintype α] [Fintype β]
    (t : α → β) (ht : Injective t) (f : β → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∑ i, f (t i)) ≤ ∑ i, f i := by
  calc
    _ = ∑ i ∈ Finset.univ.image t, f i := (Finset.sum_image ht.injOn).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun i _ _ => hf i)

private theorem flatten_bond (G : Gauge) (n : Side) (k : G.ColorIndex) :
    FreeResolvent.flatten (NativeNormalizedBondTest.bondField G n k) =
      Pi.single (FreeResolvent.ix (NativeNormalizedBondTest.anchor n) k) 1 := by
  funext z
  rcases z with ⟨x, d, j⟩
  by_cases hx : x = 0 <;> by_cases hd : d = coord (0 : Axis) <;>
    by_cases hj : j = k <;>
    simp [FreeResolvent.flatten, FreeResolvent.ix,
      NativeNormalizedBondTest.bondField, NativeNormalizedBondTest.scalarBond,
      NativeNormalizedBondTest.anchor, NativeNormalizedBondTest.colorUnit,
      Pi.single_apply, Prod.mk.injEq, hx, hd, hj, eq_comm]
  exact Ne.symm hj

private theorem collect_bond (G : Gauge) (n : Side) (k : G.ColorIndex) :
    collect G (NativeNormalizedBondTest.bondField G n k) =
      Pi.single ((0 : Site n), (0 : Axis)) (NativeNormalizedBondTest.colorUnit G k) := by
  funext e
  rcases e with ⟨x, d⟩
  by_cases hx : x = 0 <;> by_cases hd : d = 0 <;>
    simp [collect, NativeNormalizedBondTest.bondField,
      NativeNormalizedBondTest.scalarBond, NativeNormalizedBondTest.anchor,
      Prod.mk.injEq, coord_iff, hx, hd]

private theorem collect_bond_mass (G : Gauge) (n : Side) (k : G.ColorIndex) :
    (∑ e : Pressure.Bond n, ∑ j : G.ColorIndex,
      |collect G (NativeNormalizedBondTest.bondField G n k) e j|) = 1 := by
  rw [collect_bond, Finset.sum_eq_single_of_mem ((0 : Site n), (0 : Axis)) (Finset.mem_univ _)]
  · rw [Pi.single_eq_same, Finset.sum_eq_single_of_mem k (Finset.mem_univ _)]
    · simp [NativeNormalizedBondTest.colorUnit]
    · intro j _ hj
      simp [NativeNormalizedBondTest.colorUnit, hj]
  · intro e _ he
    rw [Pi.single_eq_of_ne he]
    simp

private theorem primary_bond_mass (G : Gauge) (n : Side) (k : G.ColorIndex) :
    (∑ q : Primary n G, |NativeNormalizedBondTest.bondField G n k q.1 q.2|) = 1 := by
  have h : (∑ q : FreeResolvent.Slot G n 1,
      |FreeResolvent.flatten (NativeNormalizedBondTest.bondField G n k) q|) = 1 := by
    rw [flatten_bond, Finset.sum_eq_single_of_mem
      (FreeResolvent.ix (NativeNormalizedBondTest.anchor n) k) (Finset.mem_univ _)]
    · simp
    · intro q _ hq
      rw [Pi.single_eq_of_ne hq, abs_zero]
  simpa only [Fintype.sum_prod_type, FreeResolvent.flatten] using h

private theorem paint_inverse_mass {c f : Side} {p : Ratio c f} (F : Forest p)
    (x : fieldDir G c 1) (v : AxisChart G F) :
    (∑ q : Push.Uniform.Joint F G, |(paint F G).symm (x, v) q|) =
      (∑ q : Primary c G, |x q.1 q.2|) +
        ∑ q : Precision.Key F G, |v q.1 q.2| := by
  exact Fintype.sum_sum_type _

/-- Bound the literal copied field on every free coordinate. The full block
multiplicity is retained even though the crossing indicator can reduce it. -/
theorem copy_bond_l1 {c f : Side} (p : Ratio c f) (F : Forest p)
    (k : G.ColorIndex) :
    (∑ q : Precision.Key F G,
      |linearCopy p (collect G (NativeNormalizedBondTest.bondField G c k))
        q.1.val q.2|) ≤ (p.count.val : ℝ) ^ 4 := by
  let A := collect G (NativeNormalizedBondTest.bondField G c k)
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ e : Pressure.Bond f, ∑ j : G.ColorIndex, |linearCopy p A e j| :=
      sum_comp_le (fun x : F.Free => x.val) Subtype.val_injective
        (fun e => ∑ j : G.ColorIndex, |linearCopy p A e j|)
        (fun _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    _ ≤ ∑ e : Pressure.Bond f, ∑ j : G.ColorIndex,
        |A (p.parent e.1, e.2) j| := by
      apply Finset.sum_le_sum
      intro e _
      by_cases h : p.parent (e.1 + step e.2) = p.parent e.1
      · simp only [linearCopy, if_pos h]
        change (∑ _ : G.ColorIndex, |(0 : ℝ)|) ≤
          ∑ j : G.ColorIndex, |A (p.parent e.1, e.2) j|
        rw [abs_zero, Finset.sum_const_zero]
        exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
      · simp only [linearCopy, if_neg h]
        exact le_rfl
    _ = (Fintype.card (Site p.count) : ℝ) *
        ∑ e : Pressure.Bond c, ∑ j : G.ColorIndex, |A e j| :=
      Work.F01.sum_parent_bond p (fun e => ∑ j : G.ColorIndex, |A e j|)
    _ = (p.count.val : ℝ) ^ 4 := by
      dsimp only [A]
      rw [collect_bond_mass, mul_one, Lattice.site_card, Nat.cast_pow]

section Actual
variable (R : Run G) (Y : Bulk.Chain R.family.path)
    (N period m : ℕ) (hm : m < N)

local notation "a" => R.family.path.levels
local notation "S" => R.family.path.levels.clock.op m period
local notation "F" => green (R.family.path.levels.clock.op m period)

/-- The original Array coordinates of the actual stationary one-bond ray. -/
def bondRay (k : G.ColorIndex) : Positions (Push.Uniform.Joint F G) :=
  let B := NativeNormalizedBondTest.bondField G ((a).S.side m period) k
  (paint F G).symm (B, fderiv ℝ ((Y.step N m period hm).b F) 0 B)

/-- Coarse identity, full copied-coarse multiplicity and complete RootField
column are all charged separately on the same original Run. -/
theorem bondRay_bound (hAttached : ActualRunNativeComponentRecipe.Attached R)
    (t : (S).Choices) (k : G.ColorIndex) :
    (∑ q, |bondRay R Y N period m hm k q|) ≤
      1 + (((a).S.block m).val : ℝ) ^ 4 +
        (Fintype.card (Stationary.Loc G 1) : ℝ) *
          (Real.exp 4 * (Real.log ((a).clock.hatBeta m)) ^ 6) := by
  let B := NativeNormalizedBondTest.bondField G ((a).S.side m period) k
  let V := fderiv ℝ ((Y.step N m period hm).b F) 0 B
  let M := Cell.RootField (a).clock.kernel G S (R.alloy.B.M.H N (m + 1))
  let C := (Fintype.card (Stationary.Loc G 1) : ℝ) *
    (Real.exp 4 * (Real.log ((a).clock.hatBeta m)) ^ 6)
  have hroot : (∑ q : Precision.Key F G,
      |(M *ᵥ FreeResolvent.flatten B) (FreeResolvent.plant F q)|) ≤ C := by
    refine (sum_comp_le (FreeResolvent.plant F) (FreeResolvent.plant_inj F)
      (fun z => |(M *ᵥ FreeResolvent.flatten B) z|) (fun _ => abs_nonneg _)).trans ?_
    dsimp only [M, B]
    rw [flatten_bond, Matrix.mulVec_single_one]
    exact NativePaidRootFieldColumns.root_column R hAttached N period m hm
      (FreeResolvent.ix (NativeNormalizedBondTest.anchor ((a).S.side m period)) k)
  have hcopy : (∑ q : Precision.Key F G,
      |linearCopy (S).ratio (collect G B) q.1.val q.2|) ≤
        (((a).S.block m).val : ℝ) ^ 4 :=
    copy_bond_l1 (S).ratio F k
  have hv : (∑ q : Precision.Key F G, |V q.1 q.2|) ≤
      C + (((a).S.block m).val : ℝ) ^ 4 := by
    calc
      _ = ∑ q : Precision.Key F G,
          |(M *ᵥ FreeResolvent.flatten B) (FreeResolvent.plant F q) -
            (linearCopy (S).ratio (collect G B)) q.1.val q.2| := by
        apply Finset.sum_congr rfl
        intro q _
        exact congrArg abs
          (ActualNativeKernelDictionary.actual_stationary R Y N period m hm
            t B q.1 q.2)
      _ ≤ (∑ q : Precision.Key F G,
          |(M *ᵥ FreeResolvent.flatten B) (FreeResolvent.plant F q)|) +
          ∑ q : Precision.Key F G,
            |(linearCopy (S).ratio (collect G B)) q.1.val q.2| := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_le_sum
        intro q _
        simpa only [Real.norm_eq_abs] using
          norm_sub_le ((M *ᵥ FreeResolvent.flatten B) (FreeResolvent.plant F q))
            ((linearCopy (S).ratio (collect G B)) q.1.val q.2)
      _ ≤ _ := add_le_add hroot hcopy
  change (∑ q : Push.Uniform.Joint F G, |(paint F G).symm (B, V) q|) ≤ _
  calc
    _ = 1 + ∑ q : Precision.Key F G, |V q.1 q.2| := by
      rw [paint_inverse_mass]
      exact congrArg (fun r : ℝ => r + ∑ q : Precision.Key F G, |V q.1 q.2|)
        (primary_bond_mass G ((a).S.side m period) k)
    _ ≤ 1 + (C + (((a).S.block m).val : ℝ) ^ 4) := add_le_add le_rfl hv
    _ = _ := by dsimp only [C]; ring

/-- The original length receipt pays the copy and the identity inside the
same fixed logarithmic degree; no volume or color factor is suppressed. -/
theorem bondRay_paid (hAttached : ActualRunNativeComponentRecipe.Attached R)
    (t : (S).Choices) (k : G.ColorIndex) :
    (∑ q, |bondRay R Y N period m hm k q|) ≤
      (2 + (Fintype.card (Stationary.Loc G 1) : ℝ) * Real.exp 4) *
        (Real.log ((a).clock.hatBeta m)) ^ 6 := by
  have h := bondRay_bound R Y N period m hm hAttached t k
  obtain ⟨s, T, C, n, -, -, -, hquote, -, -, -, hReal⟩ := hAttached
  have hpaid : Yamen.Payment G R.metals.K C.secondary
      (Next.Foundations.chart G) a := by
    rw [hquote]
    exact hReal.payment
  have hlog : 1 ≤ Real.log ((a).clock.hatBeta m) :=
    (NativePaidKernelCosts.paid_costs hpaid m).1
  have hlength := NativePaidRootFieldColumns.length_paid hpaid m
  have hfour : (((a).S.block m).val : ℝ) ^ 4 ≤
      (Real.log ((a).clock.hatBeta m)) ^ 6 :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hlength 4).trans
      (pow_le_pow_right₀ hlog (by decide : 4 ≤ 6))
  have hone : 1 ≤ (Real.log ((a).clock.hatBeta m)) ^ 6 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hlog 6
  refine h.trans ?_
  calc
    _ ≤ (Real.log ((a).clock.hatBeta m)) ^ 6 +
        (Real.log ((a).clock.hatBeta m)) ^ 6 +
        (Fintype.card (Stationary.Loc G 1) : ℝ) *
          (Real.exp 4 * (Real.log ((a).clock.hatBeta m)) ^ 6) :=
      add_le_add (add_le_add hone hfour) le_rfl
    _ = _ := by ring

/-- The actual nonzero normalized test is supplied internally by the same
Run; this is the exact coarse-plus-stationary Array ray used by the vertex. -/
theorem actualRay_paid (hG : G.Simple)
    (hAttached : ActualRunNativeComponentRecipe.Attached R) (t : (S).Choices) :
    let B := NativeNormalizedBondTest.actualField R hG m period
    (∑ q : Push.Uniform.Joint F G,
      |(paint F G).symm (B, fderiv ℝ ((Y.step N m period hm).b F) 0 B) q|) ≤
        (2 + (Fintype.card (Stationary.Loc G 1) : ℝ) * Real.exp 4) *
          (Real.log ((a).clock.hatBeta m)) ^ 6 := by
  exact bondRay_paid R Y N period m hm hAttached t
    (NativeNormalizedBondTest.colorIndex G hG)

end Actual
end YM.Integration.NativePaidStationaryArray
end
