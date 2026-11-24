import YM.Integration.NativeOriginalMainBondPrice
import YM.Integration.NativeOriginalLoopBondJets
import YM.Integration.OriginalLayerBondJetBound
import YM.Integration.ActualCoarseStagePrice

/-! A single polynomial bill for the three original field contributions.
The numerical schedule and its price record are unchanged. Constants are
chosen before the retained level, cutoff, period and original layer data.
The main action, full loop and complete layer list are centered separately;
every derivative order up to the requested finite bound is retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualOriginalFieldCost

open Function Filter Lattice Wilson RG Precision Exterior
open PhysicalNext.Repeat.Legato
open IterationFour IterationFour.Vacuum LocalComparison.Global FullQLocal
open FullQLocal.RenderedStep Comparison.RG02.Assembly
open scoped Topology BigOperators ContDiff Classical

private theorem stage_parts (p : Stage) {W : ℝ}
    (h : NativeStageLogarithmicPrice.stageSum p ≤ W) :
    1 + p.paths ≤ W ∧ 1 + p.width⁻¹ ≤ W := by
  have hp := p.paths_pos
  have hw := inv_pos.mpr p.width_pos
  have hc := p.columns_ge
  have hr := p.clip.radius_pos
  have he := p.price_pos
  dsimp only [NativeStageLogarithmicPrice.stageSum] at h
  constructor <;> linarith

private theorem output_inverse {G : Gauge} {V : Type} {F : YM.Family G}
    {J : Request V} (A : NumericSchedule F J) (m : ℕ) :
    (A.outputWidth m)⁻¹ ≤ A.admittedCost m := by
  have hi := inv_pos.mpr (A.input_width_pos m)
  have hr := A.radius_loss_positive m
  have h := A.cost_covers_widths m
  linarith

private theorem loop_cap_nonneg {G : Gauge} (S : Calendar G) (m : ℕ) :
    0 ≤ S.loopCap m := by
  unfold Calendar.loopCap Calendar.monitor
  positivity

private theorem loop_cap_le {G : Gauge} {V : Type} {F : YM.Family G}
    {J : Request V} (A : NumericSchedule F J) (m : ℕ) :
    F.path.levels.clock.loopCap m ≤ A.admittedCost m := by
  let S := F.path.levels
  have h0 : 0 ≤ (S.clock.coverSize m : ℝ) := by positivity
  have h1 : 0 ≤ (S.clock.coverSize (m + 1) : ℝ) := by positivity
  have h2 : 0 ≤ S.clock.monitor m := by unfold Calendar.monitor; positivity
  have h3 : 0 ≤ S.clock.monitor (m + 1) := by unfold Calendar.monitor; positivity
  have h4 := loop_cap_nonneg S.clock (m + 1)
  have h5 := (S.params m).paths_pos.le
  have h6 := (S.params (m + 1)).paths_pos.le
  have h7 : 0 ≤ (S.params m).columns := zero_le_one.trans (S.params m).columns_ge
  have h8 : 0 ≤ (S.params (m + 1)).columns :=
    zero_le_one.trans (S.params (m + 1)).columns_ge
  have h9 := (S.params m).clip.radius_pos.le
  have h10 := (S.params (m + 1)).clip.radius_pos.le
  have h := A.cost_covers_geometry m
  dsimp only [S] at *
  linarith only [h, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

private theorem two_powers {a b x y z : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxz : x ≤ z) (hyz : y ≤ z) (i j : ℕ) :
    a * x^i * y^j ≤ b * z^(i+j) := by
  have hb : 0 ≤ b := ha.trans hab
  have hz : 0 ≤ z := hx.trans hxz
  have hleft : a * x^i ≤ b * z^i :=
    mul_le_mul hab (pow_le_pow_left₀ hx hxz i) (pow_nonneg hx i) hb
  have h := mul_le_mul hleft (pow_le_pow_left₀ hy hyz j)
    (pow_nonneg hy j) (mul_nonneg hb (pow_nonneg hz i))
  simpa only [pow_add, mul_assoc] using h

/-- One original-schedule event pays all three full centered field terms,
uniformly through the requested finite derivative order. -/
theorem uniform_cost {G : Gauge} (n rankCap : ℕ)
    (T : Run G) (hG : G.Simple) (hT : ActualRunNativeComponentRecipe.Attached T)
    {V : Type} {J : Request V} (A : NumericSchedule T.family J) (K : NumericPrices A) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ᶠ m : ℕ in atTop,
      ∀ N period : ℕ, m ≤ N →
      ∀ {layers : List (Piece G (T.family.side m period))} {point : BudgetPoint}
        {order : ℕ}
        (_H : GradedVacuumLayers layers point order rankCap
          (A.outputWidth m) (K.geometry m)),
      ∀ k : ℕ, k ≤ n →
      ‖jet (fun B : fieldDir G (T.family.side m period) 1 =>
          mainTerm (T.family.path.levels.params m).clip
            (T.family.path.rep N period m).path (represent B)) k
          (NativeNormalizedBondTest.actualField T hG m period) -
        jet (fun B : fieldDir G (T.family.side m period) 1 =>
          mainTerm (T.family.path.levels.params m).clip
            (T.family.path.rep N period m).path (represent B)) k 0‖ +
      ‖jet (fun B : fieldDir G (T.family.side m period) 1 =>
          loop (T.family.path.rep N period m).path (represent B)) k
          (NativeNormalizedBondTest.actualField T hG m period) -
        jet (fun B : fieldDir G (T.family.side m period) 1 =>
          loop (T.family.path.rep N period m).path (represent B)) k 0‖ +
      (layers.map fun a =>
        ‖jet (fun B : fieldDir G (T.family.side m period) 1 =>
            unmaskedPayload a.packet (represent B)) k
            (NativeNormalizedBondTest.actualField T hG m period) -
          jet (fun B : fieldDir G (T.family.side m period) 1 =>
            unmaskedPayload a.packet (represent B)) k 0‖).sum ≤
        C * (A.admittedCost m)^d := by
  choose loopBound loopPos loopEstimate using
    (fun j : Fin (n + 1) => NativeOriginalLoopBondJets.atRun G j.val)
  choose layerBound layerPos layerEstimate using
    (fun j : Fin (n + 1) => OriginalLayerBondJetBound.actual_layers_bound G rankCap j.val)
  let M : ℝ := ∑ j : Fin (n + 1), NativeOriginalMainBondPrice.coefficient G j.val
  let L : ℝ := ∑ j : Fin (n + 1), loopBound j
  let P : ℝ := ∑ j : Fin (n + 1), layerBound j
  have hM : 0 ≤ M :=
    Finset.sum_nonneg (fun j _ => (NativeOriginalMainBondPrice.coefficient_pos G j.val).le)
  have hL : 0 ≤ L := Finset.sum_nonneg (fun j _ => (loopPos j).le)
  have hP : 0 ≤ P := Finset.sum_nonneg (fun j _ => (layerPos j).le)
  have hm (j : Fin (n + 1)) : NativeOriginalMainBondPrice.coefficient G j.val ≤ M :=
    Finset.single_le_sum (fun i _ => (NativeOriginalMainBondPrice.coefficient_pos G i.val).le)
      (Finset.mem_univ j)
  have hl (j : Fin (n + 1)) : loopBound j ≤ L :=
    Finset.single_le_sum (fun i _ => (loopPos i).le) (Finset.mem_univ j)
  have hp (j : Fin (n + 1)) : layerBound j ≤ P :=
    Finset.single_le_sum (fun i _ => (layerPos i).le) (Finset.mem_univ j)
  let B : ℝ := 1 + M + L + K.polynomialConstant * P
  let D : ℕ := K.polynomialDegree + 7*n + 8
  have hB : 0 < B := by
    have hK := K.polynomial_constant_nonnegative
    dsimp only [B]
    positivity
  refine ⟨B * (2 : ℝ)^D, mul_pos hB (pow_pos (by norm_num) D), D, ?_⟩
  filter_upwards [ActualCoarseStagePrice.coarse_cost T hG hT A] with m hstage
  intro N period hmN layers point order H k hk
  let j : Fin (n + 1) := ⟨k, Nat.lt_succ_of_le hk⟩
  let W : ℝ := A.admittedCost m
  let X : ℝ := 1 + W
  let p := T.family.path.levels.params m
  have hW : 0 ≤ W := A.admitted_cost_nonnegative m
  have hW1 : 1 ≤ W := A.admitted_cost_ge_one m
  have hX1 : 1 ≤ X := by dsimp only [X]; linarith
  have hX : 0 ≤ X := zero_le_one.trans hX1
  have hWX : W ≤ X := by dsimp only [X]; linarith
  have hs : 1 + p.paths ≤ W ∧ 1 + p.width⁻¹ ≤ W :=
    stage_parts p hstage.2.1
  have hpath : 0 ≤ 1 + p.paths := by have h := p.paths_pos; linarith
  have hwidth : 0 ≤ 1 + p.width⁻¹ := by
    have h := inv_pos.mpr p.width_pos
    linarith
  have hdm : 2 + (2*k+6) ≤ D := by dsimp only [D]; omega
  have hdl : 1 + (k+6) ≤ D := by dsimp only [D]; omega
  have hdp : K.polynomialDegree + 7*k ≤ D := by dsimp only [D]; omega
  have hmainPrice :
      NativeOriginalMainBondPrice.coefficient G k * (1+p.paths)^2 *
        (1+p.width⁻¹)^(2*k+6) ≤ M * X^D := by
    exact (two_powers (NativeOriginalMainBondPrice.coefficient_pos G k).le
      (hm j) hpath hwidth (hs.1.trans hWX) (hs.2.trans hWX) 2 (2*k+6)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 hdm) hM)
  have hmain := (NativeOriginalMainBondPrice.atRun k T hG N period m hmN).trans hmainPrice
  have hloop0 := loop_cap_nonneg T.family.path.levels.clock m
  have hloopX : T.family.path.levels.clock.loopCap m ≤ X :=
    (loop_cap_le A m).trans hWX
  have hloopPrice :
      T.family.path.levels.clock.loopCap m * loopBound j *
        (1+p.width⁻¹)^(k+6) ≤ L * X^D := by
    calc
      _ = loopBound j * (T.family.path.levels.clock.loopCap m)^1 *
          (1+p.width⁻¹)^(k+6) := by ring
      _ ≤ L * X^(1+(k+6)) :=
        two_powers (loopPos j).le (hl j) hloop0 hwidth hloopX
          (hs.2.trans hWX) 1 (k+6)
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 hdl) hL
  have hloop := (loopEstimate j T hG N period m hmN).trans hloopPrice
  let Z : ℝ := 1 + (A.outputWidth m)⁻¹
  have hZ : 0 ≤ Z := by
    have h := inv_pos.mpr (A.output_width_pos m)
    dsimp only [Z]
    linarith
  have hZX : Z ≤ X := by
    exact add_le_add (le_refl 1) (output_inverse A m)
  have hfirst : K.geometry m * layerBound j ≤
      (K.polynomialConstant * X^K.polynomialDegree) * P :=
    mul_le_mul (K.polynomial_bound m) (hp j) (layerPos j).le
      (mul_nonneg K.polynomial_constant_nonnegative (pow_nonneg hX _))
  have hKP : 0 ≤ K.polynomialConstant * P :=
    mul_nonneg K.polynomial_constant_nonnegative hP
  have hlayerPrice : K.geometry m * layerBound j * Z^(7*k) ≤
      (K.polynomialConstant * P) * X^D := by
    calc
      _ ≤ ((K.polynomialConstant * X^K.polynomialDegree) * P) * X^(7*k) :=
        mul_le_mul hfirst (pow_le_pow_left₀ hZ hZX (7*k)) (pow_nonneg hZ _)
          (mul_nonneg
            (mul_nonneg K.polynomial_constant_nonnegative (pow_nonneg hX _)) hP)
      _ = (K.polynomialConstant * P) * X^(K.polynomialDegree + 7*k) := by
        rw [pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 hdp) hKP
  have hlayer := (layerEstimate j T hG m period H (A.output_width_pos m)).trans hlayerPrice
  have hsum := add_le_add (add_le_add hmain hloop) hlayer
  calc
    _ ≤ M * X^D + L * X^D + (K.polynomialConstant * P) * X^D := hsum
    _ = (M + L + K.polynomialConstant * P) * X^D := by ring
    _ ≤ B * X^D := mul_le_mul_of_nonneg_right
      (by dsimp only [B]; linarith) (pow_nonneg hX D)
    _ ≤ B * (2*W)^D := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hX (by dsimp only [X]; linarith) D) hB.le
    _ = (B * (2 : ℝ)^D) * W^D := by rw [mul_pow]; ring

end YM.Integration.ActualOriginalFieldCost
end
