import YM.Integration.SelectedPlanPriorJetBound
import YM.Integration.ScalarJetCauchy
import YM.Integration.MonomialListMixedMarginal

/-! The complete auxiliary prior numerator, on the original Plan's rows.
Only earlier coefficients are kept by prior. Every nonlinear field factor is
retained, and the finite Cauchy estimate sums the original list occurrences.
This is an intermediate estimate; the actual field bills are supplied separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedPlanPriorNumerator
open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison.Global FullQLocal Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology ContDiff Classical BigOperators

inductive Term (G : Gauge) (s : Side) where
  | main
  | loop
  | layer (a : Piece G s)

def rows {G : Gauge} {s : Side} (l : List (Piece G s)) : List (Term G s) :=
  Term.main :: Term.loop :: l.map Term.layer

def field {G : Gauge} (T : Run G) {N period : ℕ} (m : ℕ) :
    Term G (T.family.side m period) → fieldDir G (T.family.side m period) 1 → ℝ
  | .main => fun B => mainTerm (T.family.path.levels.params m).clip
      (T.family.path.rep N period m).path (represent B)
  | .loop => fun B => Precision.loop (T.family.path.rep N period m).path (represent B)
  | .layer a => fun B => unmaskedPayload a.packet (represent B)

def scalar {G : Gauge} (T : Run G) {N period r : ℕ}
    (P : Plan T.family N period r) (m e : ℕ) :
    Term G (T.family.side m period) → ℝ → ℝ
  | .main => ActualAnalyticPlanVacuum.radicand T (SelectedPlanTriangular.prior P e) m
  | .loop => fun g => g ^ 2
  | .layer a => fun g =>
      ActualAnalyticPlanVacuum.radicand T (SelectedPlanTriangular.prior P e) m g *
        ActualAnalyticPlanVacuum.coupling T (SelectedPlanTriangular.prior P e) m g ^
          (a.power + 2 - a.rank)

def realNumerator {G : Gauge} (T : Run G) {N period r : ℕ}
    (P : Plan T.family N period r) (m e : ℕ)
    (z : ℝ × fieldDir G (T.family.side m period) 1) : ℝ :=
  ((rows (P.layers m)).map fun a =>
    scalar T P m e a z.1 * field (N := N) T m a z.2).sum

def modifierCost {G : Gauge} {C : Family G} {N period r : ℕ}
    (P : Plan C N period r) (m e : ℕ) : ℝ :=
  SelectedPlanPriorJetBound.constant r *
    (1 + ∑ j ∈ (Finset.range (r - 2 + 1)).filter (fun j => j < e),
      |P.coefficient m j|) ^ (r + 4)

private theorem list_mul {ι : Type*} (l : List ι) (c : ℝ) (f : ι → ℝ) :
    (l.map fun a => c * f a).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, mul_add]

/-- The exact full prior numerator, including its kinetic and loop terms. -/
theorem numerator_eq {G : Gauge} (T : Run G) {N period r : ℕ}
    (P : Plan T.family N period r) (m e : ℕ)
    (z : ℝ × fieldDir G (T.family.side m period) 1) :
    SelectedPlanClearedNumerator.numerator T (SelectedPlanTriangular.prior P e) m z =
      (realNumerator T P m e z : ℂ) := by
  let Q := SelectedPlanTriangular.prior P e
  let a := ActualAnalyticPlanVacuum.radicand T Q m z.1
  let g := ActualAnalyticPlanVacuum.coupling T Q m z.1
  have hs : (P.layers m |>.map fun b =>
      (a * g ^ (b.power + 2 - b.rank)) * unmaskedPayload b.packet (represent z.2)).sum =
      a * (P.layers m |>.map fun b =>
        g ^ (b.power + 2 - b.rank) * unmaskedPayload b.packet (represent z.2)).sum := by
    simpa only [mul_assoc] using list_mul (P.layers m) a
      (fun b => g ^ (b.power + 2 - b.rank) * unmaskedPayload b.packet (represent z.2))
  simp only [SelectedPlanClearedNumerator.numerator, ActualAnalyticPlanVacuum.vacuum,
    ActualAnalyticPlanVacuum.kinetic, ActualGradedVacuum.restored,
    SelectedPlanTriangular.prior, realNumerator, rows, List.map_cons, List.sum_cons,
    List.map_map, Function.comp_def, scalar, field]
  apply congrArg Complex.ofReal
  change _ = a * _ + (z.1 ^ 2 * _ + ((P.layers m).map fun b =>
    (a * g ^ (b.power + 2 - b.rank)) * unmaskedPayload b.packet (represent z.2)).sum)
  rw [hs]
  dsimp only [a, g, Q, SelectedPlanTriangular.prior, ActualAnalyticPlanVacuum.radicand]
  ring

private theorem poly_smooth {G : Gauge} {C : Family G} {N period r : ℕ}
    (P : Plan C N period r) (m : ℕ) : ContDiff ℝ ω (P.poly m) := by
  unfold Plan.poly
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_id.pow j)

private theorem scalar_smooth {G : Gauge} (T : Run G) {N period r : ℕ}
    (P : Plan T.family N period r) (m e : ℕ)
    (a : Term G (T.family.side m period)) : ContDiffAt ℝ ω (scalar T P m e a) 0 := by
  have hr : ContDiffAt ℝ ω
      (ActualAnalyticPlanVacuum.radicand T (SelectedPlanTriangular.prior P e) m) 0 :=
    contDiffAt_const.add ((contDiffAt_id.pow 2).mul
      (poly_smooth (SelectedPlanTriangular.prior P e) m).contDiffAt)
  cases a with
  | main => exact hr
  | loop => exact contDiffAt_id.pow 2
  | layer a =>
    exact hr.mul ((ActualAnalyticPlanVacuum.coupling_analytic T
        (SelectedPlanTriangular.prior P e) m).pow _)

private theorem cost_nonneg {G : Gauge} {C : Family G} {N period r : ℕ}
    (P : Plan C N period r) (m e : ℕ) : 0 ≤ modifierCost P m e := by
  have h := (SelectedPlanPriorJetBound.constant_pos r).le
  unfold modifierCost
  positivity

private theorem scalar_bound {G : Gauge} (T : Run G) {N period r : ℕ}
    (P : Plan T.family N period r) (m e n : ℕ)
    {point : BudgetPoint} {rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers (P.layers m) point r rankCap width budget)
    (hn : n ≤ r + 4) (a : Term G (T.family.side m period))
    (ha : a ∈ rows (P.layers m)) (c : ℕ) (hc : c ≤ n) :
    ‖jet (scalar T P m e a) c 1‖ ≤ (n + 1 : ℝ) * (1 + modifierCost P m e) := by
  have hb := cost_nonneg P m e
  have hnb : modifierCost P m e ≤ (n + 1 : ℝ) * (1 + modifierCost P m e) := by
    nlinarith [(show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n),
      mul_nonneg ((show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)) hb]
  have hn1 : (1 : ℝ) ≤ (n + 1 : ℝ) * (1 + modifierCost P m e) := by
    nlinarith [(show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n),
      mul_nonneg ((show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)) hb]
  cases a with
  | main =>
      have h := SelectedPlanPriorJetBound.prior_bound P m e 0 c (by omega) (hc.trans hn)
      have hh : ‖jet (scalar T P m e Term.main) c 1‖ ≤ modifierCost P m e := by
        change ‖jet (fun g : ℝ => 1 + g ^ 2 * (SelectedPlanTriangular.prior P e).poly m g) c 1‖ ≤ _
        simpa only [pow_zero, mul_one,
          Real.norm_eq_abs, modifierCost] using h
      exact hh.trans hnb
  | loop =>
      have h := MonomialListMixedMarginal.monomial_jet_le c 2
      exact (show ‖jet (scalar T P m e Term.loop) c 1‖ ≤ 1 by
        simpa only [scalar, Real.norm_eq_abs] using h).trans hn1
  | layer a =>
      have ha' : a ∈ P.layers m := by simpa [rows] using ha
      let q := a.power + 2 - a.rank
      have hq : q ≤ r + 2 := by
        have hp := (H.orders a ha').2
        dsimp only [q]
        omega
      let f : ℝ → ℝ := fun g =>
        (1 + g ^ 2 * (SelectedPlanTriangular.prior P e).poly m g) *
          ((Real.sqrt (1 + g ^ 2 *
            (SelectedPlanTriangular.prior P e).poly m g))⁻¹) ^ q
      have hr : ContDiffAt ℝ ω
          (fun g : ℝ => 1 + g ^ 2 * (SelectedPlanTriangular.prior P e).poly m g) 0 :=
        contDiffAt_const.add ((contDiffAt_id.pow 2).mul
          (poly_smooth (SelectedPlanTriangular.prior P e) m).contDiffAt)
      have hf : ContDiffAt ℝ ω f 0 :=
        hr.mul (((hr.sqrt (by simp)).inv (by simp)).pow q)
      have heq : scalar T P m e (.layer a) = fun g => g ^ q * f g := by
        funext g
        simp only [scalar, ActualAnalyticPlanVacuum.radicand,
          ActualAnalyticPlanVacuum.coupling, div_eq_mul_inv, mul_pow, f, q]
        ring
      rw [heq]
      have hh := ScalarJetCauchy.scalar_product_bound (fun g : ℝ => g ^ q) f
        (contDiffAt_id.pow q) hf c 1 (modifierCost P m e) zero_le_one hb
        (fun k _ => by simpa only [Real.norm_eq_abs] using
          MonomialListMixedMarginal.monomial_jet_le k q)
        (fun k hk => by simpa only [f, modifierCost, Real.norm_eq_abs] using
          SelectedPlanPriorJetBound.prior_bound P m e q k hq ((hk.trans hc).trans hn))
      have hcn : (c + 1 : ℝ) ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.add_le_add_right hc 1
      have hmul := mul_le_mul_of_nonneg_right hcn hb
      exact hh.trans (by nlinarith [(show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)])

private theorem path_bounds {G : Gauge} (T : Run G) {N period : ℕ}
    (m : ℕ) (hm : m ≤ N) :
    (T.family.path.rep N period m).path.Bounds
      (T.family.path.levels.params m).clip (T.family.path.levels.params m).width
      (T.family.path.levels.params m).paths (T.family.path.levels.clock.loopCap m) := by
  have h : T.family.path.Conv N period m := T.makes.wilson.represents N period m hm
  rw [← h.clip]
  exact h.good.paths

private theorem fields_smooth {G : Gauge} (T : Run G) {N period r : ℕ}
    (P : Plan T.family N period r) (m : ℕ)
    {point : BudgetPoint} {rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers (P.layers m) point r rankCap width budget)
    (hm : m ≤ N) (hw : 0 < width) (a : Term G (T.family.side m period))
    (ha : a ∈ rows (P.layers m)) : ContDiffAt ℝ ω (field (N := N) T m a) 0 := by
  cases a with
  | main =>
    exact Extra.Iteration.Calibration.main_jet (path_bounds (period := period) T m hm)
  | loop => exact Bulk.loop_smooth _ _ (path_bounds (period := period) T m hm)
  | layer a =>
      exact (ActualGradedVacuum.payload_grade H hw a (by simpa [rows] using ha)).smooth

private theorem list_smooth {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l : List ι) (f : ι → E → ℝ)
    (h : ∀ a ∈ l, ContDiffAt ℝ ω (f a) 0) :
    ContDiffAt ℝ ω (fun z => (l.map fun a => f a z).sum) 0 := by
  revert h
  induction l with
  | nil => intro _; exact contDiffAt_const
  | cons a l ih =>
      intro h
      exact (h a (List.mem_cons_self ..)).add
        (ih (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- A complete prior numerator estimate from the sum of its original field bills.
The field bill is a genuine intermediate inlet, supplied by the actual one-bond
main/loop/layer estimates. No coefficient-size premise is added here. -/
theorem prior_bound {G : Gauge} (T : Run G) {N period r : ℕ}
    (P : Plan T.family N period r) (m e n : ℕ)
    {point : BudgetPoint} {rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers (P.layers m) point r rankCap width budget)
    (hm : m ≤ N) (hw : 0 < width) (hn : n ≤ r + 4)
    (B : fieldDir G (T.family.side m period) 1) (F : ℝ) (hF : 0 ≤ F)
    (hfields : ∀ k ≤ n,
      ‖jet (field (N := N) T m Term.main) k B - jet (field (N := N) (period := period) T m Term.main) k 0‖ +
      ‖jet (field (N := N) T m Term.loop) k B - jet (field (N := N) (period := period) T m Term.loop) k 0‖ +
      ((P.layers m).map fun a =>
        ‖jet (fun U => unmaskedPayload a.packet (represent U)) k B -
          jet (fun U => unmaskedPayload a.packet (represent U)) k 0‖).sum ≤ F) :
    ‖jet (SelectedPlanClearedNumerator.numerator T (SelectedPlanTriangular.prior P e) m)
        n (1, B) -
      jet (SelectedPlanClearedNumerator.numerator T (SelectedPlanTriangular.prior P e) m)
        n (1, 0)‖ ≤
      (n + 1 : ℝ) ^ 2 * (1 + modifierCost P m e) * F := by
  let l := rows (P.layers m)
  let h := scalar T P m e
  let f := field (N := N) (period := period) T m
  have hh : ∀ a ∈ l, ContDiffAt ℝ ω (h a) 0 := fun a _ => scalar_smooth T P m e a
  have hf : ∀ a ∈ l, ContDiffAt ℝ ω (f a) 0 :=
    fun a ha => fields_smooth T P m H hm hw a ha
  have hcost : 0 ≤ (n + 1 : ℝ) * (1 + modifierCost P m e) := by
    have hp := cost_nonneg P m e
    positivity
  have hb := NormalizedJetCauchy.list_centered_product_bound l h f hh hf n B
    ((n + 1 : ℝ) * (1 + modifierCost P m e)) F hcost hF
    (fun a ha c hc => scalar_bound T P m e n H hn a ha c hc)
    (fun k hk => by
      simpa only [l, rows, List.map_cons, List.sum_cons, List.map_map,
        Function.comp_def, f, field, add_assoc] using hfields k hk)
  have hs : ContDiffAt ℝ ω (realNumerator T P m e) 0 := by
    exact list_smooth l (fun a (z : ℝ × fieldDir G (T.family.side m period) 1) =>
      h a z.1 * f a z.2)
      (fun a ha => ((hh a ha).comp (0 : ℝ × _) contDiffAt_fst).mul
        ((hf a ha).comp (0 : ℝ × _) contDiffAt_snd))
  have heq : SelectedPlanClearedNumerator.numerator T (SelectedPlanTriangular.prior P e) m =
      Complex.ofRealCLM ∘ realNumerator T P m e := funext (numerator_eq T P m e)
  have hj (U : fieldDir G (T.family.side m period) 1) :
      jet (SelectedPlanClearedNumerator.numerator T (SelectedPlanTriangular.prior P e) m)
        n (1, U) = Complex.ofReal (jet (realNumerator T P m e) n ((1 : ℝ), U)) := by
    rw [heq]
    exact (jet_apply_left Complex.ofRealCLM _ n (hs.of_le le_top) (1, U)).symm
  rw [hj B, hj 0, ← Complex.ofReal_sub, Complex.norm_real]
  have hb' : ‖jet (realNumerator T P m e) n (1, B) -
      jet (realNumerator T P m e) n (1, 0)‖ ≤
      (n + 1 : ℝ) ^ 2 * (1 + modifierCost P m e) * F := by
    change ‖jet (realNumerator T P m e) n (1, B) -
        jet (realNumerator T P m e) n (1, 0)‖ ≤
        (n + 1 : ℝ) * ((n + 1 : ℝ) * (1 + modifierCost P m e)) * F at hb
    simpa only [pow_two, mul_assoc] using hb
  simpa only [Real.norm_eq_abs] using hb'

end YM.Integration.SelectedPlanPriorNumerator
end
