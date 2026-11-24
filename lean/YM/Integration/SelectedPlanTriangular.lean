import YM.Integration.SelectedPlanClearedNumerator
import YM.Integration.NativeRestoredLayerJets

/-! Triangular extraction on the original selected Plan. The auxiliary prior
keeps the exact same layers and merely erases coefficients at and above e.
It is an algebraic comparison numerator, never a replacement selected model.
Every full nonlinear layer is retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SelectedPlanTriangular
open Function Filter Lattice Wilson RG Precision Exterior Marker
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric Comparison.RG02 Comparison.RG02.Assembly
open scoped Topology ContDiff Classical BigOperators

section Composition
variable {E F W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup W] [NormedSpace ℝ W]

private theorem postcompose {k : ℕ} {f g : E → F} {φ : F → W}
    (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0)
    (h0 : f 0 = g 0) (hφ : ContDiffAt ℝ ω φ (f 0))
    (h : GradeAt k (f - g)) : GradeAt k (φ ∘ f - φ ∘ g) := by
  have hφg : ContDiffAt ℝ ω φ (g 0) := h0 ▸ hφ
  have he (j : ℕ) (hj : j < k) :
      iteratedFDeriv ℝ j f 0 = iteratedFDeriv ℝ j g 0 := by
    have hz := h.vanish j hj
    rw [iteratedFDeriv_sub_apply (hf.of_le le_top) (hg.of_le le_top)] at hz
    exact sub_eq_zero.mp hz
  refine ⟨(hφ.comp 0 hf).sub (hφg.comp 0 hg), ?_⟩
  intro i hi
  rw [iteratedFDeriv_sub_apply ((hφ.comp 0 hf).of_le le_top)
      ((hφg.comp 0 hg).of_le le_top),
    iteratedFDeriv_comp hφ hf le_top,
    iteratedFDeriv_comp hφg hg le_top, h0]
  apply sub_eq_zero.mpr
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_congr rfl
  intro c _hc
  ext v
  simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply, ftaylorSeries]
  congr 1
  funext j
  rw [he (c.partSize j) ((c.partSize_le j).trans_lt hi)]
end Composition

variable {G : Gauge} {C : Family G} {N period order : ℕ}

/-- Exact same rows and alpha; only coefficients at and above e are erased. -/
def prior (P : Plan C N period order) (e : ℕ) : Plan C N period order where
  layers := P.layers
  orders := P.orders
  coefficient i j := if j < e then P.coefficient i j else 0
  alpha := P.alpha

private theorem poly_smooth (P : Plan C N period order) (m : ℕ) :
    ContDiff ℝ ω (P.poly m) := by
  unfold Plan.poly
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_id.pow j)

private theorem poly_tail_grade (P : Plan C N period order) (m e : ℕ) :
    GradeAt e (P.poly m - (prior P e).poly m) := by
  have heq : P.poly m - (prior P e).poly m =
      fun g => ∑ j ∈ Finset.range (order - 2 + 1),
        if e ≤ j then P.coefficient m j * g ^ j else 0 := by
    funext g
    simp only [Plan.poly, prior, Pi.sub_apply]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases h : j < e
    · simp [h, not_le.mpr h]
    · simp [h, Nat.le_of_not_gt h]
  rw [heq]
  apply GradeAt.list_sum
  intro j _hj
  by_cases h : e ≤ j
  · simp only [if_pos h]
    have hp := GradeAt.shifts (fun g : ℝ => g) contDiffAt_id rfl j
    have hc : GradeAt 0 (fun _ : ℝ => P.coefficient m j) :=
      GradeAt.unchecked contDiffAt_const
    have hh : GradeAt j (fun g : ℝ => P.coefficient m j * g ^ j) := by
      simpa only [Nat.zero_add, smul_eq_mul] using hc.scale hp
    exact hh.lower h
  · simp only [if_neg h]
    exact GradeAt.grade_zero e

private theorem prior_step (P : Plan C N period order) (m e : ℕ)
    (he : e ≤ order - 2) (g : ℝ) :
    (prior P (e + 1)).poly m g - (prior P e).poly m g =
      P.coefficient m e * g ^ e := by
  simp only [Plan.poly, prior]
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single e]
  · simp
  · intro j _hj hje
    have h : j < e + 1 ↔ j < e := by omega
    simp only [h, sub_self]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

private theorem poly_remainder_grade (P : Plan C N period order) (m e : ℕ)
    (he : e ≤ order - 2) :
    GradeAt (e + 1) (fun g => P.poly m g - (prior P e).poly m g -
      P.coefficient m e * g ^ e) := by
  have h := poly_tail_grade P m (e + 1)
  convert h using 1
  funext g
  have hs := prior_step P m e he g
  dsimp only [Pi.sub_apply]
  linarith

private def modifier (c : ℕ) (t : ℝ) : ℝ :=
  (1 + t) * ((Real.sqrt (1 + t))⁻¹) ^ c

private theorem modifier_smooth (c : ℕ) : ContDiffAt ℝ ω (modifier c) 0 := by
  have h : ContDiffAt ℝ ω (fun t : ℝ => 1 + t) 0 :=
    contDiffAt_const.add contDiffAt_id
  exact h.mul (((h.sqrt (by norm_num)).inv (by norm_num)).pow c)

private theorem sum_factor (a : ℝ) (l : List ℝ) :
    a * l.sum = (l.map (fun b => a * b)).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp only [List.sum_cons, List.map_cons, mul_add, ih]

private theorem list_difference_grade {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ι : Type*} (l : List ι) (f g : ι → E → ℝ) (k : ℕ)
    (h : ∀ a ∈ l, GradeAt k (f a - g a)) :
    GradeAt k (fun z => (l.map (fun a => f a z)).sum -
      (l.map (fun a => g a z)).sum) := by
  revert h
  induction l with
  | nil =>
    intro _h
    simpa only [List.map_nil, List.sum_nil, sub_self] using
      (GradeAt.grade_zero k : GradeAt k (fun _ : E => (0 : ℝ)))
  | cons a l ih =>
    intro h
    have hh := (h a (List.mem_cons_self ..)).add
      (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))
    convert hh using 1
    funext z
    simp only [List.map_cons, List.sum_cons, Pi.add_apply, Pi.sub_apply]
    ring

variable (T : Run G) (P : Plan T.family N period order) (m : ℕ)

private def layerPart (z : ℝ × fieldDir G (T.family.side m period) 1) : ℝ :=
  ActualAnalyticPlanVacuum.radicand T P m z.1 *
    ActualGradedVacuum.restored (P.layers m)
      (ActualAnalyticPlanVacuum.coupling T P m z.1) (represent z.2)

private def row (a : Piece G (T.family.side m period))
    (z : ℝ × fieldDir G (T.family.side m period) 1) : ℝ :=
  z.1 ^ (a.power + 2 - a.rank) *
    modifier (a.power + 2 - a.rank) (z.1 ^ 2 * P.poly m z.1) *
    unmaskedPayload a.packet (represent z.2)

private theorem layerPart_eq (z : ℝ × fieldDir G (T.family.side m period) 1) :
    layerPart T P m z = ((P.layers m).map (fun a => row T P m a z)).sum := by
  unfold layerPart ActualGradedVacuum.restored
  rw [sum_factor, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _ha
  simp only [Function.comp_def, row, modifier, ActualAnalyticPlanVacuum.coupling,
    ActualAnalyticPlanVacuum.radicand, div_eq_mul_inv, mul_pow]
  ring

variable {point : BudgetPoint} {rankCap : ℕ} {width budget : ℝ}
    (H : GradedVacuumLayers (P.layers m) point order rankCap width budget)

include H in
private theorem layer_contact (e : ℕ) (hw : 0 < width) :
    GradeAt (e + 7) (layerPart T P m - layerPart T (prior P e) m) := by
  let u : (ℝ × fieldDir G (T.family.side m period) 1) → ℝ :=
    fun z => z.1 ^ 2 * P.poly m z.1
  let v : (ℝ × fieldDir G (T.family.side m period) 1) → ℝ :=
    fun z => z.1 ^ 2 * (prior P e).poly m z.1
  have hu : ContDiffAt ℝ ω u 0 :=
    (contDiffAt_fst.pow 2).mul ((poly_smooth P m).contDiffAt.comp 0 contDiffAt_fst)
  have hv : ContDiffAt ℝ ω v 0 :=
    (contDiffAt_fst.pow 2).mul
      ((poly_smooth (prior P e) m).contDiffAt.comp 0 contDiffAt_fst)
  have huv : GradeAt (2 + e) (u - v) := by
    have hp := (poly_tail_grade P m e).coarse
      (g := fun z : ℝ × fieldDir G (T.family.side m period) 1 => z.1)
      contDiffAt_fst rfl
    have hg := GradeAt.shifts
      (fun z : ℝ × fieldDir G (T.family.side m period) 1 => z.1) contDiffAt_fst rfl 2
    convert hg.scale hp using 1
    funext z
    simp only [u, v, Function.comp_def, Pi.sub_apply, smul_eq_mul]
    ring
  have hrows (a : Piece G (T.family.side m period)) (ha : a ∈ P.layers m) :
      GradeAt (e + 7) (row T P m a - row T (prior P e) m a) := by
    have hmod := postcompose hu hv (by simp [u, v])
      (show ContDiffAt ℝ ω (modifier (a.power + 2 - a.rank)) (u 0) by
        simpa only [u, Prod.fst_zero, zero_pow (by decide : 2 ≠ 0), zero_mul] using
          modifier_smooth (a.power + 2 - a.rank)) huv
    have hg := GradeAt.shifts
      (fun z : ℝ × fieldDir G (T.family.side m period) 1 => z.1)
      contDiffAt_fst rfl (a.power + 2 - a.rank)
    have hp := (ActualGradedVacuum.payload_grade H hw a ha).coarse
      (g := fun z : ℝ × fieldDir G (T.family.side m period) 1 => z.2)
      contDiffAt_snd rfl
    have heq : (a.power + 2 - a.rank) + a.rank = a.power + 2 :=
      Nat.sub_add_cancel (H.leading_rank a ha)
    have hprod := hmod.scale (hg.scale hp)
    have horder : e + 7 ≤ (2 + e) + ((a.power + 2 - a.rank) + a.rank) := by
      have hlow := (H.orders a ha).1
      omega
    convert hprod.lower horder using 1
    funext z
    simp only [row, u, v, Function.comp_def, Pi.sub_apply, smul_eq_mul]
    ring
  have hs := list_difference_grade (P.layers m) (row T P m)
    (row T (prior P e) m) (e + 7) hrows
  convert hs using 1
  funext z
  simp only [Pi.sub_apply, layerPart_eq, prior]

private theorem path_bounds (hm : m ≤ N) :
    (T.family.path.rep N period m).path.Bounds
      (T.family.path.levels.params m).clip (T.family.path.levels.params m).width
      (T.family.path.levels.params m).paths (T.family.path.levels.clock.loopCap m) := by
  have h : T.family.path.Conv N period m := T.makes.wilson.represents N period m hm
  rw [← h.clip]
  exact h.good.paths

def kinetic (B : fieldDir G (T.family.side m period) 1) : ℝ :=
  mainTerm (T.family.path.levels.params m).clip
    (T.family.path.rep N period m).path (represent B)

private theorem main_grade (hm : m ≤ N) : GradeAt 2 (kinetic (N := N) (period := period) T m) := by
  have hW := path_bounds (period := period) T m hm
  change GradeAt 2 (Extra.Iteration.Calibration.main
    (T.family.path.rep N period m).path (T.family.path.levels.params m).clip)
  refine ⟨Extra.Iteration.Calibration.main_jet hW, ?_⟩
  intro i hi
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · ext v
    simpa only [iteratedFDeriv_zero_apply, _root_.zero_apply] using
      (Bulk.main_origin (m := T.family.side m period)
        (T.family.path.levels.params m).clip (T.family.path.rep N period m).path hW)
  · ext v
    simp only [iteratedFDeriv_one_apply, Bulk.main_first _ _ hW,
      _root_.zero_apply]

include H in
/-- All terms above the single next coefficient vanish past the extraction
order. The full nonlinear same-list response starts three orders later. -/
theorem contact (e : ℕ) (he : e ≤ order - 2) (hm : m ≤ N) (hw : 0 < width) :
    GradeAt (e + 5) (fun z : ℝ × fieldDir G (T.family.side m period) 1 =>
      SelectedPlanClearedNumerator.numerator T P m z -
        SelectedPlanClearedNumerator.numerator T (prior P e) m z -
        ((P.coefficient m e * z.1 ^ (e + 2) *
          kinetic (N := N) (period := period) T m z.2 : ℝ) : ℂ)) := by
  have hp := (poly_remainder_grade P m e he).coarse
    (g := fun z : ℝ × fieldDir G (T.family.side m period) 1 => z.1)
    contDiffAt_fst rfl
  have hg := GradeAt.shifts
    (fun z : ℝ × fieldDir G (T.family.side m period) 1 => z.1) contDiffAt_fst rfl 2
  have hb := (main_grade (N := N) (period := period) T m hm).coarse
    (g := fun z : ℝ × fieldDir G (T.family.side m period) 1 => z.2)
    contDiffAt_snd rfl
  have hkin : GradeAt (e + 5) (fun z : ℝ × fieldDir G (T.family.side m period) 1 =>
      z.1 ^ 2 * (P.poly m z.1 - (prior P e).poly m z.1 -
        P.coefficient m e * z.1 ^ e) * kinetic (N := N) (period := period) T m z.2) := by
    simpa only [Function.comp_def, smul_eq_mul, show 2 + (e + 1) + 2 = e + 5 by omega]
      using (hg.scale hp).scale hb
  have hl := (layer_contact T P m H e hw).lower (show e + 5 ≤ e + 7 by omega)
  have h := GradeAt.linear_contact Complex.ofRealCLM (hkin.add hl)
  convert h using 1
  funext z
  simp only [SelectedPlanClearedNumerator.numerator, ActualAnalyticPlanVacuum.vacuum,
    ActualAnalyticPlanVacuum.kinetic, layerPart, kinetic, Function.comp_def,
    Pi.add_apply, Pi.sub_apply, Complex.ofRealCLM_apply, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_mul, pow_add]
  ring

private theorem jet_sub {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f g : E → W}
    (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) (n : ℕ) (x : E) :
    jet (f - g) n x = jet f n x - jet g n x := by
  simp only [jet, iteratedFDeriv_sub_apply (hf.of_le le_top) (hg.of_le le_top),
    _root_.sub_apply, smul_sub]

include H in
/-- The next coefficient multiplies the original kinetic quadratic exactly.
The comparison Plan has the same layers and only earlier coefficients. -/
theorem coefficient (e : ℕ) (he : e ≤ order - 2) (hm : m ≤ N) (hw : 0 < width)
    (B : fieldDir G (T.family.side m period) 1) :
    jet (SelectedPlanClearedNumerator.numerator T P m) (e + 4) (1, B) -
      jet (SelectedPlanClearedNumerator.numerator T (prior P e) m) (e + 4) (1, B) =
      ((P.coefficient m e * jet (kinetic (N := N) (period := period) T m) 2 B : ℝ) : ℂ) := by
  let f : (ℝ × fieldDir G (T.family.side m period) 1) → ℝ :=
    fun z => z.1 ^ (e + 2) * kinetic (N := N) (period := period) T m z.2
  let L : ℝ →L[ℝ] ℂ := P.coefficient m e • Complex.ofRealCLM
  have hk := (main_grade (N := N) (period := period) T m hm).coarse
    (g := fun z : ℝ × fieldDir G (T.family.side m period) 1 => z.2)
    contDiffAt_snd rfl
  have hf : ContDiffAt ℝ ω f 0 := (contDiffAt_fst.pow _).mul
    hk.smooth
  have hL : ContDiffAt ℝ ω (L ∘ f) 0 := L.contDiff.contDiffAt.comp 0 hf
  have hP := (SelectedPlanClearedNumerator.numerator_grade T P m H hm hw).smooth
  have hQ := (SelectedPlanClearedNumerator.numerator_grade T (prior P e) m H hm hw).smooth
  have hz := (contact T P m H e he hm hw).jet_z (1, B) (by omega : e + 4 < e + 5)
  have hlead : (fun z : ℝ × fieldDir G (T.family.side m period) 1 =>
      ((P.coefficient m e * z.1 ^ (e + 2) *
        kinetic (N := N) (period := period) T m z.2 : ℝ) : ℂ)) = L ∘ f := by
    funext z
    simp only [L, f, Function.comp_def, _root_.smul_apply,
      Complex.ofRealCLM_apply, Complex.real_smul, ← Complex.ofReal_mul, mul_assoc]
  have hfun : (fun z : ℝ × fieldDir G (T.family.side m period) 1 =>
      SelectedPlanClearedNumerator.numerator T P m z -
        SelectedPlanClearedNumerator.numerator T (prior P e) m z -
        ((P.coefficient m e * z.1 ^ (e + 2) *
          kinetic (N := N) (period := period) T m z.2 : ℝ) : ℂ)) =
      (SelectedPlanClearedNumerator.numerator T P m -
        SelectedPlanClearedNumerator.numerator T (prior P e) m) - L ∘ f := by
    funext z
    exact congrArg (fun a : ℂ => SelectedPlanClearedNumerator.numerator T P m z -
      SelectedPlanClearedNumerator.numerator T (prior P e) m z - a) (congrFun hlead z)
  have hjet := congrArg (fun h : (ℝ × fieldDir G (T.family.side m period) 1) → ℂ =>
    jet h (e + 4) (1, B)) hfun
  have hz' := hjet.symm.trans hz
  have hsub := jet_sub (hP.sub hQ) hL (e + 4) (1, B)
  have hsub' := jet_sub hP hQ (e + 4) (1, B)
  have hs := hsub.trans (congrArg
    (fun z : ℂ => z - jet (L ∘ f) (e + 4) (1, B)) hsub')
  have ht := sub_eq_zero.mp (hs.symm.trans hz')
  have ht' := ht.trans (jet_apply_left L f (e + 4) (hf.of_le le_top) (1, B)).symm
  have hpow := NativeRestoredLayerJets.power_jet
    (kinetic (N := N) (period := period) T m)
    (main_grade (N := N) (period := period) T m hm).smooth (e + 2) (e + 4) 1 B
  have hn : e + 4 - (e + 2) = 2 := by omega
  simp only [if_pos (show e + 2 ≤ e + 4 by omega), hn, one_pow, one_mul] at hpow
  change jet f (e + 4) (1, B) = _ at hpow
  have ht'' := ht'.trans (congrArg L hpow)
  simpa only [L, _root_.smul_apply, Complex.ofRealCLM_apply,
    Complex.real_smul, ← Complex.ofReal_mul] using ht''

end YM.Integration.SelectedPlanTriangular
end
