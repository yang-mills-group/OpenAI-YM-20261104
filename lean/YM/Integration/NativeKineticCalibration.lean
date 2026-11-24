import YM.Integration.NativeCappedKineticQuotes
import YM.Integration.LocalComparisonCalibrationClass
import YM.AnalyticBridge.COUPLING_SHAPE_ESTIMATE.Local

/-! The original clipped kinetic action as a nonzero calibration. The original
low rows and masked cubic/quartic rows are retained. The scalar defect is not
identified with zero, and its eventual smallness is not assumed by this file. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.NativeKineticCalibration
open WilsonStartup
open Function Set Lattice Wilson RG MeasureTheory
open AnalyticBridge VerifiedReset Collection Averaging Extra.Iteration Next.Scheduling
open FullQLocal
open scoped BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side}

abbrev Index (n : Side) := (Seat n × Low) ⊕ (Seat n × High)

def address (R : PathData G) (p : BudgetPoint) : Index n → RegularAddress n :=
  Sum.elim (Quotes.lowEntry G R p) (Quotes.highEntry G R)

def original (R : PathData G) (c : Clip) (p : BudgetPoint) : Index n → Pot G n :=
  Sum.elim (fun i U => i.2.live R c p 0 (i.1.view U))
    (fun i U => summit R p i.2 0 (i.1.view U))

def germ (R : PathData G) (c : Clip) : Index n → Pot G n :=
  Sum.elim (fun i U => i.2.mark R c * i.2.plain R 0 (i.1.view U))
    (fun i U => i.2.plain R 0 (i.1.view U))

def regularCharge (R : PathData G) (c : Clip) (p : BudgetPoint) : Index n → ℝ :=
  Sum.elim (fun i => Collection.turnFee p *
      (p.threshold ^ 2 * (|i.2.mark R c| * lowCost G p (i.2.length R))))
    (fun i => Collection.turnFee p * (i.2.price R p * p.threshold ^ 3))

def fullCharge (R : PathData G) (c : Clip) : Index n → ℝ :=
  Sum.elim (fun i => 4 * (Real.exp ((i.2.length R : ℝ) / c.relaxation) *
      |i.2.mark R c|)) (fun i => 16 * i.2.charge R)

def regularCost (G : Gauge) (c : Clip) (p : BudgetPoint) (σ C : ℝ) : ℝ :=
  (Collection.turnFee p * p.threshold ^ 2) * CappedRegularReset.lowBase G c p σ C +
  (Collection.turnFee p * p.threshold ^ 3) * CappedRegularReset.highBase G p σ C

def fullCost (c : Clip) (p : BudgetPoint) (σ C : ℝ) : ℝ :=
  4 * NativeCappedKineticQuotes.lowHitCost p c σ C +
  16 * NativeCappedKineticQuotes.highHitCost p σ C

def unitCost (G : Gauge) (c : Clip) (p : BudgetPoint) (σ C : ℝ) : ℝ :=
  regularCost G c p σ C + fullCost c p σ C

def price (G : Gauge) (c : Clip) (p : BudgetPoint) (σ C δ : ℝ) : ℝ :=
  |δ * VerifiedReset.factor| * unitCost G c p σ C

variable (R : PathData G) (c : Clip) (p : BudgetPoint)

private lemma low_regular (hd : Decent c p) (d : Low) :
    p.Regular (d.home R p (0 : Site n))
      (fun U => d.mark R c * d.plain R 0 U) := by
  have hr := VerifiedReset.reg_bill (d.plain_bill R c (0 : Site n) hd)
    (d.plain_cont R 0).measurable (d.plain_local R p hd.radius 0)
    (d.plain_gauge R 0)
  exact CouplingShape.reg_scale (d.mark R c) hr

private lemma low_bill (hd : Decent c p) (d : Low) :
    Bill p (0 : Site n) (Healthy p.threshold (d.home R p 0))
      (p.threshold ^ 2 * (|d.mark R c| * lowCost G p (d.length R)))
      (fun U => d.mark R c * d.plain R 0 U) := by
  refine Bill.le (Bill.mul_left (d.mark R c) (d.plain_bill R c 0 hd)) ?_
  have hc : faceCost G p + rowCost G p (d.length R) ≤ lowCost G p (d.length R) := by
    unfold lowCost
    exact le_add_of_nonneg_left
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹) (pair_nonneg G p))
  calc
    _ ≤ |d.mark R c| * (lowCost G p (d.length R) * p.threshold ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hc (sq_nonneg p.threshold)) (abs_nonneg _)
    _ = _ := by ring

private lemma low_plain_bound (d : Low) (o : Site n) (U : Config G n) :
    ‖d.plain R o U‖ ≤ 4 := by
  cases hd : d.2 with
  | inl j =>
    have hb := G.price_range (faceValue U (o, d.1))
    simpa only [Low.plain, hd, Sum.elim_inl, Real.norm_of_nonneg hb.1]
      using hb.2.trans (by norm_num : (2 : ℝ) ≤ 4)
  | inr j =>
    have hl : ‖(d.left R j).atSite U o‖ ≤ 2 := Slot.eval_norm ..
    have hr : ‖(d.right R j).atSite U o‖ ≤ 2 := Slot.eval_norm ..
    have hi := abs_real_inner_le_norm ((d.left R j).atSite U o)
      ((d.right R j).atSite U o)
    have hm := mul_le_mul hl hr (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    simp only [Low.plain, hd, Sum.elim_inr, Real.norm_eq_abs, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

private lemma high_bound (d : High) (o : Site n) (U : Config G n) :
    ‖d.plain R o U‖ ≤ 16 * d.charge R := by
  have hm : 0 ≤ d.charge R := by unfold High.charge Atom.magnitude; positivity
  have hk : (2 : ℝ) ^ d.arity ≤ 16 := by
    rcases d.significant with h | h <;> rw [h] <;> norm_num
  exact (show ‖d.plain R o U‖ ≤ d.charge R * 2 ^ d.arity from
    (d.term R).unmasked_bound U o).trans
    ((mul_le_mul_of_nonneg_left hk hm).trans_eq (mul_comm _ _))

private lemma full_nonnegative (i : Index n) : 0 ≤ fullCharge R c i := by
  cases i with
  | inl i =>
    change 0 ≤ 4 * (Real.exp ((i.2.length R : ℝ) / c.relaxation) * |i.2.mark R c|)
    positivity
  | inr i =>
    change 0 ≤ 16 * i.2.charge R
    unfold High.charge Atom.magnitude
    positivity

private lemma original_bound (i : Index n) (U : Config G n) :
    ‖original R c p i U‖ ≤ fullCharge R c i := by
  cases i with
  | inl i =>
    refine (i.2.shapeBound R c 0 (i.1.view U)).trans ?_
    change |i.2.mark R c| *
      (2 * p.threshold * Real.exp ((i.2.length R : ℝ) / c.relaxation)) ≤ _
    have he := (Real.exp_pos ((i.2.length R : ℝ) / c.relaxation)).le
    have ht : 2 * p.threshold ≤ 4 := by linarith [p.threshold_le]
    calc
      _ ≤ |i.2.mark R c| *
          (4 * Real.exp ((i.2.length R : ℝ) / c.relaxation)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht he) (abs_nonneg _)
      _ = _ := by
        change |i.2.mark R c| * (4 * Real.exp ((i.2.length R : ℝ) / c.relaxation)) =
          4 * (Real.exp ((i.2.length R : ℝ) / c.relaxation) * |i.2.mark R c|)
        ring
  | inr i =>
    change ‖summit R p i.2 0 (i.1.view U)‖ ≤ 16 * i.2.charge R
    by_cases hh : Healthy p.threshold (i.2.home R 0) (i.1.view U)
    · rw [summit, masked_eq _ _ _ _ hh]
      exact high_bound R i.2 0 _
    rw [summit, masked_ne _ _ _ _ hh, norm_zero]
    exact full_nonnegative R c (.inr i)

private lemma germ_bound (i : Index n) (U : Config G n) :
    ‖germ R c i U‖ ≤ fullCharge R c i := by
  cases i with
  | inl i =>
    have he : 1 ≤ Real.exp ((i.2.length R : ℝ) / c.relaxation) :=
      Real.one_le_exp (div_nonneg (Nat.cast_nonneg _) c.radius_pos.le)
    change ‖i.2.mark R c * i.2.plain R 0 (i.1.view U)‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs]
    calc
      _ ≤ |i.2.mark R c| * 4 :=
        mul_le_mul_of_nonneg_left (low_plain_bound R i.2 0 _) (abs_nonneg _)
      _ = 4 * (1 * |i.2.mark R c|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right he (abs_nonneg _)) (by norm_num : (0 : ℝ) ≤ 4)
  | inr i => exact high_bound R i.2 0 _

variable {R c p} {σ C Λ : ℝ}

private lemma rows_regular (h : R.Bounds c σ C Λ) (hd : Decent c p)
    (i : Index n) : p.Regular (address R p i).support (germ R c i) := by
  cases i with
  | inl i => exact i.1.regular (low_regular R c p hd i.2)
  | inr i =>
    exact i.1.regular
      (Extra.Iteration.Derivs.canonical_regular (i.2.term R) 0 p
        (i.2.invariant R h))

private lemma rows_bound (h : R.Bounds c σ C Λ) (hd : Decent c p)
    (i : Index n) :
    p.supBounds (address R p i).site (address R p i).support
      (germ R c i) (regularCharge R c p i) := by
  cases i with
  | inl i =>
    exact i.1.sup (low_regular R c p hd i.2)
      (Bill.sup (low_bill R c p hd i.2) (fun _ hh => hh))
  | inr i =>
    exact i.1.sup
      (Extra.Iteration.Derivs.canonical_regular (i.2.term R) 0 p
        (i.2.invariant R h))
      (Bill.sup (i.2.paid R 0 p) (fun _ hh => hh))

private lemma rows_measurable (i : Index n) :
    Measurable (original R c p i) := by
  cases i with
  | inl i => exact (i.2.live_meas R c p 0).comp (continuous_pull ..).measurable
  | inr i =>
    exact (masked_measurable p.threshold (i.2.home R (0 : Site n))
      (i.2.plain R (0 : Site n)) ((i.2.term R).unmasked_cont (0 : Site n)).measurable).comp
        (continuous_pull ..).measurable

private lemma rows_gauge (h : R.Bounds c σ C Λ) (i : Index n) :
    GaugeInvariant (original R c p i) := by
  cases i with
  | inl i => exact Push.Local.invariant_pull (i.2.live_gauge R c 0) _ _
  | inr i =>
    exact Push.Local.invariant_pull
      (CouplingShape.stencil_gi
        (Extra.Iteration.Derivs.canonical_regular (i.2.term R) 0 p
          (i.2.invariant R h)).symmetry p.threshold (i.2.home R 0)) _ _

private lemma rows_reads (hd : Decent c p)
    (i : Index n) : UsesFinal p.threshold (address R p i).support
      (original R c p i) := by
  cases i with
  | inl i =>
    exact Push.Local.uses_pull
      (fun U V ha _ => i.2.live_local R c hd 0 U V ha) _ _
  | inr i =>
    exact Push.Local.uses_pull
      (CouplingShape.stencil_reads (i.2.home R 0)
        (Extra.Iteration.Derivs.atom_local (i.2.term R) 0) p.threshold) _ _

private lemma rows_healthy (hd : Decent c p) (i : Index n) (U : Config G n)
    (hh : Healthy p.threshold (address R p i).support U) :
    original R c p i U = germ R c i U := by
  cases i with
  | inl i => exact i.2.live_plain R c hd 0 ((i.1.healthy ..).mp hh)
  | inr i => exact masked_eq _ _ _ _ ((i.1.healthy ..).mp hh)

private lemma regular_total (h : R.Bounds c σ C Λ) (hw : Geo.Width p c σ)
    (x : Site n) : SumBudget
    (fun i : Index n => if (address R p i).site = x then
      p.mass (address R p i).support (regularCharge R c p i) else 0)
    (regularCost G c p σ C) := by
  obtain ⟨hl, hh⟩ := NativeCappedKineticQuotes.regular_rows (n := n) h hw
  have ht := Collection.turnFee_pos p
  have hp := p.threshold_pos
  have hL := Quotes.anchored_scale
    (r := Collection.turnFee p * p.threshold ^ 2) (by positivity) hl x
  have hH := Quotes.anchored_scale
    (r := Collection.turnFee p * p.threshold ^ 3) (by positivity) hh x
  apply Cost.sum
  · simpa only [address, regularCharge, Sum.elim_inl, mul_assoc] using hL
  simpa only [address, regularCharge, Sum.elim_inr, mul_assoc, mul_left_comm,
    mul_comm] using hH

private lemma hit_mass {ι : Type*} {X : ι → Support n} {b : ι → ℝ} {A : ℝ}
    (hb : ∀ i, 0 ≤ b i) (h : Ac.Hit X p.B b (p.supportExponent + 1) A)
    (x : Site n) :
    SumBudget (fun i => if x ∈ X i then p.mass (X i) (b i) else 0) A := by
  apply Cost.mono (h x)
  · intro i
    split <;> first | exact le_rfl | exact mul_nonneg (Real.exp_pos _).le (hb i)
  intro i
  by_cases hi : x ∈ X i
  · simp only [if_pos hi, BudgetPoint.mass]
    calc
      _ ≤ Real.exp ((p.supportExponent + 1) * coverNumber p.B (X i)) * b i :=
        mul_le_mul_of_nonneg_right (Real.exp_monotone
          (by nlinarith [Nat.cast_nonneg (α := ℝ) (coverNumber p.B (X i))])) (hb i)
      _ = _ := mul_comm _ _
  simp only [if_neg hi, le_refl]

private lemma full_total (h : R.Bounds c σ C Λ) (hw : Geo.Width p c σ)
    (x : Site n) : SumBudget
    (fun i : Index n => if x ∈ (address R p i).support then
      p.mass (address R p i).support (fullCharge R c i) else 0)
    (fullCost c p σ C) := by
  obtain ⟨hl, hh⟩ := NativeCappedKineticQuotes.full_hits (n := n) h hw
  have hL := hit_mass (p := p) (fun i => full_nonnegative R c (.inl i))
    (Quotes.hit_scale (r := 4) (by norm_num) hl) x
  have hH := hit_mass (p := p) (fun i => full_nonnegative R c (.inr i))
    (Quotes.hit_scale (r := 16) (by norm_num) hh) x
  exact Cost.sum hL hH

private lemma costs_nonnegative (h : R.Bounds c σ C Λ) (hw : Geo.Width p c σ) :
    0 ≤ regularCost G c p σ C ∧ 0 ≤ fullCost c p σ C :=
  ⟨Cost.nonneg (regular_total (n := (1 : Side)) h hw 0),
    Cost.nonneg (full_total (n := (1 : Side)) h hw 0)⟩

private def unitPresentation (h : R.Bounds c σ C Λ) (hd : Decent c p)
    (hw : Geo.Width p c σ) (Q : Rep G n) (hq : p.threshold = Q.p.threshold) :
    CalibrationPresentation Q p (unitCost G c p σ C) where
  threshold := hq
  size_nonnegative := add_nonneg (costs_nonnegative h hw).1 (costs_nonnegative h hw).2
  address := fun i => address R p (numbering (Index n) i)
  original := fun i => original R c p (numbering (Index n) i)
  germ := fun i => germ R c (numbering (Index n) i)
  regular := fun i => rows_regular h hd (numbering (Index n) i)
  original_measurable := fun i => rows_measurable (numbering (Index n) i)
  original_gauge := fun i => rows_gauge h (numbering (Index n) i)
  original_reads := fun i => hq ▸ rows_reads hd (numbering (Index n) i)
  on_healthy := fun i U hh => rows_healthy hd (numbering (Index n) i) U (hq.symm ▸ hh)
  regularMajorant := fun i => regularCharge R c p (numbering (Index n) i)
  fullMajorant := fun i => fullCharge R c (numbering (Index n) i)
  regular_bound := fun i => rows_bound h hd (numbering (Index n) i)
  full_nonnegative := fun i => full_nonnegative R c (numbering (Index n) i)
  original_bound := fun i U => original_bound R c p (numbering (Index n) i) U
  germ_bound := fun i U => germ_bound R c (numbering (Index n) i) U
  regular_total := fun x => Cost.equiv (numbering (Index n))
    (Cost.enlarge (regular_total h hw x) (le_add_of_nonneg_right (costs_nonnegative h hw).2))
  full_hit := fun x => Cost.equiv (numbering (Index n))
    (Cost.enlarge (full_total h hw x) (le_add_of_nonneg_left (costs_nonnegative h hw).1))

private def scalePresentation {Q : Rep G n} {p : BudgetPoint} {A : ℝ}
    (K : CalibrationPresentation Q p A) (d : ℝ) :
    CalibrationPresentation Q p (|d| * A) where
  threshold := K.threshold
  size_nonnegative := mul_nonneg (abs_nonneg _) K.size_nonnegative
  address := K.address
  original := fun i U => d * K.original i U
  germ := fun i U => d * K.germ i U
  regular := fun i => CouplingShape.reg_scale d (K.regular i)
  original_measurable := fun i => measurable_const.mul (K.original_measurable i)
  original_gauge := fun i a U => congrArg (d * ·) (K.original_gauge i a U)
  original_reads := fun i U V ha hf => congrArg (d * ·) (K.original_reads i U V ha hf)
  on_healthy := fun i U hh => congrArg (d * ·) (K.on_healthy i U hh)
  regularMajorant := fun i => |d| * K.regularMajorant i
  fullMajorant := fun i => |d| * K.fullMajorant i
  regular_bound := fun i => CouplingShape.sup_scale d (K.regular_bound i)
  full_nonnegative := fun i => mul_nonneg (abs_nonneg _) (K.full_nonnegative i)
  original_bound := fun i U => by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (K.original_bound i U) (abs_nonneg _)
  germ_bound := fun i U => by
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (K.germ_bound i U) (abs_nonneg _)
  regular_total := fun x => by
    simpa [BudgetPoint.mass, mul_ite, mul_left_comm |d|] using
      Cost.scale (K.regular_total x) |d| (abs_nonneg _)
  full_hit := fun x => by
    simpa [BudgetPoint.mass, mul_ite, mul_left_comm |d|] using
      Cost.scale (K.full_hit x) |d| (abs_nonneg _)

/-- A complete nonzero calibration for any literal scalar kinetic defect. -/
def calibration (h : R.Bounds c σ C Λ) (hd : Decent c p) (hw : Geo.Width p c σ)
    (Q : Rep G n) (hq : p.threshold = Q.p.threshold) (δ : ℝ) :
    CalibrationPresentation Q p (price G c p σ C δ) :=
  scalePresentation (unitPresentation h hd hw Q hq) (δ * VerifiedReset.factor)

/-- Every original clip/mask contribution survives in the exact full action. -/
theorem amount (h : R.Bounds c σ C Λ) (hd : Decent c p) (hw : Geo.Width p c σ)
    (Q : Rep G n) (hq : p.threshold = Q.p.threshold) (δ : ℝ) (U : Config G n) :
    (calibration h hd hw Q hq δ).amount U =
      δ * Push.BetaTransport.kinetic R c p U := by
  let K := unitPresentation h hd hw Q hq
  have hb : Summable K.fullMajorant :=
    Activities.summable_charge (fun i => ⟨_, (K.address i).anchor⟩)
      K.full_nonnegative K.full_hit
  have hs : Summable (fun i => K.original i U) :=
    (show Dominated K.original from ⟨_, hb, K.original_bound⟩).summable U
  have hi : Summable (fun i : Index n => original R c p i U) :=
    (numbering (Index n)).summable_iff.mp hs
  have hl := hi.comp_injective Sum.inl_injective
  have hh := hi.comp_injective Sum.inr_injective
  have he : VerifiedReset.factor * K.amount U = Push.BetaTransport.kinetic R c p U := by
    change VerifiedReset.factor *
      (∑' i, original R c p (numbering (Index n) i) U) = _
    rw [(numbering (Index n)).tsum_eq (fun i : Index n => original R c p i U),
      Summable.tsum_sum (f := fun i : Index n => original R c p i U) hl hh,
      Summable.tsum_prod (f := fun i : Seat n × Low => original R c p (Sum.inl i) U) hl,
      Summable.tsum_prod (f := fun i : Seat n × High => original R c p (Sum.inr i) U) hh,
      tsum_fintype, tsum_fintype]
    calc
      _ = VerifiedReset.layer (fun i : Low => i.live R c p (0 : Site n)) U +
          VerifiedReset.layer (fun i : High => summit R p i 0) U := by
        simp only [VerifiedReset.layer, original, Sum.elim_inl, Sum.elim_inr]
        ring
      _ = _ := VerifiedReset.true_base h hw U
  change (∑' i, (δ * VerifiedReset.factor) * K.original i U) = _
  rw [tsum_mul_left]
  calc
    _ = δ * (VerifiedReset.factor * K.amount U) := mul_assoc _ _ _
    _ = _ := congrArg (δ * ·) he

/-- A proved scalar defect estimate transfers to the displayed local/full-hit
price. The original geometry remains explicit, and no smallness is inferred. -/
theorem price_le (h : R.Bounds c σ C Λ) (hw : Geo.Width p c σ)
    {δ D : ℝ} (hd : |δ| ≤ D) :
    price G c p σ C δ ≤ D * unitCost G c p σ C := by
  have hu : 0 ≤ unitCost G c p σ C :=
    add_nonneg (costs_nonnegative h hw).1 (costs_nonnegative h hw).2
  have hf := VerifiedReset.factor_pos
  have hδ : |δ * VerifiedReset.factor| ≤ |δ| := by
    rw [abs_mul, abs_of_pos hf]
    exact mul_le_of_le_one_right (abs_nonneg _) VerifiedReset.factor_le
  exact mul_le_mul_of_nonneg_right (hδ.trans hd) hu

end YM.Integration.NativeKineticCalibration
end
