import YM.RG.Bounded
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite probability tilts and local replacement

Preparations for a comparison of **actual** Wilson conditional integrals with flat-saddle
perturbation theory. Everything here is real; e.g., the density `f` might include *all*
rare events, even events on which it is not continuous. The Envelope hypotheses in
these comparison lemmas are used only at fixed parameters and finite volume, to manipulate
finite integrals.

The replacement lemma is set up to avoid using any **volume** lower estimate on the physical
vacuum denominator. It keeps both the cost of the collar in the Haar prior and the exponent
loss in the pointwise density comparison (which can include a *field-dependent* boundary cost,
inside `W`).
-/

set_option autoImplicit false
noncomputable section
namespace YM.MatchingLedger

open Set Filter Function RG MeasureTheory
open scoped Topology BigOperators

section bounded

variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace E] [Norm E]

lemma envelope_comp {f : X → E} {g : Y → X} (hf : Envelope f) (hg : Measurable g) :
    Envelope (fun y => f (g y)) := by
  obtain ⟨C,H⟩ := hf.cost
  exact ⟨hf.meas.comp hg,C,fun y => H (g y)⟩

lemma envelope_sub {f g : X → ℝ} (hf : Envelope f) (hg : Envelope g) :
    Envelope (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

end bounded

section tilt
variable {V : Type*} [MeasurableSpace V] (μ : Measure V) [IsProbabilityMeasure μ]

/-- Use on bounded measurable densities and insertions (at one finite regulator).
Positive normalized to probability, not connected! -/
def weigh (f W : V → ℝ) : ℝ := (∫ x, W x * f x ∂μ) / (∫ x, f x ∂μ)

/-- A basic license to use `weigh` in this ledger. -/
structure Weight (f : V → ℝ) : Prop extends Envelope f where
  positive : ∀ x, 0 ≤ f x
  nonempty : 0 < ∫ x, f x ∂μ

omit [IsProbabilityMeasure μ] in
lemma weigh_self_unit {f : V → ℝ} (hf : Weight μ f) : weigh μ f (fun _ => 1) = 1 := by
  simp only [weigh, one_mul, div_self hf.nonempty.ne']

omit [IsProbabilityMeasure μ] in
lemma weigh_const_mul {f W : V → ℝ} (a : ℝ) : weigh μ f (fun x => a * W x)= a * weigh μ f W := by
  simp_rw [weigh, mul_assoc, integral_const_mul, mul_div_assoc]

variable {μ}

omit [IsProbabilityMeasure μ] in
lemma weigh_const {f : V → ℝ} (hf : Weight μ f) (a : ℝ) : weigh μ f (fun _ => a)=a := by
  rw [weigh, integral_const_mul, mul_div_assoc, div_self hf.nonempty.ne', mul_one]

lemma weight_of_pos {f : V → ℝ} (hf : Envelope f) (hp : ∀ x, 0 < f x) : Weight μ f := by
  refine ⟨hf, fun x => (hp x).le, (integral_pos_iff_support_of_nonneg (fun i => (hp i).le) (hf.integrable μ)).mpr ?_⟩
  · have hs : Function.support f=univ := Set.eq_univ_of_forall fun x => (hp x).ne'
    rw [hs,measure_univ]; exact zero_lt_one

lemma weigh_add {f x y : V → ℝ} (hf : Envelope f) (hx : Envelope x) (hy : Envelope y) :
    weigh μ f (fun v => x v + y v)= weigh μ f x + weigh μ f y := by
  simp_rw [weigh, add_mul]
  rw [integral_add ((hx.mul hf).integrable _) ((hy.mul hf).integrable _), add_div]

lemma weigh_mono {f x y : V → ℝ} (hf : Weight μ f) (hx : Envelope x) (hy : Envelope y)
    (h : ∀ v, x v ≤ y v) : weigh μ f x ≤ weigh μ f y :=
  div_le_div_of_nonneg_right (integral_mono ((hx.mul hf.toEnvelope).integrable _)
    ((hy.mul hf.toEnvelope).integrable _) (fun v => mul_le_mul_of_nonneg_right (h v) (hf.positive v))) hf.nonempty.le

lemma weigh_exp_pos {f x : V → ℝ} (hf : Weight μ f) (hx : Envelope x) :
    0 < weigh μ f (fun v => Real.exp (x v)) := by
  obtain ⟨C,hC⟩ := hx.cost
  apply lt_of_lt_of_le (Real.exp_pos (-C))
  rw [← weigh_const hf (Real.exp (-C))]
  exact weigh_mono hf (Envelope.const _) hx.exp fun v => Real.exp_monotone
    (neg_le.mp ((neg_le_abs (x v)).trans (hC v)))

variable (μ)

/-- Log partition pressure *difference* for a tilt by `W`. -/
def pressureBill (f W : V → ℝ) := Real.log (weigh μ f (fun x => Real.exp (W x)))

variable {μ}

lemma pressure_affine {f X : V → ℝ} (hf : Weight μ f) (hX : Envelope X) (s : ℝ) :
    pressureBill μ f (fun x => X x + s) = pressureBill μ f X + s := by
  simp_rw [pressureBill, add_comm (X _), Real.exp_add, weigh_const_mul]
  rw [Real.log_mul (Real.exp_pos _).ne' (weigh_exp_pos hf hX).ne', Real.log_exp, add_comm]

lemma pressure_mono {f X Y : V → ℝ} (hf : Weight μ f) (hX : Envelope X) (hY : Envelope Y)
    (h : ∀ v, X v ≤ Y v) : pressureBill μ f X ≤ pressureBill μ f Y :=
  Real.log_le_log (weigh_exp_pos hf hX)
    (weigh_mono hf hX.exp hY.exp fun v => Real.exp_monotone (h v))

omit [IsProbabilityMeasure μ] in
lemma pressure_const {f : V → ℝ} (hf : Weight μ f) (s : ℝ) :
    pressureBill μ f (fun _ => s) = s := by rw [pressureBill, weigh_const hf, Real.log_exp]

private lemma weigh_shift {f X : V → ℝ} (hf : Weight μ f) (hX : Envelope X) :
    weigh μ f (fun v => Real.exp (X v-pressureBill μ f X)) = 1 := by
  unfold pressureBill; simp_rw [Real.exp_sub,div_eq_inv_mul]; rw [weigh_const_mul,
    Real.exp_log (weigh_exp_pos hf hX), inv_mul_cancel₀ (weigh_exp_pos hf hX).ne']

/-- Keep a convex combination of **log** bills, even at probability tilts. -/
lemma pressure_blend {f X Y : V → ℝ} (hf : Weight μ f) (hX : Envelope X) (hY : Envelope Y)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : p+q=1) :
    pressureBill μ f (fun v => p * X v + q * Y v) ≤ p * pressureBill μ f X + q * pressureBill μ f Y := by
  let A := pressureBill μ f X; let B := pressureBill μ f Y
  let X' v := X v - A; let Y' v := Y v - B
  let m := p*A + q*B; let W v := p*X' v+q*Y' v
  have hx : Envelope X' := envelope_sub hX (Envelope.const A)
  have hy : Envelope Y' := envelope_sub hY (Envelope.const B)
  have hw : Envelope W := ((Envelope.const _).mul hx).add ((Envelope.const _).mul hy)
  have hz (v : V) : Real.exp (W v) ≤ p * Real.exp (X' v)+q * Real.exp (Y' v) :=
    convexOn_exp.2 (Set.mem_univ (X' v)) (Set.mem_univ (Y' v)) hp hq hs
  have he := weigh_mono hf hw.exp (((Envelope.const _).mul hx.exp).add ((Envelope.const _).mul hy.exp)) hz
  rw [weigh_add hf.toEnvelope ((Envelope.const _).mul hx.exp) ((Envelope.const _).mul hy.exp),
    weigh_const_mul, weigh_const_mul, show weigh μ f (fun v => Real.exp (X' v))=1 from weigh_shift hf hX,
    show weigh μ f (fun v => Real.exp (Y' v))=1 from weigh_shift hf hY, mul_one, mul_one, hs] at he
  rw [show (fun v => p * X v+q*Y v)=(fun v => W v + m) by funext v; unfold W X' Y' m; ring,
    pressure_affine hf hw]
  exact add_le_of_nonpos_left (Real.log_nonpos (weigh_exp_pos hf hw).le he)

end tilt

section erase
variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (s : Finset ι)

local notation "A" => { i // i ∈ s }
local notation "B" => { i // i ∉ s }
local notation "ν" => Measure.pi (fun _ : ι => μ)
local notation "ν₁" => Measure.pi (fun _ : A => μ)
local notation "ν₂" => Measure.pi (fun _ : B => μ)

def joinWindow := (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => X) (·∈s)).symm

omit [Fintype ι] in
lemma join_off {s : Finset ι} (a : {i // i∈s} → X) (b : {i // i∉s} → X) {i : ι} (hi : i∉s) :
    joinWindow s (a,b) i=b ⟨i,hi⟩ := by
  change (Equiv.piEquivPiSubtypeProd (·∈s) (fun _=>X)).symm (a,b) i = _
  simp [Equiv.piEquivPiSubtypeProd_symm_apply, hi]

omit [Fintype ι] in
lemma join_on {s : Finset ι} (a : {i // i∈s} → X) (b : {i // i∉s} → X) {i : ι} (hi : i∈s) :
    joinWindow s (a,b) i=a ⟨i,hi⟩ := by
  change (Equiv.piEquivPiSubtypeProd (·∈s) (fun _=>X)).symm (a,b) i = _
  simp [Equiv.piEquivPiSubtypeProd_symm_apply, hi]

lemma joinWindow_pay : MeasurePreserving (joinWindow s) ((ν₁).prod ν₂) ν := by
  unfold joinWindow
  convert! (measurePreserving_piEquivPiSubtypeProd (fun _ : ι=>μ) (·∈s)).symm

/-- In analogy to resampling in House (`YM.OPE.Therm.Press`). Used with Haar on the
*forest slice*; not an assertion about the dependence/support of a resampled density. -/
lemma integrate_window {f : (ι → X) → ℝ} (hf : Envelope f) :
    (∫ x, f x ∂ν) = ∫ y, (∫ x, f (joinWindow s (x,y)) ∂ν₁) ∂ν₂ := by
  rw [← (joinWindow_pay μ s).integral_comp (joinWindow (X:=X) s).measurableEmbedding]
  exact integral_prod_symm _ ((envelope_comp hf (joinWindow (X:=X) s).measurable).integrable _)

-- avoiding measure conditionals (a ratio per exterior), proving a pressure difference
set_option maxHeartbeats 400000 in
theorem erase_budget {Y : Set X} (hY : MeasurableSet Y)
    {f W : (ι → X) → ℝ} (hf : Weight ν f) (hW : Envelope W) (c d : ℝ)
    (hy : Real.exp (-d) ≤ (μ.real Y)^s.card)
    (h : ∀ x y, (∀ i, i ∉ s → x i = y i) → (∀ i ∈ s, y i ∈ Y) →
      Real.exp (W x) * f x ≤ Real.exp c * f y) : pressureBill ν f W ≤ c + d := by
  let u := joinWindow (X:=X) s
  let P := (ν₁).prod ν₂
  let Z : Set (A → X) := Set.pi univ (fun _ => Y)
  have hm : MeasurableSet Z := MeasurableSet.univ_pi (fun _ => hY)
  have hz : (ν₁).real Z = (μ.real Y)^s.card := by
    unfold Measure.real Z; rw [Measure.pi_pi]; simp
  let L x := Real.exp (W x)* f x
  let M x := Real.exp (c+d) * f x
  have hL : Envelope L := hW.exp.mul hf.toEnvelope; have hM : Envelope M :=
    (Envelope.const _).mul hf.toEnvelope
  have hi (x y) : Real.exp (-d) * L (u (x,y)) ≤ ∫ z, Real.exp c * f (u (z,y)) ∂ν₁ := by
    let E(z) := Real.exp c * f (u (z,y)); let q := L (u (x,y))
    have hE : Envelope E := (Envelope.const _).mul (envelope_comp hf.toEnvelope
      (u.measurable.comp (measurable_id.prodMk measurable_const)))
    have hp z : 0 ≤ E z := mul_nonneg (Real.exp_pos _).le (hf.positive _)
    have hq : 0 ≤ q := mul_nonneg (Real.exp_pos _).le (hf.positive _)
    calc
      _ ≤ (ν₁).real Z * q := mul_le_mul_of_nonneg_right (hz.symm ▸ hy) hq
      _ = ∫ _ in Z, q ∂ν₁ := (setIntegral_const ..).symm
      _ ≤ ∫ z in Z, E z ∂ν₁ := setIntegral_mono_on (integrable_const q|>.integrableOn) (hE.integrable _).integrableOn hm
            fun z hv => h (u (x,y)) (u (z,y)) (fun i hi => (join_off x y hi).trans (join_off z y hi).symm)
              (fun i hi => by unfold u; rw [join_on z y hi]; exact hv _ (Set.mem_univ _))
      _ ≤ _ := setIntegral_le_integral (hE.integrable _) (Eventually.of_forall hp)
  have hv (y : B → X) : (∫ x, L (u (x,y)) ∂ν₁) ≤ ∫ x, M (u (x,y)) ∂ν₁ := by
    have hh (x : A → X) := hi x y
    refine (mul_le_mul_iff_right₀ (Real.exp_pos (-d))).mp (le_trans (b:=∫ _ : A → X, (∫ z, Real.exp c * f (u (z,y)) ∂ν₁) ∂ν₁) ?_ ?_)
    · rw [← integral_const_mul]; exact integral_mono ((envelope_comp hL (u.measurable.comp
        (measurable_id.prodMk measurable_const))).integrable _ |>.const_mul _) (integrable_const _) (fun x=> hh x)
    apply le_of_eq; rw [integral_const]; simp only [probReal_univ, one_smul]; unfold M; rw [integral_const_mul, integral_const_mul, ← mul_assoc,← Real.exp_add,show -d+(c+d)=c by ring]
  have he : (∫ x, L x ∂ν) ≤ ∫ x, M x ∂ν := by
    rw [integrate_window μ s hL, integrate_window μ s hM]; apply integral_mono _ _ hv
    · exact ((envelope_comp hL u.measurable).integrable P).integral_prod_right
    · exact ((envelope_comp hM u.measurable).integrable P).integral_prod_right
  unfold M at he; rw [integral_const_mul] at he
  exact Real.log_exp (c+d) ▸ (Real.log_le_log (weigh_exp_pos hf hW) ((div_le_iff₀ hf.nonempty).mpr he))

end erase
end YM.MatchingLedger
