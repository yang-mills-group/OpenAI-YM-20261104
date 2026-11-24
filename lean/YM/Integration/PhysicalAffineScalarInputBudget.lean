import YM.Integration.PhysicalAffineScalarRetainedSource
import YM.Integration.PhysicalAffineScalarOrdinaryColumns

/-! Both genuinely discarded physical factors of the stationary square are
paid at a common exponential rate. Each field occurrence retains the root
of the particular real source or either of the real Jacobian endpoints. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.PhysicalAffineScalarInputBudget
open Function Filter Matrix Lattice Wilson RG RG.Shoot Precision Exterior Tree
open Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD
open PhysicalAffineScalarCutWeights PhysicalAffineScalarCutResidual
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}
abbrev Term (G : Gauge) (S : StepData c f) := Rows.Receipt G S ⊕ (Rows.Receipt G S×raw G f)

def input (T : Tube G S) (x : ℝ) (k : S.Choices) (z : Term G S) (B : Vec G c 1) :=
  z.elim (sourceTail T x B) fun p => columnTail T x k B p.1 p.2

def sourceWeight (S : StepData c f) (d : ℝ) (i : Rows.Receipt G S) (l : List (raw G c)) :=
  Real.exp (d*Stars.rays (native c) (PhysicalAffineScalarComparison.rowRoot S i) (hearth∘l.get))

def endpoints (S : StepData c f) (t : ℝ) (n : ℕ) (i : Rows.Receipt G S) (j : raw G f) (l : List (raw G c)) :=
  let o := PhysicalAffineScalarComparison.rowRoot S i
  let h := home S j
  let W := (native c).weight (wider t n)
  let M := marks G c (tier t n)
  max (M.pay l o*W o h) (M.pay l h*W h o)

def cap (S : StepData c f) (a t d M : ℝ) (n : ℕ) (z : Term G S) (l : List (raw G c)) :=
  z.elim (fun i => |slip| * M/sourceWeight S d i l)
    (fun p => |slip| * phasePrice G S.patch S.kernel n a t/endpoints S t n p.1 p.2 l)

private theorem horizon {u v : ℝ} (h : u≤v) (r : ℕ) : Real.exp (-v*r)≤Real.exp (-u*r) := by
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_right h (Nat.cast_nonneg r : 0≤(r:ℝ))]

private theorem remove_weight {w a C t s : ℝ} (hw : 0<w) (hc : 0≤C) (h : w*a≤C*t) (hs : t ≤ s) : a ≤ s *(C/w) := by
  calc a ≤ (C*s)/w := (le_div_iff₀ hw).mpr ((mul_comm a w).le.trans (h.trans (mul_le_mul_of_nonneg_left hs hc)))
    _=s*(C/w) := by ring

private theorem two_ended_price {u v u' v' z a b e : ℝ}
    (h₁ : u * (v * z) ≤ a * (e * b)) (h₂ : u' * (v' * z) ≤ a * (e * b)) :
    max (u * v) (u' * v') * z ≤ (a * b) * e := by
  have price_change : a * (e * b) = (a * b) * e := by ring
  rcases le_total (u * v) (u' * v') with h | h
  · rw [max_eq_right h, mul_assoc, ← price_change]
    exact h₂
  · rw [max_eq_left h, mul_assoc, ← price_change]
    exact h₁

/-- Common cutoff price from the native signed source and row estimates.
There is no abstract paid-tail or source-regularity input in this theorem. -/
theorem bought (G : Gauge) (P : Teller G) (L : Side) (n : ℕ) :
    ∃ d M : ℝ, 0<d ∧ 0<M ∧ 0<ConditionalAffineSourcePrices.rate P L ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), P.Funds S T → S.patch.L=L → ∀ (_F : Forest S.ratio)
    (x : ℝ), 0 < temp x → ∀ (k : S.Choices) (a t : ℝ), 0 < t → 0 ≤ a → Sheet T.up t a →
    1<c.val → S.patch.Branches S.kernel G → ∀ z : Term G S,
    ContDiffAt ℝ n (input T x k z) 0 ∧ ∀ l : List (raw G c), l.length≤n →
      |jet (ray G c) (input T x k z) l 0|≤Real.exp (-min (ConditionalAffineSourcePrices.rate P L) (t/4)*(till x:ℝ))*
        cap S a t d M n z l := by
  obtain ⟨d,M,hd,hM,hρ,h⟩ := PhysicalAffineScalarInputPrices.source G P L n
  refine ⟨d,M,hd,hM,hρ,?_⟩
  intro c f S T hP hL F x hx k a t ht ha hW hc hp z
  let κ := min (ConditionalAffineSourcePrices.rate P L) (t/4)
  have source_decay := horizon
    (min_le_left (ConditionalAffineSourcePrices.rate P L) (t / 4)) (till x)
  have column_decay := horizon
    (min_le_right (ConditionalAffineSourcePrices.rate P L) (t / 4)) (till x)
  cases z with
  | inl i =>
    have hs := h S T hP hL F x hx i
    refine ⟨hs.1,fun l hl => ?_⟩
    apply remove_weight (w:=sourceWeight S d i l) (C:=|slip| * M) (t:=Real.exp (-ConditionalAffineSourcePrices.rate P L*(till x:ℝ)))
      (Real.exp_pos _) (mul_nonneg (abs_nonneg _) hM.le)
    · exact hs.2 l.length hl l.get
    · exact source_decay
  | inr p =>
    let C := |slip| * phasePrice G S.patch S.kernel n a t
    have hC := mul_nonneg (abs_nonneg slip) (phase_nn G S.patch S.kernel (k:=n) ht ha)
    have hJ (q : Admit) := PhysicalAffineScalarOrdinaryColumns.smooth T k q hp hc ht ha hW n p.1 p.2
    refine ⟨(hJ _).sub (hJ _),fun l hl => ?_⟩
    let o := PhysicalAffineScalarComparison.rowRoot S p.1
    let y := home S p.2
    let R := marks G c (tier t n)
    let W := (native c).weight (wider t n)
    let w₁ := R.pay l o*W o y
    let w₂ := R.pay l y*W y o
    have hw : 0<endpoints S t n p.1 p.2 l := (mul_pos (R.pay_pos ..) (Cost.weight_pos ..)).trans_le (le_max_left ..)
    have hh := PhysicalAffineScalarInputPrices.columns T x k p.1 p.2 n hc ht ha hW (ordering ht n).1.le le_rfl l hl
    apply remove_weight (w:=endpoints S t n p.1 p.2 l) (C:=C) (t:=Real.exp (-(t/4)*(till x:ℝ))) hw hC
    · change max w₁ w₂ * |jet (ray G c) (fun B => columnTail T x k B p.1 p.2) l 0| ≤ C*_
      exact two_ended_price (u := R.pay l o) (v := W o y) (u' := R.pay l y) (v' := W y o)
        (a := |slip|) (b := phasePrice G S.patch S.kernel n a t)
        (e := Real.exp (-(t/4)*(till x:ℝ))) hh.1 hh.2
    · exact column_decay

end YM.Integration.PhysicalAffineScalarInputBudget
