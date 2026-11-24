import YM.Integration.WilsonInvariantActionPriorHearing

/-! The signed density insertion at an actual registered grade-four pair. A
distinguished hard occurrence keeps every genuine compatible partner. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonInvariantActionRegisteredHearing
open Function Filter Set Finset MeasureTheory Lattice Wilson RG RG.Shoot OPE.Therm
open PhysicalNext.Repeat.Legato WilsonInvariantActionPriorHearing
open WilsonInvariantActionRegisteredReturn WilsonInheritedRegisteredField
open scoped Classical BigOperators Topology

variable {G:Gauge} (R:Run G) {N p m:ℕ}
local notation "fine" => Config G (R.family.side (m+1) p)
local notation "coarse" => Config G (R.family.side m p)
local notation "Ω" => (coarse×fine)
local notation "P" => R.family.path.rep N p (m+1)
local notation "P₀" => R.family.path.rep N p m

def filed (live:m<N) (birth:R.family.ref 4 ≤ m+1) (v:R.family.label 4)
    (o:Site (R.family.side (m+1) p)) (η:ℂ→L[ℝ]ℝ):readings Ω:=by
  let f:=regular (C:=R.family) R.makes live v o
  have ef:Envelope f:=(source R live birth v o).1
  refine ⟨fun z=>η (f z.2),⟨η.continuous.measurable.comp (ef.meas.comp measurable_snd),
    ‖η‖*ef.cost.choose,?_⟩⟩
  exact fun z=>(η.le_opNorm (f z.2)).trans
    (mul_le_mul_of_nonneg_left (ef.cost.choose_spec z.2) (norm_nonneg _))

def score (interior:m+1<N) (δ:readings Ω):readings Ω:=by
  have eP:Envelope ((P).eval):=(P).envelope (R.makes.wilson.represents N p (m+1) interior.le).good
  refine ⟨fun z=>δ.val z/(P).eval z.2,?_⟩
  obtain ⟨a,ha,bound⟩:=SelectedCofactorLocalProjection.floor (C:=R.family) (p:=p) R.makes interior
  refine ⟨δ.property.meas.div (eP.meas.comp measurable_snd),δ.property.cost.choose/a,?_⟩
  intro z
  rw [norm_div,Real.norm_of_nonneg (ha.le.trans (bound z.2))]
  exact (div_le_div_of_nonneg_left (norm_nonneg _) ha (bound z.2)).trans
    (div_le_div_of_nonneg_right (δ.property.cost.choose_spec z) ha.le)

theorem under_kernel (interior:m+1<N) (δ:readings Ω) (V:coarse) (U:fine):
    actualConditionalDensity R.family N p m V U*(score R interior δ).val (V,U)=
    (R.family.path.levels.clock.op m p).density (R.family.path.β N p (m+1)) U V*δ.val (V,U)/(P₀).eval V:=by
  have pos : (P).eval U ≠ 0 := (Multi.AxisShift.chosen_positive R.makes.wilson (p:=p) interior.le U).ne'
  let b:=(R.family.path.levels.clock.op m p).density (R.family.path.β N p (m+1)) U V
  change (b*(P).eval U/(P₀).eval V)*(δ.val (V,U)/(P).eval U)=b*δ.val (V,U)/(P₀).eval V
  calc
    _=(b*δ.val (V,U)/(P₀).eval V)*((P).eval U*((P).eval U)⁻¹):=by ring
    _=b*δ.val (V,U)/(P₀).eval V:=by rw [mul_inv_cancel₀ pos,mul_one]

def receipts (live:m<N) (f h w:readings Ω):ℝ:=
  let I:=conditional R live
  let E:=earlier R (p:=p) live
  covariance E (I w) (covariance I f h) + cubic E (I w) (I f) (I h) + E (cubic I f h w) +
    covariance E (I f) (covariance I h w)+covariance E (I h) (covariance I f w)

theorem registered (interior:m+1<N) (birth:R.family.ref 4 ≤ m+1)
    (v w:R.family.label 4) (o z:Site (R.family.side (m+1) p)) (η χ:ℂ→L[ℝ]ℝ) (numerator:readings Ω):
    let live:m<N:=Nat.lt_trans (Nat.lt_succ_self m) interior
    let A:=filed R live birth v o η
    let B:=filed R live birth w z χ
    let W:=score R interior numerator
    HasDerivAt (fun t:ℝ=>covariance (reweighted (joint R (p:=p) live) W t) A B) (receipts R live A B W) 0:=by
  intro live A B W
  exact WilsonInvariantActionPriorHearing.original R live A B W

variable {n:Side}
def occurrence (Q:Rep G n) (i:ℕ) (U:Config G n):ℝ:=
  ∑' b:Finset ℕ,if i∈b then Q.activities.gasOccurrence Q.p b U else 0

private theorem budget (Q:Rep G n) {κ C L τ w:ℝ} (H:Q.Lawful κ C L τ w) (i:ℕ):
    Dominated (fun (b:Finset ℕ) (U:Config G n)=>if i∈b then Q.activities.gasOccurrence Q.p b U else 0):=by
  obtain ⟨fare,bill,cap⟩:=Activities.gasSeries H.labels
  refine ⟨fare,bill,fun b U=>?_⟩
  change ‖if i∈b then Q.activities.gasOccurrence Q.p b U else 0‖≤fare b
  by_cases inside:i∈b
  · simpa only [if_pos inside] using cap b U
  · simp only [if_neg inside,norm_zero]
    exact (norm_nonneg _).trans (cap b U)

private theorem funded (Q:Rep G n) {κ C L τ w:ℝ} (H:Q.Lawful κ C L τ w) (i:ℕ):
    Envelope (occurrence Q i):=by
  refine ⟨Measurable.tsum (fun b=>?_), (budget Q H i).bound⟩
  by_cases inside:i∈b
  · simp only [if_pos inside]
    exact Measurable.ite (Q.activities.admissible_borel Q.p b)
      (Finset.measurable_fun_prod _ (fun j _=>H.labels.forced.meas j)) measurable_const
  · simp only [if_neg inside]
    exact measurable_const

/-- The signed density derivative of the entire compatible gas when its single
filed hard activity is multiplied by one plus the parameter. -/
def hard (interior:m+1<N) (i:ℕ):readings Ω:=by
  have lawful:=(R.makes.wilson.represents N p (m+1) interior.le).good
  have valid:= ((P).exponentEnv lawful).exp.mul (funded P lawful i)
  exact ⟨fun z=>Real.exp ((P).exponent z.2)*occurrence P i z.2,
    valid.meas.comp measurable_snd,valid.cost.choose,fun z=>valid.cost.choose_spec z.2⟩

/-- The root retains every compatible physical companion and every flag. -/
theorem cofactor (interior:m+1<N) (birth:R.family.ref 4 ≤ m+1) (i:ℕ)
    (v w:R.family.label 4) (o z:Site (R.family.side (m+1) p)) (η χ:ℂ→L[ℝ]ℝ):
    let live:=Nat.lt_trans (Nat.lt_succ_self m) interior
    let A:=filed R live birth v o η
    let B:=filed R live birth w z χ
    let W:=score R interior (hard R interior i)
    (∀V:coarse,∀U:fine,actualConditionalDensity R.family N p m V U*W.val (V,U)=
      (R.family.path.levels.clock.op m p).density (R.family.path.β N p (m+1)) U V*
      (Real.exp ((P).exponent U)*occurrence P i U)/(P₀).eval V) ∧
    HasDerivAt (fun t:ℝ=>covariance (reweighted (joint R (p:=p) live) W t) A B) (receipts R live A B W) 0:=by
  intro live A B W
  exact ⟨under_kernel R interior (hard R interior i), registered R interior birth v w o z η χ (hard R interior i)⟩

end YM.Integration.WilsonInvariantActionRegisteredHearing
