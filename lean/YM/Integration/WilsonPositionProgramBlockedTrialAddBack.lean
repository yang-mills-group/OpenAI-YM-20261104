import YM.Integration.WilsonPositionProgramBlockedTrialPanel
import YM.Integration.PhysicalWilsonHotIntegral
import YM.Extra.MULTISOURCE_BOUNDS.Columns
/-! The uncut trial at a nonbare birth. Only its nonunit field is corrected
on the failed stencil. This absolute invoice is on the same original Wilson
law, and is valid on each earlier held law through the actual transport. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonPositionProgramBlockedTrialAddBack
open Function Filter Finset MeasureTheory Lattice Wilson RG Extra.Histories Labels Source
open PhysicalNext.Repeat.Legato OPE.Therm Push.AbsoluteSums.Animals Extra.Multi
open WilsonPositionProgramOriginalBlockedTrial
open scoped Classical BigOperators

variable {G:Gauge} (R:Run G) (d:ℕ)
local notation "C₀" => R.family
local notation "F₀" => (C₀).labels.level d
local notation "B₀" => (C₀).localSection d
local notation "H₀" => (C₀).path

def names (N p K:ℕ) (v:(C₀).label d) : (C₀).label d :=
  (F₀).scaled (((H₀).rep N p K).p.threshold)⁻¹ ((F₀).core v)

def uncut (N p K:ℕ) (o:Site ((C₀).side K p)) (v:(C₀).label d) (U:Config G ((C₀).side K p)) : ℂ :=
  v 0 + (B₀).places (names R d N p K v) o U

def missed (N p K:ℕ) (o:Site ((C₀).side K p)) (v:(C₀).label d) :
    Config G ((C₀).side K p)→ℂ :=
  let W:=(H₀).rep N p K
  PhysicalWilsonHotIntegral.restricted (E:=SelectedCofactorAnchoredRegister.hot W.p.threshold ((B₀).footprint o)) 1
    ((B₀).places (names R d N p K v) o)

theorem field (N p K:ℕ) (o:Site ((C₀).side K p)) (v:(C₀).label d) (U:Config G ((C₀).side K p)) :
    let W:=(H₀).rep N p K
    (W.eval U:ℂ)*uncut R d N p K o v U =
      numerator R d N p K o v U + (W.eval U:ℂ)*missed R d N p K o v U:=by
  intro W
  let S:=(B₀).footprint o
  let E:=SelectedCofactorAnchoredRegister.hot (G:=G) W.p.threshold S
  have hot:U∈E ↔ ¬Healthy W.p.threshold S U:=by
    simp [E,SelectedCofactorAnchoredRegister.hot,Healthy,Finset.disjoint_left]
  rw [original_field,←mul_add]
  congr 1
  let f:=(B₀).places (names R d N p K v) o
  change v 0 + f U = (v 0 + masked W.p.threshold S f U) + E.indicator (fun V=>(1:ℝ) • f V) U
  by_cases h:U∈E
  · rw [masked_ne _ _ _ _ (hot.mp h),Set.indicator_of_mem h,one_smul,add_zero]
  · rw [masked_eq _ _ _ _ (by by_contra bad;exact h (hot.mpr bad)),Set.indicator_of_notMem h,add_zero]

theorem earlier (simple:G.Simple) (quote:Poetry (H₀).levels):
  ∃ C:ℝ,0≤C ∧ ∀ᶠ K:ℕ in atTop,∀ N p,K≤N → ∀ (o:Site ((C₀).side K p)) (v:(C₀).label d) j (hj:j≤K),
    (∫ U, ‖actualTransport C₀ (N:=N) (missed R d N p K o v) hj U‖ ∂scene H₀ N p j) ≤
      C*((F₀).coeffSize (names R d N p K v))*(H₀).levels.clock.forcedAllowance K:=by
  let B:=BasisCost.price B₀
  have hB:0≤B:=zero_le_one.trans (BasisCost.price_pos B₀)
  let count:ℝ:=((B₀).stencil.card*ballCost 2*Fintype.card PlaqAxes:ℕ)
  refine ⟨B*count,mul_nonneg hB (by unfold count;positivity),?_⟩
  filter_upwards [PhysicalWilsonHotIntegral.divided R simple quote (ρ:=1) zero_lt_one 0] with K bought N p live o v j hj
  let W:=(H₀).rep N p K
  let S:=(B₀).footprint o
  let E:=SelectedCofactorAnchoredRegister.hot (G:=G) W.p.threshold S
  let x:=names R d N p K v
  let a:=∑i,‖x i‖
  have ha:0≤a:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have hE:MeasurableSet E:=SelectedCofactorAnchoredRegister.measurable _ _
  have sub:E⊆SelectedCofactorAnchoredRegister.hot (1*W.p.threshold) S:=by rw [one_mul]
  have cert:=bought N live p S E hE sub 0 le_rfl (B*a) (mul_nonneg hB ha)
    ((B₀).places x o) ((B₀).continuous_places x o).measurable (fun U _=>BasisCost.full B₀ x o U) j hj
  have cells:S.card≤(B₀).stencil.card:=Finset.card_image_le
  have geo:((S.card*ballCost 2*Fintype.card PlaqAxes:ℕ):ℝ)≤count:=by
    unfold count
    exact_mod_cast Nat.mul_le_mul_right (Fintype.card PlaqAxes) (Nat.mul_le_mul_right (ballCost 2) cells)
  have pos:0≤(H₀).levels.clock.forcedAllowance K:=Real.exp_nonneg _
  simp only [pow_zero,inv_one] at cert
  apply cert.trans
  calc _ ≤ B*a*count*(H₀).levels.clock.forcedAllowance K:=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left geo (mul_nonneg hB ha)) pos
     _ = _:=by change B*a*count*_=B*count*a*_;ring
end YM.Integration.WilsonPositionProgramBlockedTrialAddBack
end
