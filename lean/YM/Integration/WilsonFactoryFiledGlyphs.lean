import YM.Integration.WilsonFactoryBoxedFields
import YM.Integration.WilsonFactoryPhysicalGlyphs

/-! The precise input register for the independently prescribed named field,
on the original finite Wilson factory. Its difference from the measured
J-field is a single original signed register on the very same ensemble. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFactoryFiledGlyphs
open Function Finset Lattice Wilson RG Labels Spec OPE PhysicalNext.Repeat.Legato
open MS MS.Menus MS.Local.Physical FVAAlt2 FVA2 Extra.Histories
open RegulatorIR.FVAAlt2.Lodge WilsonFactoryBoxedFields MeasureTheory
open scoped Classical BigOperators Topology
variable {G : Gauge} (R : Run G) {B : Deck G} (v : MS.Rake.Label B) (N per : ℕ) (g : ℝ)
set_option quotPrecheck false
local notation "F" => R.family.labels.level v.h
local notation "T" => R.family.factory v.h N per
local notation "θ" => R.family.path.levels.clock.threshold N
local notation "Γ" => Lobby.γ (basisR R) v
local notation "n₁" => R.family.side N per

def ledger : R.family.label v.h := (T).terminal ((F).scaled (g/θ)⁻¹ Γ)
def material (x : Site n₁) (U : Config G n₁) : ℂ :=
  ∑ j : (F).Index, Γ j * ((g:ℂ)^((F).grades j).2)⁻¹ * (Lobby.poster (basisR R) v x j U : ℂ)

theorem paid (hg : g≠0) : restored R v.h N per (ledger R v N per g) g = Γ := by
  unfold restored ledger
  rw [LinearEquiv.symm_apply_apply]
  exact (F).scaled_inv (div_ne_zero hg (R.family.path.levels.budget N).threshold_pos.ne') _

theorem word_eq (hg : g≠0) (x : Site n₁) (U : Config G n₁) :
    word R v.h N per (ledger R v N per g) g x U = material R v N per g x U := by
  unfold word material
  rw [paid R v N per g hg]
  refine sum_congr rfl fun j _ => ?_
  rw [WilsonRichPrimitiveRows.physical R v x j U]
  rfl

theorem visible (hg : g≠0) (x : Site n₁) (U : Config G n₁) :
    R.family.O N per (ledger R v N per g) x U =
      ((R.family.S.a N:ℂ)^v.h)⁻¹ * material R v N per g x U := by
  rw [field R v.h N per _ hg,word_eq R v N per g hg]

theorem positive_input (hg : g≠0) (deep : R.family.ref v.h ≤ N) (U : Config G n₁) :
    ((T).entries N ((F).scaled (g/θ)⁻¹ Γ)).density 0 (R.family.localSection v.h)
      (R.family.path.rep N per N) U = (Wilson.bare (R.family.beta N per) U:ℂ) * material R v N per g 0 U := by
  have hp := WilsonFactoryBoxedFields.top R v.h N per (ledger R v N per g) hg deep U
  rw [word_eq R v N per g hg] at hp
  simpa only [ledger,LinearEquiv.symm_apply_apply] using hp

variable {S : Table R.family.book} (J : ℝ → PhysMS.tower S) (r : ℝ)

def current : R.family.label v.h := S.representative v.h (J r v.h
  (Pert.RawLabels.enroll R.family.labels v.h (FVAAlt2.Shop.seat B v.item.2)))
def difference : R.family.label v.h := current R v J r - ledger R v N per g

theorem coefficients (hg : g≠0) :
    restored R v.h N per (difference R v N per g J r) g =
      restored R v.h N per (current R v J r) g - Γ := by
  rw [← paid R v N per g hg]
  unfold difference restored
  rw [map_sub,map_sub]

theorem discrepancy (x : Site n₁) (U : Config G n₁) :
    R.family.O N per (difference R v N per g J r) x U =
    R.family.O N per (current R v J r) x U - R.family.O N per (ledger R v N per g) x U := by
  let A := (R.family.linearO N per v.h x).mk' _
  exact congrFun (map_sub A (current R v J r) (ledger R v N per g)) U

/-- True complex material on the original fixed positive measure. The two
signed terms keep every spectator and the genuine two joint insertions. -/
theorem joint (w : MS.Rake.Label B) (s : ℝ) (x y : Site n₁) (ζ : Config G n₁ → ℂ) (hz : Continuous ζ) :
    R.family.omega N per (fun U => R.family.O N per (current R v J r) x U *
        R.family.O N per (current R w J s) y U * ζ U) -
      R.family.omega N per (fun U => R.family.O N per (ledger R v N per g) x U *
        R.family.O N per (ledger R w N per g) y U * ζ U) =
      R.family.omega N per (fun U => (R.family.O N per (difference R v N per g J r) x U *
        R.family.O N per (current R w J s) y U + R.family.O N per (ledger R v N per g) x U *
        R.family.O N per (difference R w N per g J s) y U) * ζ U) := by
  unfold Family.omega Wilson.moment
  rw [← integral_sub]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun U => by
      dsimp only
      rw [discrepancy R v N per g J r x U,discrepancy R w N per g J s y U]
      ring
  · exact Wilson.continuous_integrable _ (((R.family.continuousO N per _ _ x).mul
        (R.family.continuousO N per _ _ y)).mul hz)
  · exact Wilson.continuous_integrable _ (((R.family.continuousO N per _ _ x).mul
        (R.family.continuousO N per _ _ y)).mul hz)

end YM.Integration.WilsonFactoryFiledGlyphs
