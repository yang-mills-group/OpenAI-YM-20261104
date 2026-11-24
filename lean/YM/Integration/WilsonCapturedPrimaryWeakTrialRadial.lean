import YM.Integration.WilsonCapturedPrimaryWeakTrialColumn
import YM.Integration.WilsonCapturedPrimarySampledPanel

/-! A finite reconstruction of the intrinsic graded page of the returned
trial. All abscissae and gauge configurations come from the original run. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWeakTrialRadial
open Function Filter Finset Set Lattice RG Wilson Source Labels Push.Local Extra.Histories
open Next.Foundations ProjectorNext.Equivariance Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Pert.Asymptotics Stationary Comparison.RG02 RG16 RG16.Literal
open WilsonCapturedPrimaryAperture WilsonCapturedPrimaryPotential WilsonCapturedPrimaryPaid
open WilsonCapturedPrimaryReading WilsonCapturedPrimaryCollar WilsonFirstReceivedRadialStencil
open WilsonPositionProgramBlockedTrialNodes
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) (d N per i target D : ℕ)
local notation "Fr" => R.family.labels.level d
local notation "W" => R.family.path.rep N per i
local notation "g" => regulatorRun R.family N per (i+1)

def field (a : Probe G d) (j : ℕ) : Config G (R.family.side i per) :=
  let b := R.family.path.levels.budget i
  let r := radius b (cutoff b g (grade target d 1))
  let z := g ^ gap target 1 * node D j
  Integral.sample g (Stationary.arm G (R.family.side i per) 1 (lifted R.family.params b 0 r a g z))

def slate (Y : Config G (R.family.side i per) → ℂ) (a : Probe G d) : Polynomial ℂ :=
  WilsonCapturedPrimarySampledPanel.sample D (g ^ gap target 1)
    (fun j => Y (field R d N per i target D a j))

def decode (Y : Config G (R.family.side i per) → ℂ) : R.family.label d :=
  WilsonCapturedPrimaryDecoder.forecast (Fr) (slate R d N per i target D Y)

def price (e : R.family.label d) (extra : ℝ) : ℝ :=
  2^(degree (Fr))*WilsonCapturedPrimaryDecoder.invoice (Fr) R.family.params D *
    (originalRent R d i e+extra)*g^target

theorem calibrated (live : i < N) (rd : d ≤ D) (q : Coefficient (Fr) (R.family.side i per))
    (e : R.family.label d) (earned : Invoice R d N per i target e q)
    (Y : Config G (R.family.side i per) → ℂ) {extra : ℝ} (nonnegative : 0 ≤ extra)
    (heard : ∀ a ∈ tests (Fr), ∀ j ≤ D,
      let V := field R d N per i target D a j
      ‖reading (R.family.localSection d) W 0 q V-Y V‖ ≤ (originalRent R d i e+extra)*g^(grade target d 1)) :
    (Fr).coeffSize (gMap R.family N per d i (e-decode R d N per i target D Y)) ≤
      price R d N per i target D e extra := by
  have pg : 0 < g := RG16.Literal.g_pos R.makes live
  have step : g ^ gap target 1 ≠ 0 := pow_ne_zero _ pg.ne'
  apply earned extra nonnegative D rd (slate R d N per i target D Y)
  · exact fun a _ => WilsonCapturedPrimarySampledPanel.degree D step _
  · intro a ha j hj z X angle _ _ _
    change ‖reading (R.family.localSection d) W 0 q (field R d N per i target D a j) -
      (slate R d N per i target D Y a).eval (((g ^ gap target 1 * node D j : ℝ) : ℂ))‖ ≤ _
    rw [slate,WilsonCapturedPrimarySampledPanel.at_node D step _ hj]
    exact heard a ha j hj

theorem original (live : i < N) (rd : d ≤ D) (q : Coefficient (Fr) (R.family.side i per))
    (e : R.family.label d) (earned : Invoice R d N per i target e q) :
    let Y := reading (R.family.localSection d) W 0 q
    let err := gMap R.family N per d i (e-decode R d N per i target D Y)
    (Fr).coeffSize err ≤ price R d N per i target D e 0 ∧
      ∀ a : (Fr).Index, ‖err a‖ ≤ price R d N per i target D e 0 := by
  intro Y err
  have pg : 0 < g := RG16.Literal.g_pos R.makes live
  have col : 0 ≤ (R.family.path.levels.params i).columns :=
    zero_le_one.trans (R.family.path.levels.params i).columns_ge
  have rent : 0 ≤ originalRent R d i e := by
    unfold originalRent Trace.Physical.GermGraph.stock Trace.Physical.GermGraph.stage
    exact mul_nonneg (mul_nonneg (by norm_num) (add_nonneg col col)) (Work.G08.size_nonneg _ _)
  have read : (Fr).coeffSize err ≤ price R d N per i target D e 0 := by
    apply calibrated R d N per i target D live rd q e earned Y le_rfl
    intro a _ j _ V
    simp only [Y,sub_self,norm_zero,add_zero]
    exact mul_nonneg rent (pow_nonneg pg.le _)
  refine ⟨read,fun a => le_trans ?_ read⟩
  exact Finset.single_le_sum (f:=fun j => ‖err j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ a)

end YM.Integration.WilsonCapturedPrimaryWeakTrialRadial
