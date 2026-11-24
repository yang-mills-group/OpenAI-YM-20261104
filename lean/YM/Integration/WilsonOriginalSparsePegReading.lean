import YM.Integration.WilsonOriginalCensusChildReading
import YM.Integration.WilsonOriginalSparsePeg

/-! Read an ordered peg by comparing the two original child pupils only on its
finite list of sparse directions. The remaining peg incomes keep their own prices. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSparsePegReading
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Earn.Scene QuadraticLocal.Sunrise
open AllOrder AllOrder.Floe Laurent Comparison.RG02 Comparison.Density Comparison.Density.Mirrors
open Transport AnalyticBridge.SectorAffine.Offset WilsonEmittedWordJointFare WilsonEmittedCutGrouping
open WilsonEmittedFiledCatalogue Push.AbsoluteSums WilsonOriginalCensusPhysicalLoad
open Stationary Exterior Comparison.RG02.Adjacent Multi
open FVA1Physical FVA1Physical.TwoReset Further.PhysicalPeriodLimitF933 Macrame
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Booth
open RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open WilsonCapturedRootedAngularSlots WilsonCapturedPrimaryWindingMaterialRead
open WilsonNeutralTwoPrintPeg WilsonCoeffUV WilsonCoeffUV.Blue FormalBulk08
open WilsonOriginalCensusFiledProbe
open scoped BigOperators ContDiff Classical Matrix.Norms.Frobenius

variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V]{Γ:Census V}
  {I X:Bool→Type}{P:Bool→Passport n V}(M:(a:Bool)→I a→Row (P a) Γ G (X a))
  (x:(a:Bool)→X a)(grades:Bool→V→ℕ)(s:Multi.Hot Γ)
  (layout:Bool→Layout G)(tape:Bool→Finset Age)(legal:∀a,Legal (tape a) (layout a))
  {w:Bool→V→ℝ}{σ b:Bool→ℝ}{p seats shelf:Bool→ℕ}
  (stock:∀a,Scene.Armada (M a) (w a) (grades a) (σ a) (b a) (p a) (seats a) (shelf a))
  (positive:∀a,0<σ a)(v₀:s.val.val)

local notation "Slots" => Site n × Loc G 1
local notation "pupil" a:max e:max Y:max =>
  (peek dvd_rfl (M a) (grades a) (layout a) (tape a) (x a) e Y).part s.val
local notation "table" a:max l:max =>
  WilsonNeutralTwoPrintFronts.table (M a) (x a) (grades a) (layout a) (tape a) s (phase l)
local notation "cap" e:max => e + WilsonOriginalCensusPhysicalLoad.head grades s.val
local notation "print" a:max l:max e:max =>
  packed ((table a l) e) (e + (Launch.index Γ (grades a) s.val + 1))

/-- The signed polynomial is determined by the two funded printed spectra. -/
def difference (e:ℕ) (l:Bool) : MvPolynomial Slots ℝ := (print false l e) - (print true l e)

private theorem degree_packed {I:Type}[Fintype I] (T:Ranked I) (k:ℕ) :
    (packed T k).totalDegree ≤ k := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro t ht
  change (Lava.facade t (T t)).totalDegree ≤ k
  exact (Lava.facade_grade t (T t)).totalDegree_le.trans (Nat.le_of_lt_succ (mem_range.mp ht))

theorem cutoff (e:ℕ) (l:Bool) :
    (difference M x grades s layout tape e l).totalDegree ≤ cap e := by
  unfold difference
  refine (MvPolynomial.totalDegree_sub ..).trans (max_le ?_ ?_)
  · exact (degree_packed ..).trans
      (Nat.add_le_add_left (Nat.succ_le_succ (le_max_left ..)) e)
  · exact (degree_packed ..).trans
      (Nat.add_le_add_left (Nat.succ_le_succ (le_max_right ..)) e)

include stock positive legal v₀ in
theorem angular (e:ℕ) (l:Bool) (Y:Link G n) :
    phase l (pupil false e Y) - phase l (pupil true e Y) =
      MvPolynomial.eval Y (difference M x grades s layout tape e l) := by
  rw [difference,map_sub]
  exact congrArg₂ (·-·)
    ((WilsonNeutralTwoPrintPathSpectrum.paid M x grades s layout tape stock positive legal v₀ false l e).1 Y)
    ((WilsonNeutralTwoPrintPathSpectrum.paid M x grades s layout tape stock positive legal v₀ true l e).1 Y)

include stock positive legal v₀ in
theorem entry (e r:ℕ) (hr:r ≤ cap e) (z:Fin r→Slots) (E:ℝ) (hE:0≤E)
    (near:∀ S j, let Y := WilsonOriginalSparsePeg.probe (cap e) z S j
      ‖pupil false e Y - pupil true e Y‖ ≤ E) :
    ‖WilsonNeutralTwoPrintAccount.entry M x grades s layout tape e r z‖ ≤
      2 * WilsonOriginalSparsePeg.cost (cap e) * E := by
  let D:=difference M x grades s layout tape e
  have heard := angular M x grades s layout tape legal stock positive v₀ e
  have mono (l:Bool) : |Lava.marble r (D l) z| ≤ WilsonOriginalSparsePeg.cost (cap e) * E := by
    apply WilsonOriginalSparsePeg.original _ (cutoff M x grades s layout tape e l) hr z hE
    intro S j
    let Y:=WilsonOriginalSparsePeg.probe (cap e) z S j
    rw [←heard,←map_sub]
    cases l
    · exact (Complex.abs_re_le_norm _).trans (near S j)
    · exact (Complex.abs_im_le_norm _).trans (near S j)
  rw [WilsonNeutralTwoPrintPathSpectrum.original M x grades s layout tape stock positive legal v₀ e D heard r z]
  refine (norm_add_le ..).trans ?_
  rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
  linarith [mono false,mono true]

include stock positive legal v₀ in
/-- At a given site the signed near probes can be combined with independently paid
far pegs. Every probe reads both live pupils on their own original wallet. -/
theorem mass (e:ℕ) (near:(r:ℕ)→(Fin r→Slots)→Prop)
    (E:(r:ℕ)→(Fin r→Slots)→ℝ) (positiveE:∀r z,near r z → 0≤E r z)
    (localRead:∀r≤cap e,∀z,near r z → ∀ S j, let Y := WilsonOriginalSparsePeg.probe (cap e) z S j
      ‖pupil false e Y - pupil true e Y‖ ≤ E r z) :
    WilsonEmittedAngularJointFare.mass (WilsonNeutralTwoPrintAccount.entry M x grades s layout tape e) (cap e) ≤
      ∑r∈range ((cap e)+1),∑z,if near r z then 2*WilsonOriginalSparsePeg.cost (cap e)*E r z
      else ‖WilsonNeutralTwoPrintAccount.entry M x grades s layout tape e r z‖ := by
  unfold WilsonEmittedAngularJointFare.mass
  refine sum_le_sum fun r hr => sum_le_sum fun z _ => ?_
  split_ifs with inside
  · exact entry M x grades s layout tape legal stock positive v₀ e r
      (Nat.le_of_lt_succ (mem_range.mp hr)) z (E r z) (positiveE r z inside)
      (localRead r (Nat.le_of_lt_succ (mem_range.mp hr)) z inside)
  · exact le_rfl

variable [Fintype V] (B:BudgetPoint) (g:ℝ) (o:Site n) (tube:LinkTube G)
    (source target:ℕ) (A δ:ℝ)
local notation "D₀" => WilsonOriginalCensusPhysicalLoad.rank grades
local notation "lag" => WilsonOriginalCensusPhysicalLoad.delay grades s.val
local notation "height" => WilsonOriginalCensusPhysicalLoad.head grades s.val +
  WilsonOriginalCensusTariff.debit source D₀ + target

include stock positive legal v₀ in
/-- File the measured near pegs and the paid original far subtotal on this child's
actual two wallets. The thermal and geometric invoices are the native receiver's. -/
def original (near:(e r:ℕ)→(Fin r→Slots)→Prop) (E:(e r:ℕ)→(Fin r→Slots)→ℝ)
    (ε:ℝ) (eps:0≤ε) (home:∀a,(P a).origin v₀=o)
    (positiveE:∀e,cap e < 3*height → ∀r z,near e r z → 0≤E e r z)
    (localRead:∀e,cap e < 3*height → ∀r≤cap e,∀z,near e r z → ∀ S j,
      let Y := WilsonOriginalSparsePeg.probe (cap e) z S j
      ‖pupil false e Y - pupil true e Y‖ ≤ E e r z)
    (total:∀e,cap e < 3*height → ((cap e).factorial:ℝ) *
      (∑r∈range ((cap e)+1),∑z,if near e r z then 2*WilsonOriginalSparsePeg.cost (cap e)*E e r z
      else ‖WilsonNeutralTwoPrintAccount.entry M x grades s layout tape e r z‖) ≤ ε)
    (width:ℝ)(room:Room B n tube B.B width)(radius:0≤width)(held:width≤2*g^(1/2:ℝ))
    (H β:ℝ)(thermal:H/2≤β ∧ β≤2*H)(dated:g=(Real.sqrt β)⁻¹)(small:g≤1/2)
    (side:B.B=Nat.ceil ((Real.log H)^2))(tax:B.supportExponent+2≤102)(reserve:∀a,Real.exp ((σ a)⁻¹^2)≤H)
    (begun:WilsonOriginalCensusTariffDate.Begun tube (Fintype.card V) D₀ (3*height) height p lag H)
    (quote:((g^(WilsonOriginalCensusPhysicalLoad.head grades s.val))⁻¹*
      (groupPrice tube 0*((2*height:ℕ):ℝ)*((3*height:ℕ):ℝ)))*ε+
      (WilsonEmittedOutputPower.constant height+1)*(posted A D₀)*g^target≤δ):
    Reading M grades x B σ p g s v₀ o tube source target A δ := by
  refine ⟨layout,tape,legal,ε,eps,?_,home,small,width,room,radius,held,H,β,thermal,dated,
    side,tax,reserve,begun,quote⟩
  intro e live
  exact (mul_le_mul_of_nonneg_left
    (mass M x grades s layout tape legal stock positive v₀ e (near e) (E e)
      (positiveE e live) (localRead e live)) (Nat.cast_nonneg _)).trans (total e live)

end YM.Integration.WilsonOriginalSparsePegReading
end
