import YM.Integration.WilsonMaxwellThermometerStationHeads
import YM.Integration.WilsonMovingForkMixedSeed

/-! The fitted public vote and the signed weak station head on one actual
microscopic source. The difference in their common station coordinates
is the authenticated finite-period wrap of that source. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalChiralNonfreeStationVote
open Function Filter Finset RG Lattice Wilson Source Labels Next.Rank Next.Rank.Price Next.Rank.Atlas
open Next.Rank.Station Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East Trace.Physical.Germ
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonMaxwellThermometerMaximalHead WilsonOriginalMicroscopicGuardedPage RG05Readout.Address
open Pert.Asymptotics RG05Readout WilsonCapturedPrimaryCoreBill WilsonMeasuredPublicEntranceGridDebit
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family

private theorem change_head {d:ℕ}(F:Labels.Frame G d)(χ:ℝ)(a:ℂ)(x y p:F.Coeff):
    error F χ (a • x) p ≤ error F χ (a • y) p + ‖(χ:ℂ)*a‖*F.coeffSize (x-y):=by
  unfold error Frame.coeffSize
  rw [mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro i _
  by_cases hi:F.grades i=(d,d/2)
  · simp only [if_pos hi,Pi.smul_apply,smul_eq_mul,Pi.sub_apply]
    rw [←norm_mul]
    calc
      _ = ‖((χ:ℂ)*(a*y i)-p i)+((χ:ℂ)*a)*(x i-y i)‖ := by congr 1;ring
      _ ≤ _ := norm_add_le .. 
  · simp only [if_neg hi,zero_add]
    positivity

def wrap (d N per k:ℕ)(y:R.family.label d):ℝ:=
    wrapFee ((C).labels.level d) (C).params*
    wraps ((C).path.rep N per k).p ((C).side k per)*
    (((C).path.levels.params k).columns*((C).labels.level d).coeffSize (columns C d k N per y))

theorem filed (d N per k:ℕ)(early:R.t d≤k)(ref:(C).ref d≤k)(live:k≤N)
    (width:1≤((C).path.levels.budget k).supportExponent)(y:R.family.label d)
    (A:(C).label d≃ₗ[ℂ](C).label d)(χ:ℝ)(p:(C).label d):
    let a:=(((C).S.a k:ℂ)^d)⁻¹
    let dose:=A.symm (fitted R d k N per y)
    error ((C).labels.level d) χ (a • A dose) p ≤
      error ((C).labels.level d) χ (awake C d k N per y) p + ‖(χ:ℂ)*a‖*wrap R d N per k y:=by
  intro a dose
  have fullPage:fitted R d k N per y=full R d N per k y:=(page_at R d live y).symm
  have paid:((C).labels.level d).coeffSize (fitted R d k N per y-columns C d k N per y)≤wrap R d N per k y:=by
    rw [fullPage]
    exact (wage R d (p:=per) early ref live width y).1
  dsimp only [dose]
  rw [LinearEquiv.apply_symm_apply]
  exact (change_head _ χ a _ (columns C d k N per y) p).trans
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left paid (norm_nonneg _)))

variable {f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}

theorem original (simple:G.Simple):∀ᶠ k:ℕ in atTop,∀A:Group C 6,
    A.station.k=k → A.station.checked f H A.horizon → ∀N per,k<N → ∀s (i:Fin 3),
    let d:=index A (grade i)
    let x:=A.change (grade i) (source C s i)
    let p:=ladder C d x
    let y:=A.station.wheel.atCut (N,per) d x
    let χ:=(shrink C k N per)^(d.val/2)/(Station.mag (C).path.levels A.station.b k)^d.val
    let a:=(((C).S.a k:ℂ)^d.val)⁻¹
    R.t d≤k → (C).ref d≤k → 1≤((C).path.levels.budget k).supportExponent →
    ∀S:(C).label d≃ₗ[ℂ](C).label d,
    let dose:=S.symm (fitted R d k N per y)
    error ((C).labels.level d) χ (a • S dose) p ≤
      WilsonMaxwellThermometerStationHeads.fee R k/(1-WilsonMaxwellThermometerStationHeads.fee R k)*
      ((C).labels.level d).coeffSize p+‖(χ:ℂ)*a‖*wrap R d N per k y:=by
  filter_upwards [WilsonMaxwellThermometerStationHeads.original (f:=f) (H:=H) R simple] with k known
  intro A hk checked N per live s i d x p y χ a early ref width S dose
  exact (filed R d N per k early ref live.le width y S χ p).trans
    (add_le_add (known A hk checked N per live s i) (le_refl _))

end YM.Integration.WilsonPhysicalChiralNonfreeStationVote
