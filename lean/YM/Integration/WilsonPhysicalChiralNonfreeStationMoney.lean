import YM.Integration.WilsonPhysicalChiralNonfreeStationVote
import YM.Integration.WilsonPhysicalChiralNonfreeStationSize

/-! The normalized old field keeps its physical dimensions across the
original winding correction. This also pays the linear original decoder rent. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalChiralNonfreeStationMoney
open Function Filter Finset RG Lattice Wilson Source Labels Next.Rank Next.Rank.Price Next.Rank.Atlas
open Next.Rank.Station Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open WilsonMaxwellThermometerMaximalHead WilsonOriginalMicroscopicGuardedPage RG05Readout.Address
open Trace.Physical Trace.Physical.Germ WilsonMeasuredPublicEntranceGridDebit Push.RelayDifference Bandage
open WilsonCapturedPrimaryCoreBill (wrapFee)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C" => R.family

def levy (d N per k:ℕ):ℝ:=wrapFee ((C).labels.level d) (C).params*
    wraps ((C).path.rep N per k).p ((C).side k per)*((C).path.levels.params k).columns

private theorem size_smul {d:ℕ}(F:Labels.Frame G d)(x:F.Coeff)(s:ℂ):
    F.coeffSize (s • x)=‖s‖*F.coeffSize x:=by
  simp only [Frame.coeffSize,Pi.smul_apply,smul_eq_mul,norm_mul,Finset.mul_sum]

private theorem add_back {d:ℕ}(F:Labels.Frame G d)(e y:F.Coeff):
    F.coeffSize e≤F.coeffSize y+F.coeffSize (e-y):=by
  unfold Frame.coeffSize
  rw [←Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _=>by
    change ‖e i‖≤‖y i‖+‖e i-y i‖
    simpa only [add_sub_cancel] using norm_add_le (y i) (e i-y i)

theorem same (d N per k:ℕ)(y:(C).label d)(χ:ℝ)(pos:0≤χ):
    let a:=(((C).S.a k:ℂ)^d)⁻¹
    ‖(χ:ℂ)*a‖*WilsonPhysicalChiralNonfreeStationVote.wrap R d N per k y=
      levy R d N per k*(χ*((C).labels.level d).coeffSize (awake C d k N per y)):=by
  intro a
  unfold WilsonPhysicalChiralNonfreeStationVote.wrap levy awake
  rw [size_smul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg pos]
  ring

theorem field (d N per k:ℕ)(y:(C).label d)(χ:ℝ)(pos:0≤χ)
    (early:R.t d≤k)(ref:(C).ref d≤k)(live:k≤N)
    (width:1≤((C).path.levels.budget k).supportExponent):
    let a:=(((C).S.a k:ℂ)^d)⁻¹
    ‖(χ:ℂ)*a‖*((C).labels.level d).coeffSize (fitted R d k N per y)≤
      (1+levy R d N per k)*(χ*((C).labels.level d).coeffSize (awake C d k N per y)):=by
  intro a
  have gap:= (wage R d (p:=per) early ref live width y).1
  rw [page_at R d live y] at gap
  have tri:((C).labels.level d).coeffSize (fitted R d k N per y)≤
      ((C).labels.level d).coeffSize (columns C d k N per y)+WilsonPhysicalChiralNonfreeStationVote.wrap R d N per k y:=
    (add_back _ _ _).trans (add_le_add le_rfl gap)
  calc
    _≤_:=mul_le_mul_of_nonneg_left tri (norm_nonneg ((χ:ℂ)*a))
    _=_:=by rw [mul_add,same R d N per k y χ pos,add_mul,one_mul]
            rw [awake,size_smul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg pos]
            ring

private theorem periods (f:Extraction.Order) : Tendsto (fun z : Cutoffs => z.2) f.fuse atTop := by
  refine tendsto_atTop.mpr fun b => ?_
  rw [Extraction.Order.fused]
  exact (f.per.cofinal.eventually_ge_atTop b).mono fun _ hp => Eventually.of_forall fun _ => hp

private theorem winding (f:Extraction.Order) (u:ℕ) : Tendsto (fun z : Cutoffs => Germ.wraps (R.family.path.rep z.1 z.2 u).p
    (R.family.side u z.2)) f.fuse (𝓝 0) := by
  let B := R.family.path.levels.budget u
  have grid : Tendsto (fun p : ℕ => (R.family.side u p).val) atTop atTop := by
    apply tendsto_atTop_mono (f:=fun p => (R.family.S.period p).val) _ R.family.S.period_strict.tendsto_atTop
    intro p
    exact Nat.le_mul_of_pos_right _ (R.family.S.denominator u).property
  have side : Tendsto (fun z : Cutoffs => ((R.family.side u z.2).val:ℝ)) f.fuse atTop :=
    tendsto_natCast_atTop_atTop.comp (grid.comp (periods f))
  have geo := (side.const_mul_atTop B.exponent_pos).atTop_div_const (show 0<10*(4*(B.B:ℝ)+2) by positivity)
  have exponent : Tendsto (fun z : Cutoffs => 2*B.supportExponent -
      B.supportExponent*(R.family.side u z.2).val/(10*(4*(B.B:ℝ)+2))) f.fuse atBot := by
    refine tendsto_atBot.mpr fun a => ?_
    filter_upwards [geo.eventually_ge_atTop (2*B.supportExponent-a)] with z hz
    change 2*B.supportExponent-a ≤ B.supportExponent*(R.family.side u z.2).val/(10*(4*(B.B:ℝ)+2)) at hz
    linarith
  apply (Real.tendsto_exp_atBot.comp exponent).congr'
  filter_upwards [(cutoff_grows f).eventually_ge_atTop u] with z hz
  rw [show (R.family.path.rep z.1 z.2 u).p = B from (R.makes.wilson.represents z.1 z.2 u hz).vac]
  rfl

theorem period (d k:ℕ)(f:Extraction.Order):
    Tendsto (fun z:Cutoffs=>levy R d z.1 z.2 k) f.fuse (𝓝 0):=by
  simpa only [levy,mul_zero,zero_mul] using
    ((tendsto_const_nhds (x:=wrapFee ((C).labels.level d) (C).params)).mul
      (winding R f k)).mul_const ((C).path.levels.params k).columns

end YM.Integration.WilsonPhysicalChiralNonfreeStationMoney
