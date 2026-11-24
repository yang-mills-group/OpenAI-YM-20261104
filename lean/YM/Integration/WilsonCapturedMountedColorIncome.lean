import YM.Integration.WilsonCapturedPinnedColorFile
/-! The rooted tariff on the actual real tensor filed in the native committee.
The degree normalization retains the precise factorial. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedMountedColorIncome
open Function Finset Lattice RG Wilson Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise Stationary
open Comparison.RG02 Comparison.RG02.Adjacent Multi
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalOccupiedFieldLayout WilsonCapturedPinnedGroupClock WilsonCapturedPinnedClockIncome
open WilsonCapturedCoveredSourceWage WilsonCapturedPinnedColorFile WilsonOriginalLinkedAngularPage
open WilsonOriginalCenteredSeamSalary WilsonCapturedRootedAngularSlots WilsonCapturedClockRankProjection
open RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Pipeline RegulatorIR.FVAAlt2.Booth
open scoped Classical BigOperators
variable {G:Gauge}{n N:Side}{V X ι:Type}[DecidableEq V]{o:Passport n V}{J:Census V}
    (h:n.val∣N.val)(M:ι→Row o J G X)(t:X)(s:J.Mode)(v:s.val)
    {w:V→ℝ}{grades:V→ℕ}{σ C:ℝ}{order seats shelf:ℕ}
    (stock:Scene.Armada M w grades σ C order seats shelf)(hs:0<σ)(cut:ι→Prop)
    (b:PagesOf n N)(clock:UnitCost)(pole:ℕ)(quiet:ℝ → Config G N → ℝ)
local notation "row" => reportedRow h M t s v cut b clock pole

include stock hs in
theorem crop (L:ℂ→L[ℝ]ℝ)(sh:LipschitzWith 1 L)(e r:ℕ)(α:ℝ)(root:Site N):
     (∑x:Fin r→Site N×Loc G 1,Real.exp (α*(radius root (sites x):ℝ))*
        |WilsonCapturedRealFiledKernel.entries (fun j=>L ∘ row j quiet) e r x|) ≤
      (r.factorial:ℝ)⁻¹ * exposure α r root (row e quiet):=by
  unfold exposure
  rw [mul_sum]
  apply sum_le_sum;intro x _
  rw [WilsonCapturedPinnedColorFile.coefficient h M t s v stock hs cut b clock pole quiet L e r x,smul_eq_mul,abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)),mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  simpa only [dist_zero_right,map_zero,NNReal.coe_one,one_mul,Real.norm_eq_abs] using
    sh.dist_le_mul (WilsonOriginalLinkedAngularPage.coefficient r (row e quiet) x) 0

include stock hs in
theorem original (L:ℂ→L[ℝ]ℝ)(sh:LipschitzWith 1 L)(e r:ℕ)(hr:0<r):
    let root:=(page h (o.origin v.val) b).val
    let bank:=WilsonCapturedRealFiledKernel.entries (fun j=>L ∘ row j quiet)
    Arm.Single clock (channel L (ink h (WilsonCapturedCoveredSourceWage.crop M cut) t s v b pole quiet)) bank () e pole ∧
    Poly.toll w s*(∑x:Fin r→Site N×Loc G 1,Real.exp ((σ/8)*(radius root (sites x):ℝ))*|bank e r x|) ≤
      (r.factorial:ℝ)⁻¹*charge clock (-(pole:ℤ)) (pole+e) r (fun j=>fare G j r σ C):=by
  intro root bank
  refine ⟨WilsonCapturedPinnedColorFile.filed h M t s v stock hs cut b clock pole quiet L e,?_⟩
  have wage:=WilsonCapturedPinnedClockIncome.original h M t s v stock hs cut b clock pole e quiet r hr
  have toll:0≤Poly.toll w s:=prod_nonneg fun v _=>(stock.positive v).le
  calc
    _ ≤ Poly.toll w s*((r.factorial:ℝ)⁻¹*exposure (σ/8) r root (row e quiet)):=
      mul_le_mul_of_nonneg_left (WilsonCapturedMountedColorIncome.crop h M t s v stock hs cut b clock pole quiet L sh e r _ _) toll
    _ = _:=mul_left_comm ..
    _ ≤ _:=mul_le_mul_of_nonneg_left wage (inv_nonneg.mpr (Nat.cast_nonneg _))

end YM.Integration.WilsonCapturedMountedColorIncome
