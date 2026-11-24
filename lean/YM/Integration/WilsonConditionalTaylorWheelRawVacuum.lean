import YM.Integration.WilsonConditionalTaylorWheelIssuedResponse
import YM.Integration.WilsonConditionalTaylorWheelTensors

/-! The pre-reset upper vacuum is the entire signed logarithm of the
same original finite partition function, modulo its explicit scalar
and the original zeroth-order kinetic polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelRawVacuum
open Function Matrix Lattice RG Exterior Wilson Precision Tree FreeResolvent Bloch PowerSeries Next.Foundations
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Jets FormalBulk08.Orb FormalBulk08.Series
open FormalBulk08.Lava FormalBulk08.Shore
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Wheel
open WilsonConditionalTaylorWheelKernel
open scoped Classical BigOperators Matrix
variable {G:Gauge} (D:Stage G)
local notation "op" => D.R.family.path.levels.clock.op D.j D.per
local notation "coarse" => D.R.family.side D.j D.per
local notation "fine" => D.R.family.side (D.j+1) D.per
local notation "form" => freeForms D.R.family.path.levels D.N (D.j+1)
local notation "target" => freeForms D.R.family.path.levels D.N D.j
set_option quotPrecheck false in
local notation "mean" => installed (op).ratio (predictionA D.R.family.path.levels D.N D.j)
local notation "bank" => Winding.emera (actionW D.R.family.path.levels D.R.metals.O D.N (D.j+1)) fine

theorem logarithm {U:Type} (T:Pap U) (unit:constantCoeff T=1):logOf T=covelog T:=by
  have origin:coeff 0 (logOf T)=0:=by rw [coeff_zero_eq_constantCoeff_apply,constantCoeff_logOf unit]
  have actual:expan (logOf T)=T:=raising_log unit
  exact (covelog_after origin).symm.trans (congrArg covelog actual)

def inside : Pap (wire G coarse):=
  amount D (expan (shot op D.forest mean D.R.metals.O bank))

theorem issued (simple:G.Simple):
    -flash (winter op D.forest form target mean D.R.metals.O bank)=
      covelog (inside D)-orbC (precisionC G coarse target)-soil (plugζ op D.R.metals.O):=by
  have old:=Winding.emera_far D.R.family.path.levels simple D.R.alloy.B.ratio (Nat.succ_le_iff.mpr D.live) fine
  rw [winter_read op D.forest form target mean old.1 D.R.alloy.B.ratio
    (D.R.family.path.levels.blocks D.j D.per).branches (age_sym D.R.family.path.levels ..) old.2]
  rw [logarithm _ (inside_mass op D.forest form mean (P:=bank) D.R.alloy.B.ratio),
    WilsonConditionalTaylorWheelKernel.vacuum]
  unfold inside
  abel

theorem occupied (simple:G.Simple) (e r:ℕ) (pos:0<e) (active:0<r):
    rancho (-flash (winter op D.forest form target mean D.R.metals.O bank)) e r=
      rancho (covelog (inside D)) e r:=by
  rw [issued D simple]
  change canyon r (coeff e (_-_ -_))=canyon r (coeff e (covelog (inside D)))
  simp only [map_sub,orbC,coeff_C,if_neg pos.ne',sub_zero,soil,coeff_map]
  have h:Lava.marble r (MvPolynomial.C (coeff e (plugζ op D.R.metals.O)):MvPolynomial (wire G coarse) ℝ)=0:=
    (Lava.marble_eq_zero_iff ..).mpr (MvPolynomial.homogeneousComponent_eq_zero _ _ (by simpa using active))
  change _-Lava.marble r (MvPolynomial.C _)=_
  rw [h,sub_zero]

end YM.Integration.WilsonConditionalTaylorWheelRawVacuum
end

