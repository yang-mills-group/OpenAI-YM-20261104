import YM.Integration.WilsonThermometerUnitFilingRelativeChamber
import YM.Integration.WilsonThermometerCenteredWeight

/-! Restoring the finite signed inverse costs a single coupling pole on each authentic original
relative cell. The remaining factor is the true occupied-arm fee in the issued marker radii. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingArmPrice
open Function Filter Set MeasureTheory Finset Lattice Wilson Labels RG Source Extra.Histories
open Push Marker PhysicalNext.Repeat.Legato MergeProof MergeProof.Accent FVA1
open OriginalForcedAddresses RG12 RG16 RG16.Literal Trace.Physical.GermGraph
open OPE.Cards Primitives.GCC.Anchor Climb WilsonPositionThermometerCapStation
open WilsonThermometerCourseIntake WilsonThermometerUnitFilingCylinder WilsonThermometerUnitFilingFeed
open WilsonThermometerCenteredAlgebra WilsonThermometerAlignedCells
open XSpace XSpace.Rose Cells Push.GridApprox WilsonThermometerWeightedCapture
open private sum_triples from YM.Integration.WilsonThermometerAlignedCells
open private admitted from YM.Integration.WilsonThermometerUnitFilingDeposit
open scoped BigOperators Topology Classical
open WilsonThermometerCenteredWeight
open WilsonCenteredCloseOccupiedSale WilsonCenteredCloseCaptureWallet
open WilsonThermometerUnitFilingRelative (Grid)
local notation "J₃" => Stock.census (Fin 3)

theorem cell (Q:Poly J₃) (w:Fin 3→ℝ) (positive:∀i,0<w i) {g B:ℝ} (gp:0<g) (small:g≤1)
    (loss:ℕ) (joint:g^loss≤Poly.toll w full)
    (funded:Poly.price (fun i=>g*w i) (inverseMass Q) ≤ WilsonFiniteOrdinaryInverse.fee J₃) (bp:0≤B)
    (fare:(J₃).Mode→ℝ) (current:∀s,Poly.toll w s*fare s≤B):
    ∑s:(J₃).Mode,‖wallet Q s‖*fare s≤(WilsonFiniteOrdinaryInverse.fee J₃/g^(3+loss))*B:=by
  have paid:=WilsonThermometerCenteredWeight.original Q w positive gp small loss joint funded
  have inv:(∑ s:(J₃).Mode,‖weight Q s‖/Poly.toll w s)≤WilsonFiniteOrdinaryInverse.fee J₃/g^(3+loss):=
    (le_div_iff₀ (pow_pos gp _)).2 (by rwa [mul_comm])
  calc
    _≤∑s:(J₃).Mode,(‖weight Q s‖/Poly.toll w s)*B:=by
      apply Finset.sum_le_sum;intro s _
      have wp:0<Poly.toll w s:=Finset.prod_pos (fun i _=>positive i)
      have line:fare s≤B/Poly.toll w s:=(le_div_iff₀ wp).2 (by rw [mul_comm];exact current s)
      calc
        _≤‖weight Q s‖*(B/Poly.toll w s):=mul_le_mul_of_nonneg_left line (norm_nonneg _)
        _=_:=by ring
    _=(∑s:(J₃).Mode,‖weight Q s‖/Poly.toll w s)*B:=(Finset.sum_mul ..).symm
    _≤_:=mul_le_mul_of_nonneg_right inv bp

variable {G:Gauge} (R:Run G) (z:UVIndex) (r:ℝ) (φ:Test 3)
local notation "active!" => Grid R z r φ
local notation "μ!" => WilsonThermometerAlignedCells.mass (R:=R) r z φ

theorem original (Q:active!→Poly J₃) (w:active!→Fin 3→ℝ) (positive:∀c i,0<w c i) {g M:ℝ}
    (gp:0<g) (small:g≤1) (loss:ℕ) (joint:∀c,g^loss≤Poly.toll (w c) full)
    (funded:∀c,Poly.price (fun i=>g*w c i) (inverseMass (Q c)) ≤ WilsonFiniteOrdinaryInverse.fee J₃)
    (fare:active!→(J₃).Mode→ℝ) (mp:0≤M) (current:∀c s,Poly.toll (w c) s*fare c s≤M):
    ∑ c:active!,∑s:(J₃).Mode,‖μ! c.val*wallet (Q c) s‖*fare c s ≤
      (∫x:Points 3,‖φ x‖)*(WilsonFiniteOrdinaryInverse.fee J₃/g^(3+loss))*M:=by
  have vp:0≤WilsonFiniteOrdinaryInverse.fee J₃:=by
    unfold WilsonFiniteOrdinaryInverse.fee WilsonFiniteOrdinaryInverse.room
    exact Finset.sum_nonneg (fun i _=>pow_nonneg (add_nonneg zero_le_one
      (Finset.sum_nonneg (fun a _=>by positivity))) i)
  calc
    _≤∑ c:active!,‖μ! c.val‖*((WilsonFiniteOrdinaryInverse.fee J₃/g^(3+loss))*M):=by
      apply Finset.sum_le_sum;intro c _
      simp_rw [norm_mul,mul_assoc,←Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (cell (Q c) (w c) (positive c) gp small loss (joint c)
        (funded c) mp (fare c) (current c)) (norm_nonneg _)
    _=(∑c:active!,‖μ! c.val‖)*((WilsonFiniteOrdinaryInverse.fee J₃/g^(3+loss))*M):=(Finset.sum_mul ..).symm
    _≤(∫x:Points 3,‖φ x‖)*((WilsonFiniteOrdinaryInverse.fee J₃/g^(3+loss))*M):=
      mul_le_mul_of_nonneg_right (WilsonThermometerSupportedCells.variation R r φ)
        (mul_nonneg (div_nonneg vp (pow_nonneg gp.le _)) mp)
    _=_:=by ring

end YM.Integration.WilsonThermometerUnitFilingArmPrice
