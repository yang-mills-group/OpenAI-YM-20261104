import YM.Integration.WilsonThermometerUnitFilingMomentSale
import YM.Integration.WilsonOriginalRelativeMixedFields
import YM.Integration.WilsonThermometerUnitFilingTuition
/-! All polynomial moments of the true mixed derivatives of the single captured
group. The absolute value is taken after assembling the original signed field
at the same covered root, original copies and independently placed names. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingMomentPanel
open Function Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Earn Stationary
open Further.PhysicalPeriodLimitF933 Macrame FVA1Physical FVA1Physical.TwoReset
open WilsonOriginalRelativeMixedFields WilsonThermometerUnitFilingMomentSale
open scoped Classical BigOperators
variable {G:Gauge} {n N:Side} {V X ι:Type} [DecidableEq V] {o:Passport n V} {J:Census V}

def payment (h:n.val∣N.val) (M:ι→Row o J G X) (t:X) (s:J.Mode) (x:Site N)
    (j r a:ℕ) (u:Choice s.val n N G r):ℝ:=
  (1+2*(span h o s.val x u:ℝ))^a * ‖WilsonOriginalJointDeckMotion.entry r
    (joined h M t s x j u) u.2.2‖

theorem original (h:n.val∣N.val) (M:ι→Row o J G X) {w:V→ℝ} {grades:V→ℕ}
    {σ C:ℝ} {ord cap H:ℕ} (stock:Scene.Armada M w grades σ C ord cap H)
    {β δ:ℝ}(seed:0<σ)(tiny:0<δ)(late:Real.exp 1 ≤ β)(paid:Real.exp (σ⁻¹^2) ≤ β)
    (t:X)(s:J.Mode)(x:Site N)(j r a:ℕ)(cells:Finset (Choice s.val n N G r)):
    Poly.toll w s * ∑u∈cells,payment h M t s x j r a u ≤ price G r a δ * β^δ*C:=by
  let μ:ℝ:=min 1 σ
  have μ0:0<μ:=lt_min one_pos seed
  have small:μ ≤ 1:=min_le_left ..
  have paid':Real.exp (μ⁻¹^2) ≤ β:=by
    rcases le_total σ 1 with hs|hs
    · simpa only [μ,min_eq_right hs] using paid
    · simpa only [μ,min_eq_left hs,inv_one,one_pow] using late
  have salary:=WilsonThermometerUnitFilingTuition.narrow M stock (min_le_right 1 σ)
  have all:=WilsonOriginalRelativeMixedFields.original h M t s x salary μ0 j r
  have toll:0 ≤ Poly.toll w s:=prod_nonneg fun v _=>(stock.positive v).le
  have cash:0 ≤ C:=(tsum_nonneg ((stock.suggests 0).1)).trans (stock.suggests 0).2.2
  have loc:0 ≤ positionCost a μ:=by unfold positionCost; positivity
  have non (u:Choice s.val n N G r):0 ≤ payment h M t s x j r a u:=by unfold payment;positivity
  have back:∑u∈cells,payment h M t s x j r a u ≤ ∑u:Choice s.val n N G r,payment h M t s x j r a u:=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun u _ _=>non u)
  calc
    _ ≤ Poly.toll w s * ∑u:Choice s.val n N G r,payment h M t s x j r a u:=by gcongr
    _ ≤ positionCost a μ * ∑u:Choice s.val n N G r,Poly.toll w s*Real.exp ((μ/2)*span h o s.val x u)*
      ‖WilsonOriginalJointDeckMotion.entry r (joined h M t s x j u) u.2.2‖:=by
      rw [mul_sum,mul_sum];apply sum_le_sum
      intro u _
      have bound:=WilsonThermometerUnitFilingMomentSale.position μ0 small (span h o s.val x u) a
      rw [show μ*(span h o s.val x u:ℝ)/2=(μ/2)*(span h o s.val x u:ℝ) by ring] at bound
      unfold payment
      calc
        _ ≤ Poly.toll w s*(positionCost a μ*Real.exp ((μ/2)*span h o s.val x u)*
          ‖WilsonOriginalJointDeckMotion.entry r (joined h M t s x j u) u.2.2‖):=by gcongr
        _ = _:=by ring
    _ ≤ positionCost a μ*(WilsonOriginalSuspendedTensor.fee G μ r*C):=by gcongr
    _ = (WilsonOriginalSuspendedTensor.fee G μ r*positionCost a μ)*C:=by ring
    _ ≤ _:=by exact mul_le_mul_of_nonneg_right (WilsonThermometerUnitFilingMomentSale.original G r a μ0 small tiny paid') cash

end YM.Integration.WilsonThermometerUnitFilingMomentPanel
