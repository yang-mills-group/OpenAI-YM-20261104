import YM.Integration.WilsonThermometerWeightedCapture
import YM.Integration.WilsonThermometerCenteredWeight
import YM.Integration.WilsonCenteredFiledAtoms

/-! One marked numerator for the complete ordinary roster on the native
Wilson deposit. Every partition and the inverse bank share the same aperture. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPlantedOrdinaryScalar
noncomputable section
open Function Finset Lattice Wilson RG Marker Multi QuadraticLocal Push.Local Source Labels Extra.Histories
open Planned.GuardedAtom Primitives.GCC.Anchor
open WilsonCenteredFiledAtoms WilsonThermometerCenteredAlgebra WilsonThermometerWeightedCapture
open WilsonFiniteOrdinaryInverse
open scoped Classical BigOperators
variable {G : Gauge} {n : Side} {d : ℕ} {F : Frame G d}
local notation "J" => Stock.census (Fin 3)
local instance : Nonempty ((J).Mode) := ⟨(J).quiet⟩

theorem original (P : Rep G n) (S : SectionData F) (Y : Hol G) (y : Site n)
    (w : Fin 3→ℝ) (wpos : ∀v,0<w v) (Q : Poly (J)) (V : Config G n→Poly (J))
    {κ σ c Λ δ η : ℝ} (hk : 0<κ) (law : P.Lawful σ c Λ δ η)
    {g A : ℝ} (gp : 0<g) (small : g≤1) (A0 : 0≤A) (e loss : ℕ)
    (fullPrice : g^loss≤Poly.toll w full) (inverse : Poly.price (fun v=>g*w v) (inverseMass Q)≤fee J)
    (fare : (J).Mode→ℝ) (each : ∀s,Poly.toll w s*fare s≤A*(g⁻¹)^e)
    (read : ∀s,Store P S Y y κ (fare s) (fun U=>(P.eval U:ℂ)*(V U).part s)) :
    Store P S Y y κ (fee (J)*A/g^(3+loss+e)) (fun U=>(P.eval U:ℂ)*(total (V U) Q).part full) := by
  choose H fit paid issued using read
  let row (s : (J).Mode):=stretch (weight Q s) (H s)
  have proved (s : (J).Mode) : (row s).remBound y P κ (‖weight Q s‖*fare s) := stretch_rem _ (paid s)
  have valid := merge_format (code ((J).Mode)) row (fun s=>stretch_format _ (fit s))
  have charged := (merge_budget (code ((J).Mode)) row hk proved (hasSum_fintype _).summable).1
  have feePoly:=WilsonThermometerCenteredWeight.original Q w wpos gp small loss fullPrice inverse
  have invoice : (∑s:(J).Mode, ‖weight Q s‖/Poly.toll w s)≤fee J/g^(3+loss) :=
    (le_div_iff₀ (pow_pos gp _)).mpr (by simpa only [mul_comm] using feePoly)
  have per (s : (J).Mode) : fare s≤A*(g⁻¹)^e/Poly.toll w s :=
    (le_div_iff₀ (show 0<Poly.toll w s from prod_pos fun v _=>wpos v)).mpr
      ((mul_comm (fare s) (Poly.toll w s)).le.trans (each s))
  have bill : (∑s:(J).Mode,‖weight Q s‖*fare s)≤fee J*A/g^(3+loss+e) := calc
    _ ≤ ∑s:(J).Mode,(‖weight Q s‖/Poly.toll w s)*(A*(g⁻¹)^e) :=sum_le_sum fun s _=>
      (mul_le_mul_of_nonneg_left (per s) (norm_nonneg _)).trans_eq (by ring)
    _ = (∑s:(J).Mode,‖weight Q s‖/Poly.toll w s)*(A*(g⁻¹)^e) := (Finset.sum_mul ..).symm
    _ ≤ (fee J/g^(3+loss))*(A*(g⁻¹)^e) := mul_le_mul_of_nonneg_right invoice (by positivity)
    _ = _ := by rw [pow_add];ring
  have realBound : (merge (code ((J).Mode)) row).remBound y P κ (∑s,‖weight Q s‖*fare s) := by
    simpa only [tsum_fintype] using charged
  obtain ⟨a₀,a₁,n₀,n₁,sum,rest⟩:=realBound
  refine ⟨_,valid,⟨a₀,a₁,n₀,n₁,sum.trans bill,rest⟩,?_⟩
  intro U
  have same:=merge_density (code ((J).Mode)) row hk law proved (hasSum_fintype _).summable
    (hasSum_fintype _).summable S U
  change (merge (code ((J).Mode)) row).density y S P U = (P.eval U:ℂ)*(total (V U) Q).part full
  rw [←same.tsum_eq,tsum_fintype,WilsonThermometerCenteredAlgebra.affine,Finset.mul_sum]
  apply sum_congr rfl
  intro s _
  change (stretch _ _).density y S P U=_
  rw [stretch_density,issued]
  ring

end
end YM.Integration.WilsonPlantedOrdinaryScalar
