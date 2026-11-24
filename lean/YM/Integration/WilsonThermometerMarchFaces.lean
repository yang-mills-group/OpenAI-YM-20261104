import YM.Integration.WilsonThermometerOwnOffsetRadii
import YM.Integration.WilsonOriginalThermometerFineHarvest
import YM.Integration.WilsonAdmissionScale

/-! Restore the actual original migrating radii on all seven displaced faces. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerMarchFaces
open Function Filter Finset Lattice Wilson RG RG05Readout Marker PhysicalNext.Repeat.Legato
open WilsonThermometerOwnOffsetRadii WilsonOriginalThermometerFineCover
open WilsonOriginalThermometerFineHarvest WilsonSeparatedOriginalThermometerCells
open scoped BigOperators Topology Classical
variable {G:Gauge} (R:Run G)
local notation "β" => R.family.path.levels.clock.hatBeta

def inverse (t m i : ℕ) (s:(Stock.census (Fin 3)).Mode) :=
  (Poly.toll (fun _ : Fin 3=>radius R t m i) s)⁻¹

theorem slot (simple:G.Simple) (t m i:ℕ) (hi : m ≤ i) :
    (radius R t m i)⁻¹ ≤ β i^(t+(i-m)) := by
  induction i,hi using Nat.le_induction with
  | base=>
    rw [radius_start,inv_inv,Nat.sub_self,Nat.add_zero]
    exact le_rfl
  | succ j hj ih =>
    have positive (i:ℕ):0<β i:=zero_lt_one.trans (R.family.path.levels.fits.delayed i)
    have next:β j≤β (j+1):=(Real.log_le_log_iff (positive _) (positive _)).mp
      (WilsonAdmissionScale.logarithm_monotone R.family.path.levels simple (Nat.le_succ j))
    rw [radius_next R t m j hj,mul_inv,inv_inv]
    have higher:=ih.trans (pow_le_pow_left₀ (positive j).le next _)
    have step:t+(j+1-m)=t+(j-m)+1:=by omega
    change β (j+1)*(radius R t m j)⁻¹ ≤ β (j+1)^(t+(j+1-m))
    rw [step,pow_succ,mul_comm (β (j+1))]
    exact mul_le_mul_of_nonneg_right higher (positive _).le

theorem face (simple:G.Simple) (t m i:ℕ) (hi : m ≤ i) (s:(Stock.census (Fin 3)).Mode) :
    inverse R t m i s ≤ β i^(3*(t+1)*(i-m+1)) := by
  have positive:0 < radius R t m i:=radius_pos R t m i hi
  have room:s.val.card≤3:=by simpa using Finset.card_le_univ s.val
  have base:1≤β i:=(R.family.path.levels.fits.delayed i).le
  have a:=slot R simple t m i hi
  have e:(t+(i-m))*s.val.card ≤ 3*(t+1)*(i-m+1) := calc
    _ ≤ (t+(i-m))*3:=Nat.mul_le_mul_left _ room
    _ ≤ _ := by nlinarith
  calc
    _ = ((radius R t m i)⁻¹)^s.val.card := by simp [inverse,Poly.toll]
    _ ≤ (β i^(t+(i-m)))^s.val.card := pow_le_pow_left₀ (inv_pos.mpr positive).le a _
    _ = _ := (pow_mul _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ base e

end YM.Integration.WilsonThermometerMarchFaces
end
