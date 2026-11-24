import YM.Integration.WilsonThermometerUnitFilingCoverPort

/-! The native cover tariff at a genuine edge midpoint, relative to the filed root. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverRoom
open Function Finset Lattice Gauge RG RegulatorIR Budget Budget.Packet Budget.Tuple Spatial Prim
open Geometry Motion Profiles Halo WilsonThermometerUnitFilingCoverChart
open scoped Classical BigOperators ENNReal
variable {G:Gauge} {S:Finset Cover}
local notation "P"=>WilsonThermometerUnitFilingCoverChart.patch G S

def mass (x:Cover):ℕ:=∑ i,(x i).natAbs
def plot (l:ℝ)(e:Foot G):Room:=Geometry.seat l e.1

theorem bound {l:ℝ}(hl:0<l)(p:Foot G): ‖plot l p‖≤l*(1+mass p.1.1):=by
  have hs:‖Motion.slide l p.1.1‖≤l*mass p.1.1:=by
    apply (pi_norm_le_iff_of_nonempty ..).mpr;intro i
    rw [Motion.slide_apply,norm_mul,Real.norm_of_nonneg hl.le,← norm_natAbs,Real.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ hl.le
    exact_mod_cast Finset.single_le_sum (f:=fun i=>(p.1.1 i).natAbs)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  have ht:‖glint l p.1.2‖≤l/2:=by
    apply (pi_norm_le_iff_of_nonempty ..).mpr;intro i
    unfold glint;simp only [Pi.smul_apply,Motion.slide_apply,Lattice.step_apply,Real.norm_eq_abs,smul_eq_mul]
    split_ifs <;> norm_num <;> linarith [abs_of_nonneg hl.le]
  unfold plot Geometry.seat
  exact (norm_add_le ..).trans ((add_le_add hs ht).trans (by linarith))

def reach {r:ℕ}(x:Fin r→↥(P)):ℝ:=1+∑ i,(mass (x i).1.1.1:ℝ)
def wage (u r:ℕ)(x:Fin r→↥(P)):ℝ:=(1+2*reach x)^u
theorem nonneg (u r:ℕ)(x:Fin r→↥(P)):0≤wage u r x:=by unfold wage reach;positivity
theorem perm (u r:ℕ)(e:Equiv.Perm (Fin r))(x:Fin r→↥(P)):wage u r (x∘e)=wage u r x:=by
  unfold wage reach
  rw [show (∑ i,(mass ((x∘e) i).1.1.1:ℝ))=∑ i,(mass (x i).1.1.1:ℝ) from
    Equiv.sum_comp e (fun i=>(mass (x i).1.1.1:ℝ))]

theorem tariff {l ρ:ℝ}(hl:0<l)(hr:0<ρ)(safe:l≤ρ)(u r:ℕ)(x:Fin r→↥(P)):
    ((Premium.rooted (Tariff.native ρ hr u) (0:Room)).uses
      ((plot l) ∘ placeFin (P))).width x≤ ENNReal.ofReal (wage u r x):=by
  let R:=reach x
  have positive : 1 ≤ R:=by
    dsimp [R,reach];linarith [Finset.sum_nonneg (s:=Finset.univ) (fun j _=>Nat.cast_nonneg (α:=ℝ) (mass (x j).val.1.1))]
  have high (i:Fin r): ‖plot l ((x i).val)‖≤l*R:=by
    apply (bound hl (x i).val).trans
    apply mul_le_mul_of_nonneg_left _ hl.le
    dsimp [R,reach];linarith [Finset.single_le_sum (f:=fun j:Fin r=>(mass (x j).val.1.1:ℝ))
      (fun _ _=>Nat.cast_nonneg _) (Finset.mem_univ i)]
  have room (d:ℝ)(dp:0≤d)(hd:d≤2*(l*R)):Tariff.amount ρ u d≤ ENNReal.ofReal (wage u r x):=by
    unfold Tariff.amount wage
    rw [← ENNReal.ofReal_pow (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (by positivity)
    change 1+d/ρ≤1+2*R
    have dx:d/ρ≤2*R:= (div_le_iff₀ hr).mpr (by
      linarith [mul_le_mul_of_nonneg_right safe (le_trans zero_le_one positive)])
    linarith
  apply Premium.width_le
  · apply Tariff.diameter_le
    · rw [← ENNReal.ofReal_one];apply ENNReal.ofReal_le_ofReal
      exact one_le_pow₀ (by change 1≤1+2*R;linarith)
    intro i j
    apply room _ dist_nonneg
    change dist (plot l (x i).val) (plot l (x j).val) ≤ _
    rw [dist_eq_norm]
    exact (norm_sub_le ..).trans (by linarith [high i,high j])
  · intro i
    apply room _ dist_nonneg
    change dist 0 (plot l (x i).val) ≤ _
    rw [dist_zero_left]
    linarith [high i, mul_nonneg hl.le (le_trans zero_le_one positive)]

end YM.Integration.WilsonThermometerUnitFilingCoverRoom
