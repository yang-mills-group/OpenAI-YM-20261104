import YM.Integration.FVA1Physical.Wilson.ResetRate
import YM.Integration.LocalFormalAction

/-! The first nontrivial coupling-reset contribution to the inherited local
vacuum action, on the same selected trajectory and the same RG02 chain. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open RG Lattice YM.Wilson Exterior Tree Marker PhysicalNext.Repeat.Legato
open Comparison.RG02 Pert.Asymptotics
open scoped Classical BigOperators

def quadraticCaliber (a : ℝ) : Adjacent.Caliber :=
  ⟨fun i => (if i = 0 then 1 else 0) + (if i = 2 then a else 0), by simp⟩

theorem quadraticCaliber_even (a : ℝ) (r : ℕ) : (quadraticCaliber a).EvenK r := by
  intro i _ hi
  have h₀ : i ≠ 0 := by rintro rfl; simp at hi
  have h₂ : i ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd (2:ℕ)) hi
  simp [quadraticCaliber,h₀,h₂]

theorem quadraticCaliber_tariff (a g : ℝ) {r : ℕ} (hr : 2 ≤ r) :
    (quadraticCaliber a).tariff r g = 1 + g^2*a := by
  simp [Adjacent.Caliber.tariff,quadraticCaliber,mul_add,mul_ite,Finset.sum_add_distrib,
    Nat.lt_succ_of_le hr]

variable {G : Gauge} (A : Run G) {N j p r : ℕ}

/-- The measured caliber converts the actual fine coupling precisely to
the physical coarse inverse coupling, at every retained step. -/
theorem physical_caliber_temperature (hj : j < N) (hr : 2 ≤ r) :
    let β := A.family.path.β N p
    let g := regulatorRun A.family N p (j+1)
    Integral.temperature (((quadraticCaliber (β j-β (j+1))).direct r).enter g) = β j := by
  dsimp only
  let β := A.family.path.β N p
  let g := regulatorRun A.family N p (j+1)
  have h₁ : 0 < β (j+1) := Overlay.beta_positive A.makes.wilson hj
  have h₀ : 0 < β j := Overlay.beta_positive A.makes.wilson hj.le
  have hq : g^2 = (β (j+1))⁻¹ := by
    change (Real.sqrt (β (j+1)))⁻¹ ^ (2:ℕ) = _
    rw [inv_pow,Real.sq_sqrt h₁.le]
  have ratio : 1+g^2*(β j-β (j+1)) = β j / β (j+1) := by rw [hq]; field_simp; ring
  change Integral.temperature (((quadraticCaliber (β j-β (j+1))).direct r).enter g) = β j
  rw [Adjacent.Caliber.real_ratio, quadraticCaliber_tariff _ _ hr,ratio,
    if_pos (div_nonneg h₀.le h₁.le), Integral.temperature, hq, inv_inv]
  field_simp

private theorem physical_delta_price (hs : G.Simple) (hj : j < N) :
    |A.family.path.β N p j - A.family.path.β N p (j+1) - (RunFormalChain.fromRun A).kin.alpha N j| ≤
      resetPrice A j := by
  obtain ⟨l,v,Q,K,x,he,hf,_⟩ := A.carries N j p hj
  obtain ⟨_,h₁,h₂,_⟩ := (K.moves hs hj).2 x.val x.property
  change |((Extra.Histories.Issue.trail A.T).rep N p j).beta -
    ((Extra.Histories.Issue.trail A.T).rep N p (j+1)).beta - A.alloy.B.kin.alpha N j| ≤ _
  rw [he,hf]
  rw [UVNext.CouplingReset.predictor,sub_add_eq_sub_sub] at h₁ h₂
  exact le_min h₁ ((le_div_iff₀ (pow_pos (A.alloy.B.a.budget j).threshold_pos _)).mpr
    (by simpa only [mul_comm] using h₂))

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} (D : LocalFormal.Datum A.family R)

/-- Exact identity of coarse-field functions, for all inherited input colors.
It identifies the entire order-two change. The only surviving factor is the
discrepancy of the physical and formal reset multiplied by the single
leading quadratic action of this same formal kernel. -/
theorem second_reset_difference (hr : 2 ≤ r) :
    let L := RunFormalChain.fromRun A
    let α := L.kin.alpha D.cutoff D.level
    let β := A.family.path.β D.cutoff D.period
    let γ := β D.level - β (D.level+1)
    D.resetVacuumAction L (quadraticCaliber γ) r 2 -
      D.resetVacuumAction L (quadraticCaliber α) r 2 =
        (↑(α-γ) : ℂ) • D.vacuumAction L r 0 := by
  dsimp only
  rw [D.resetVacuumAction_two_eq _ _ _ (quadraticCaliber_even _ r) hr,
      D.resetVacuumAction_two_eq _ _ _ (quadraticCaliber_even _ r) hr]
  have hc (a : ℝ) : (quadraticCaliber a).measure 2 = a := by simp [quadraticCaliber]
  simp only [hc,Complex.ofReal_sub,sub_smul]
  abel

/-- A quantitative order-two change on the actual inherited RG02 input,
uniformly in the period, forest and input colors after dividing out the
explicit size of the common quadratic action at the chosen coarse field. -/
theorem second_reset_bound (hs : G.Simple) (hr : 2 ≤ r) (x : fieldDir G (A.family.side D.level D.period) 1) :
    let L := RunFormalChain.fromRun A
    let α := L.kin.alpha D.cutoff D.level
    let β := A.family.path.β D.cutoff D.period
    let γ := β D.level - β (D.level+1)
    ‖D.resetVacuumAction L (quadraticCaliber γ) r 2 x - D.resetVacuumAction L (quadraticCaliber α) r 2 x‖ ≤
      resetPrice A D.level * ‖D.vacuumAction L r 0 x‖ := by
  dsimp only
  have he := congrFun (second_reset_difference A D hr) x
  rw [Pi.sub_apply,Pi.smul_apply] at he
  rw [he,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]
  exact mul_le_mul_of_nonneg_right (physical_delta_price A hs D.below) (norm_nonneg _)

end YM.Integration.FVA1Physical.Wilson
