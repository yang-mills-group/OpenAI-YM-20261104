import YM.Integration.FVA1Physical.Wilson.SecondReset

/-! Regular derivatives of the measured second-order RG02 reset on a retained step. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open RG Lattice YM.Wilson Exterior Tree Marker PhysicalNext.Repeat.Legato Comparison.RG02
open scoped Classical ContDiff

variable {G : Gauge} (A : Run G)

def measuredReset (N j p : ℕ) : ℝ := A.family.path.β N p j - A.family.path.β N p (j+1)

theorem measured_reset_price (hs : G.Simple) {N j p : ℕ} (hj : j < N) :
    |(RunFormalChain.fromRun A).kin.alpha N j - measuredReset A N j p| ≤ resetPrice A j := by
  rw [abs_sub_comm]
  obtain ⟨l,v,Q,K,x,he,hf,_⟩ := A.carries N j p hj
  obtain ⟨_,h₁,h₂,_⟩ := (K.moves hs hj).2 x.val x.property
  change |((Extra.Histories.Issue.trail A.T).rep N p j).beta -
    ((Extra.Histories.Issue.trail A.T).rep N p (j+1)).beta - A.alloy.B.kin.alpha N j| ≤ _
  rw [he,hf]
  rw [UVNext.CouplingReset.predictor,sub_add_eq_sub_sub] at h₁ h₂
  exact le_min h₁ ((le_div_iff₀ (pow_pos (A.alloy.B.a.budget j).threshold_pos _)).mpr
    (by simpa only [mul_comm] using h₂))

variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V}
    (D : LocalFormal.Datum A.family R)

def localResetDiscrepancy (r : ℕ) : fieldDir G (A.family.side D.level D.period) 1 → ℂ :=
  let L := RunFormalChain.fromRun A
  D.resetVacuumAction L (quadraticCaliber (measuredReset A D.cutoff D.level D.period)) r 2 -
    D.resetVacuumAction L (quadraticCaliber (L.kin.alpha D.cutoff D.level)) r 2

/-- The second-order discrepancy is a field polynomial of degree at most two at every
background. Its full derivative tensor, with arbitrary real, independently chosen
directions, is exactly the measured scalar times the derivative of the quadratic term. -/
theorem local_reset_jets {r : ℕ} (hr : 2 ≤ r) (k : ℕ)
    (x : fieldDir G (A.family.side D.level D.period) 1) :
    let L := RunFormalChain.fromRun A
    iteratedFDeriv ℝ k (localResetDiscrepancy A D r) x =
      (((L.kin.alpha D.cutoff D.level - measuredReset A D.cutoff D.level D.period : ℝ) : ℂ)) •
        iteratedFDeriv ℝ k (D.vacuumAction L r 0) x := by
  dsimp only
  have he : localResetDiscrepancy A D r =
      ((((RunFormalChain.fromRun A).kin.alpha D.cutoff D.level - measuredReset A D.cutoff D.level D.period : ℝ) : ℂ)) •
        D.vacuumAction (RunFormalChain.fromRun A) r 0 := second_reset_difference A D hr
  rw [he,
    iteratedFDeriv_const_smul_apply ((D.vacuumAction_degree _ r 0 (Nat.zero_le _)).smooth.contDiffAt.of_le le_top)]

/-- Higher derivatives vanish at every retained field. -/
theorem local_reset_high_jets {r : ℕ} (hr : 2 ≤ r) {k : ℕ} (hk : 2 < k)
    (x : fieldDir G (A.family.side D.level D.period) 1) :
    iteratedFDeriv ℝ k (localResetDiscrepancy A D r) x = 0 := by
  rw [local_reset_jets A D hr k x,
    (D.vacuumAction_degree _ r 0 (Nat.zero_le _)).high k (by omega) x, smul_zero]

/-- The same period-independent scalar controls every regular derivative in operator norm. -/
theorem local_reset_jet_price (hs : G.Simple) {r : ℕ} (hr : 2 ≤ r) (k : ℕ)
    (x : fieldDir G (A.family.side D.level D.period) 1) :
    ‖iteratedFDeriv ℝ k (localResetDiscrepancy A D r) x‖ ≤
      resetPrice A D.level * ‖iteratedFDeriv ℝ k (D.vacuumAction (RunFormalChain.fromRun A) r 0) x‖ := by
  rw [local_reset_jets A D hr k x, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (measured_reset_price A hs D.below) (norm_nonneg _)

end YM.Integration.FVA1Physical.Wilson
