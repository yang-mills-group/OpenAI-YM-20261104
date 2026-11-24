import YM.Integration.KineticGerm
import YM.IterationFour.Kinetic
import YM.FullVolume.Cross

/-! Native kinetic calibration on one original Run, using only row-wave
identity near zero. Any fixed polynomial enlargement of the quote is paid by
the existing same-Run mesh theorem. The actual quote and germ attachments are
retained as explicit internal consumer obligations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ActualRunKineticGerm
open Function Filter Set Lattice Wilson MeasureTheory RG
open PhysicalNext.Repeat.Legato IterationFour
open scoped Topology BigOperators
variable {G : Gauge} (R : Run G)

/-- The same original trajectory pays every fixed polynomial quote and every
requested inverse-power accuracy; no equality of the beta parameters is used. -/
theorem rigidity (hG : G.Simple) (k q : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (N p : ℕ), m ≤ N → ∀ Q : RG.Rep G (R.family.side m p),
      (∀ c : G.Color, ‖c‖ = 1 → ∀ b : Bool, ∀ᶠ t : ℝ in 𝓝 0,
        Q.eval (AnalyticBridge.VerifiedReset.line (Pert.Kinetic.rowWave c b) t) =
          (R.family.path.rep N p m).eval
            (AnalyticBridge.VerifiedReset.line (Pert.Kinetic.rowWave c b) t)) →
      ∀ σ L Λ δ w, Q.Lawful σ L Λ δ w →
      Pert.Kinetic.Quotes Q.p σ L Λ δ (Kinetic.price R.family m ^ (k+1)) →
      |Q.beta-R.family.path.β N p m| ≤ (Kinetic.price R.family m ^ q)⁻¹ := by
  let d : ℝ := Fintype.card PlaqAxes
  let e : ℕ := (k+1)*9
  filter_upwards [Kinetic.quote_eventually R.family hG,
    Kinetic.mesh_payment R.family hG (2*(Real.pi^2*(2*d))) e,
    Kinetic.mesh_payment R.family hG (4*Real.pi^2 * Pert.Kinetic.coefK) (e+q)]
      with i he h1 h2 N p hi Q hr σ L Λ δ w hl hp
  let n := R.family.side i p
  have hs : R.family.path.Conv N p i := R.makes.wilson.represents N p i hi
  have hpow : Kinetic.price R.family i ≤ Kinetic.price R.family i ^ (k+1) := by
    simpa only [pow_one] using
      (pow_le_pow_right₀ he.pos (show 1 ≤ k+1 by omega))
  have hb : |R.family.path.β N p i| ≤ Kinetic.price R.family i ^ (k+1) := by
    rw [abs_of_pos ?pos]
    case pos =>
      exact (half_pos (zero_lt_one.trans ((R.family.path.levels).fits.delayed i))).trans_le hs.band.1
    exact (hs.band.2.trans (Kinetic.two_hat_le R.family i)).trans hpow
  have hv : 4 ≤ n.val := by
    have h := (R.family.path.levels).fits.sizeT i p
    change _ ≤ n.val at h
    omega
  have hpow9 : (Kinetic.price R.family i ^ (k+1))^9 = Kinetic.price R.family i ^ e := by
    rw [← pow_mul]
  have hpay : Real.pi^2 * Pert.Full.mesh n *
      (2*d * (Kinetic.price R.family i ^ (k+1))^9) ≤ 1/2 := by
    rw [hpow9]
    apply (le_div_iff₀ zero_lt_two).2
    refine Eq.trans_le ?_ (h1 p)
    ring
  have hδ := KineticGerm.small_beta hG
    (fun c hc b => by
      filter_upwards [hr c hc b] with t ht
      exact ht.symm) hl hs.good
    (hs.vac.symm ▸ Pert.Kinetic.quotes_le hpow he) hp hv hb hpay
  rw [abs_sub_comm]
  refine hδ.trans ?_
  rw [hpow9, ← one_div]
  apply (le_div_iff₀ (pow_pos (Kinetic.price_pos R.family i) q)).2
  refine Eq.trans_le ?_ (h2 p)
  rw [pow_add]
  ring

end YM.Integration.ActualRunKineticGerm
end
