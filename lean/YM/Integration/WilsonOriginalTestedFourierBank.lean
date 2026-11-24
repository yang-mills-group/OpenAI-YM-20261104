import YM.Integration.WilsonOriginalIntegerModeCut
import YM.Integration.WilsonOriginalAnalyticHeatCoefficients

/-! Use the signed distribution estimate at every order on the same
coefficient family. All sampling radii see the measured physical clock.
The spatial loss is chosen before the heat order. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTestedFourierBank
open Filter Function Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb
open scoped Topology BigOperators
open WilsonOriginalIntegerModeCut (size)
open WilsonOriginalDatedJetSamples (date)

structure Prices {d : ℕ} (warm : ℝ → ℝ) (read : ℝ → (Fin d → ℤ) → ℂ)
    (coeff : ℕ → (Fin d → ℤ) → ℂ) where
  loss : ℕ
  A : ℝ
  D : ℝ
  c : ℝ
  prefactor : 0 ≤ A
  growth : 0 ≤ D
  width : 0 < c
  analytic : ∀ᶠ r : ℝ in trail, ∀ v, let u := warm r
    ‖read r v‖ ≤ A*(u⁻¹)^2*Real.exp (D*(u⁻¹)^4-c*(size v)^6*u)
  tested : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in trail, ∀ v, let u := warm r
    ‖read r v-∑ e : Fin (q+1), (u:ℂ)^e.val*coeff e.val v‖ ≤ C*u^q*(1+(size v)^12)^loss

theorem dates {n : ℕ} (i : Fin n) : Tendsto (fun s : ℝ => date s i) atTop trail := by
  let m : ℝ := i.val+1
  have hm : 0 < m := by dsimp [m];positivity
  have mulDate : Tendsto (fun s : ℝ => s/m) atTop atTop := by
    simpa only [div_eq_inv_mul,id_eq] using
      (Tendsto.const_mul_atTop (inv_pos.mpr hm) (tendsto_id : Tendsto id (atTop : Filter ℝ) atTop))
  exact WilsonOriginalDatedJetSamples.radii.comp mulDate

/-- One bound for the full finite initial set of published heat coefficients
on every signed frequency tuple in the box, at arbitrary decay power. -/
theorem original {G : Gauge} {d : ℕ} {warm : ℝ → ℝ} (hG : G.Simple) (paid : Coupling G warm)
    {read : ℝ → (Fin d → ℤ) → ℂ} {coeff : ℕ → (Fin d → ℤ) → ℂ}
    (b : Prices warm read coeff) (J k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s : ℝ in atTop, ∀ v : Fin d → ℤ, size v = s → ∀ e : Fin (J+1),
      s^k*‖coeff e.val v‖ ≤ ε := by
  let q := k+J+12*b.loss+1
  obtain ⟨C,hC,test⟩ := b.tested q
  have bank : ∀ᶠ s : ℝ in atTop, ∀ i : Fin (q+1), ∀ v, let u := warm (date s i)
      ‖read (date s i) v‖ ≤ b.A*(u⁻¹)^2*Real.exp (b.D*(u⁻¹)^4-b.c*(size v)^6*u) := by
    exact eventually_all.mpr fun i => (dates i).eventually b.analytic
  have crop : ∀ᶠ s : ℝ in atTop, ∀ i : Fin (q+1), ∀ v, let u := warm (date s i)
      ‖read (date s i) v - ∑ j : Fin (q+1), (u:ℂ)^j.val*coeff j.val v‖ ≤
        C*u^q*(1+(size v)^12)^b.loss :=
    eventually_all.mpr fun i => (dates i).eventually test
  have one (e : Fin (J+1)) : ∀ᶠ s : ℝ in atTop, ∀ v : Fin d → ℤ, size v = s →
      s^k*‖coeff e.val v‖ ≤ ε := by
    let j : Fin (q+1) := ⟨e.val,by dsimp [q];omega⟩
    have order : k+j.val+12*b.loss+1 ≤ q := by dsimp [q,j];omega
    have priced := WilsonOriginalAnalyticHeatCoefficients.original hG paid q k b.loss j order
      b.A b.D b.c C b.prefactor b.growth b.width hC hε
    filter_upwards [bank,crop,priced] with s bySize signed fit v hv
    exact fit (fun a => coeff a.val v) (fun i => read (date s i) v)
      (fun i => hv ▸ bySize i v) (fun i => hv ▸ signed i v)
  filter_upwards [eventually_all.mpr one] with s allSizes v hv e
  exact allSizes e v hv

end YM.Integration.WilsonOriginalTestedFourierBank

