import YM.Integration.WilsonLocalKernelTemperature
import YM.Integration.WilsonLocalKernelLaplace

/-! All coefficients of joint exponential probes of the true Wilson noise
prices, with independent source strengths on the observed links. -/
noncomputable section
namespace YM.Integration.WilsonLocalKernelPriceExpansion
open YM RG RG02 RG02.Asym Lattice Wilson MeasureTheory WilsonKernelCoupling
open WilsonLocalKernelLaplace WilsonLocalKernelTemperature
open PertExtension.Series PertExtension.Series.Tested PowerSeries Filter
open scoped BigOperators Topology
variable {c f : Side} (S : StepData c f) {G : Gauge}
variable {ι : Type*} [Fintype ι]

def series (G : Gauge) (r : ι → ℝ) : PowerSeries ℂ :=
  ∏ j, WilsonLocalKernelTemperature.series S G (r j)

theorem finite (G : Gauge) (r : ι → ℝ) (hr : ∀ j, 0 < r j) :
    Near (fun t => ∏ j, ratio S G (r j) t) (series S G r) := by
  classical
  have h (B : Finset ι) : Near (fun t => ∏ j ∈ B, ratio S G (r j) t)
      (∏ j ∈ B, WilsonLocalKernelTemperature.series S G (r j)) := by
    induction B using Finset.induction_on with
    | empty => simpa using (Near.fixed (1 : ℂ))
    | @insert i B hi ih =>
      simp only [Finset.prod_insert hi]
      exact Near.mult (WilsonLocalKernelTemperature.all_orders S G (hr i)) ih
  exact h Finset.univ

def observation (A : Finset (Edge (Site c))) (e : A ≃ ι) (r : ι → ℝ) (t : ℝ) (U : Config G f) : ℝ :=
  ∑ z, S.likelihood U z * ∫ V, S.noise (t^2)⁻¹ (S.prediction U z) V *
    tilt S A (t^2)⁻¹ (fun i => ((r (e i)*t)^2)⁻¹) (S.prediction U z) (readLinks A V) ∂prior G c

theorem measured (h : S.patch.Branches S.kernel G) (A : Finset (Edge (Site c)))
    (e : A ≃ ι) (r : ι → ℝ) (t : ℝ) (U : Config G f) :
    (observation S A e r t U : ℂ) = ∏ j, ratio S G (r j) t := by
  unfold observation
  rw [joint S h]
  push_cast
  exact Equiv.prod_comp e (fun j => ratio S G (r j) t)

theorem calendar {G : Gauge} (D : Calendar G) (r : ι → ℝ) (hr : ∀ j, 0 < r j) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ (t : ℝ) in Tested.germ, ∀ m p : ℕ,
      (D.op m p).patch.Branches D.kernel G →
      ∀ (A : Finset (Edge (Site (D.schedule.side m p)))) (e : A ≃ ι)
        (U : Config G (D.schedule.side (m+1) p)),
        ‖(observation (D.op m p) A e r t U : ℂ) -
          peval (fun j => coeff j (series (D.op 0 0) G r)) n t‖ ≤ C*t^(n+1) := by
  obtain ⟨C,hC,H⟩ := finite (D.op 0 0) G r hr n
  refine ⟨C,hC,H.mono ?_⟩
  intro t ht m p h A e U
  rw [measured (D.op m p) h A e r t U]
  exact ht

theorem gaussian (G : Gauge) (r : ι → ℝ) :
    coeff 0 (series S G r) = ∏ j, (r j : ℂ)^(Friction.cardinal G) := by
  rw [coeff_zero_eq_constantCoeff_apply, series, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [← coeff_zero_eq_constantCoeff_apply, WilsonLocalKernelTemperature.leading]

end YM.Integration.WilsonLocalKernelPriceExpansion
