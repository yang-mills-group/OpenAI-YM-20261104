import YM.Integration.WilsonOriginalGevreyFrequency
import YM.Integration.WilsonOriginalFourierReadback

/-! Use the actual localized physical Fourier integral on the box, with the
fixed profile loss chosen before every requested heat. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMeasuredGevreyBank
open Filter Lattice Wilson RG Source Extraction Table Spec
open PhysicalNext.Repeat.Legato RG17 Trace.Pilot PhysMS Climb UnitAddTorus
open scoped Topology BigOperators
open WilsonOriginalTestedFourierBank (Prices)
open WilsonOriginalFourierLattice (height)
open WilsonOriginalIntegerModeCut (size size_pow)

theorem original {G : Gauge} {warm : ℝ → ℝ} (clock : Coupling G warm)
    {d : ℕ} (f : ℝ → C(UnitAddTorus (Fin d),ℂ)) (coeff : ℕ → (Fin d → ℤ) → ℂ)
    (Dtest : ℕ) (A B D : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (hD : 0 ≤ D)
    (integrated : ∀ᶠ r : ℝ in trail, ∀ v, ∀ n : ℕ, let u := warm r
      ‖mFourierCoeff (f r) v‖ * (height v:ℝ)^n ≤ A*(u⁻¹)^2*Real.exp (D*(u⁻¹)^4)*
        ((B/u)^(2*n)*(n.factorial:ℝ)^2))
    (tested : ∀ q : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ r : ℝ in trail, ∀ v, let u := warm r
      ‖mFourierCoeff (f r) v-∑ e : Fin (q+1), (u:ℂ)^e.val*coeff e.val v‖ ≤
        C*u^q*(1+(height v:ℝ))^Dtest) :
    Nonempty (Prices warm (fun r v => mFourierCoeff (f r) v) coeff) := by
  refine ⟨⟨Dtest,2*A,D,Real.log 2/(2*B),by positivity,hD,by positivity,?_,?_⟩⟩
  · filter_upwards [clock.positive,integrated] with r hr byParts v
    refine WilsonOriginalGevreyFrequency.original (warm r) ((size v)^6) A B D hr
      (by positivity) hA hB _ ?_
    intro n
    have power : ((size v)^6)^(2*n) = (height v:ℝ)^n := by
      calc
        _ = (((size v)^6)^2)^n := pow_mul _ 2 n
        _ = _ := by
          have square : ((size v)^6)^2 = (height v:ℝ) := by rw [← pow_mul];exact size_pow v
          exact congrArg (fun x : ℝ => x^n) square
    rw [power];exact byParts v n
  · intro q
    obtain ⟨C,hC,price⟩ := tested q
    refine ⟨C,hC,?_⟩
    filter_upwards [price] with r allv v
    simpa only [size_pow] using allv v

end YM.Integration.WilsonOriginalMeasuredGevreyBank

