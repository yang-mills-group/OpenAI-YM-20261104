import YM.Integration.WilsonConditionalTaylorThermalFourthConnected

/-! The two identical cubic perturbations contribute a fourth cumulant.
Its disconnected contractions cancel on the original centered Gaussian. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalCubicPair
open MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalCumulant
open scoped Classical BigOperators

def half {E : Type*} (F : E→ℝ) : E→ℝ := fun x=>F x/2

def fourth {E : Type*} (A : (E→ℝ)→ℝ) (F Q H : E→ℝ) :=
  A (((F*Q)*H)*H)-A F*A ((Q*H)*H)-A Q*A ((F*H)*H)-2*A H*A ((F*Q)*H)-
    A (F*Q)*A (H*H)-2*A (F*H)*A (Q*H)+2*A (F*Q)*(A H)^2+
    4*A (F*H)*A Q*A H+4*A (Q*H)*A F*A H+2*A (H*H)*A F*A Q-6*A F*A Q*(A H)^2

section averaging
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (Γ : Law E) (μ : Measure E) [μ.HasTemperateGrowth]

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.HasTemperateGrowth] in
theorem scaled (F : E→ℝ) : Γ.average μ (half F) = Γ.average μ F/2 := by
  unfold Law.average
  rw [show (half F)*Γ.kern=half (F*Γ.kern) by funext x;simp [half];ring]
  simp only [half,integral_div];ring

theorem combineThird {F Q H K : E→ℝ} (f : priced F) (q : priced Q) (h : priced H) (k : priced K) :
    third (Γ.average μ) F Q (H+K)=third (Γ.average μ) F Q H+third (Γ.average μ) F Q K := by
  unfold third
  simp (disch := repeat first | assumption | apply product | apply combine) only [mul_add,read Γ μ]
  ring

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.HasTemperateGrowth] in
theorem halfThird (F Q H : E→ℝ) : third (Γ.average μ) F Q (half H) = third (Γ.average μ) F Q H/2 := by
  have move (X Y : E→ℝ) : X*half Y=half (X*Y) := by funext x;simp [half];ring
  simp only [third,move,scaled]
  ring

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.HasTemperateGrowth] in
theorem paired (F Q H : E→ℝ) (h : Γ.average μ H=0) (q : Γ.average μ (Q*H)=0) :
    third (Γ.average μ) F Q (H*H)=fourth (Γ.average μ) F Q H := by
  simp only [third,fourth,←mul_assoc,h,q]
  ring

end averaging
variable {E : Type*} [NormedAddCommGroup E]

theorem pricedHalf {H : E→ℝ} (h : priced H) : priced (half H) := by
  let C : E→ℝ := fun _=>(2:ℝ)⁻¹
  have c : priced C := ⟨Zone.Invoice.const _,continuous_const⟩
  have eq : half H=H*C := by funext x;exact div_eq_mul_inv .. 
  rw [eq];exact product h c

theorem priceDifference {F H : E→ℝ} (f : priced F) (h : priced H) : priced (F-H) := by
  refine ⟨?_,f.2.sub h.2⟩
  rw [sub_eq_add_neg]
  exact f.1.add (h.1.weaken (fun x=>by simp))

end YM.Integration.WilsonConditionalTaylorThermalCubicPair
