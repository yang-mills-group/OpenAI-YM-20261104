import YM.Integration.WilsonConditionalTaylorThermalInteractionQuotient

/-! The first interacting response is a connected three-point function on the
genuine Gaussian, together with the two connected higher source vertices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalCumulant
open Function MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalLaplace WilsonConditionalTaylorThermalInteraction
open scoped Classical BigOperators ContDiff Topology

def covariance {E : Type*} (A : (E→ℝ)→ℝ) (B F : E→ℝ) := A (B*F)-A B*A F

def third {E : Type*} (A : (E→ℝ)→ℝ) (B F H : E→ℝ) :=
  A ((B*F)*H)-A (B*F)*A H-A (B*H)*A F-A (F*H)*A B+2*A B*A F*A H

def priced {E : Type*} [NormedAddCommGroup E] (f : E→ℝ) : Prop :=
  Zone.Invoice (Radial.zone (E:=E)) f ∧ Continuous f

theorem product {E : Type*} [NormedAddCommGroup E] {f g : E→ℝ} (h : priced f) (q : priced g) :
    priced (f*g) := ⟨h.1.mul q.1,h.2.mul q.2⟩

theorem combine {E : Type*} [NormedAddCommGroup E] {f g : E→ℝ} (h : priced f) (q : priced g) :
    priced (f+g) := ⟨h.1.add q.1,h.2.add q.2⟩

theorem read {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (Γ : Law E) (μ : Measure E) [μ.HasTemperateGrowth]
    {f g : E→ℝ} (h : priced f) (q : priced g) :
    Γ.average μ (f+g) = Γ.average μ f+Γ.average μ g := by
  unfold Law.average
  rw [add_mul]
  simp only [Pi.add_apply]
  rw [integral_add (Γ.integrable_entry μ h.1 h.2) (Γ.integrable_entry μ q.1 q.2),add_div]

theorem angular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (F : E→ℝ) (k : ℕ) : priced (jet F k) := ⟨Radial.jetInvoice ..,Radial.Smooth.continuousJet ..⟩

variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d
local notation "μ" => Chart.tangent G d.Links

theorem prior (P : ChartRatio G) (t : d.Tags) : priced (interaction P t) := by
  let C := fun _ : E => (density d P)⁻¹
  have c : priced C := ⟨Zone.Invoice.const _,continuous_const⟩
  have j := product (angular (haar P d) 1) c
  have v := angular (d.phase G t) 3
  have equal : interaction P t = jet (haar P d) 1*C-jet (d.phase G t) 3 := by
    funext x; exact congrArg (·-jet (d.phase G t) 3 x) (div_eq_mul_inv ..)
  rw [equal]
  refine ⟨?_,j.2.sub v.2⟩
  rw [sub_eq_add_neg]
  exact j.1.add (v.1.weaken (fun x => by simp))

theorem original (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    (u v : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (grade : d.grade f w) :
    let A := (ambient t room).average μ
    let Q := vertex t (u-v)
    let F := field (d:=d) f w
    ranking P d u f (w+3)-ranking P d v f (w+3) =
      -covariance A Q (field f (w+1)) - covariance A (nextVertex t (u-v)) F -
        third A Q F (interaction P t) := by
  intro A Q F
  have hq : priced Q := angular _ _
  have hf : priced F := angular _ _
  have hy : priced (field (d:=d) f (w+1)) := angular _ _
  have hr : priced (nextVertex (G:=G) t (u-v)) := angular _ _
  have h := prior P t
  have a := WilsonConditionalTaylorThermalInteractionQuotient.original P R room t u v test grade
  change _ = -A _+A F*A _+(A _ -A F*A _)*A Q+(A (F*Q)-A F*A Q)*A _ at a
  rw [a]
  unfold WilsonConditionalTaylorThermalInteractionBook.inserted WilsonConditionalTaylorThermalInteractionBook.stored
  change -A (_+_+_)+A F*A (_+_)+(A (_+_)-_)*A Q+(A (F*Q)-_)*_ = _
  have pay {X Y : E→ℝ} (hx : priced X) (hy : priced Y) : A (X+Y)=A X+A Y := read _ _ hx hy
  rw [pay (combine (product hr hf) (product hq hy)) (product (product hq hf) h),
    pay (product hr hf) (product hq hy),pay hr (product hq h),pay hy (product hf h),mul_comm F Q]
  unfold covariance third
  ring

end YM.Integration.WilsonConditionalTaylorThermalCumulant
