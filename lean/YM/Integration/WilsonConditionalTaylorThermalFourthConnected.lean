import YM.Integration.WilsonConditionalTaylorThermalFourthGaussian

/-! The normalization at relative degree four leaves three covariances
and three genuine connected three-point functions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorThermalFourthConnected
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport
open RGComparison.Core16 RGComparison.Core16.Descent PertExtension PertExtension.Series Tested Radial GaussianScore
open WilsonConditionalTaylorThermalCumulant
open scoped Classical BigOperators ContDiff Topology

def contribution {E : Type*} (A : (E→ℝ)→ℝ) (F F1 F2 Q Q3 Q4 H J : E→ℝ) :=
  -(covariance A F2 Q+covariance A F1 Q3+covariance A F Q4+
    third A F1 Q H+third A F Q3 H+third A F Q J)

theorem charged {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (Γ : Law E) (μ : Measure E) [μ.HasTemperateGrowth]
    {F F1 F2 Q Q3 Q4 H J : E→ℝ} (f : priced F) (f1 : priced F1) (f2 : priced F2)
    (q : priced Q) (q3 : priced Q3) (q4 : priced Q4) (h : priced H) (j : priced J)
    (hh : Γ.average μ H=0) (hb : Γ.average μ Q3=0) (hc : Γ.average μ (Q*H)=0) :
    WilsonConditionalTaylorThermalFourthCentering.centers (Γ.average μ F)
      (Γ.average μ (F2+F1*H+F*J)) (Γ.average μ Q) (Γ.average μ (F*Q)) (Γ.average μ J)
      (Γ.average μ (F2*Q+F1*(Q3+Q*H)+F*(Q4+Q3*H+Q*J))) (Γ.average μ (Q4+Q3*H+Q*J))=
    contribution (Γ.average μ) F F1 F2 Q Q3 Q4 H J := by
  simp (disch := repeat first | assumption | apply product | apply combine) only
    [WilsonConditionalTaylorThermalFourthCentering.centers,contribution,covariance,third,mul_add,←mul_assoc,
      read Γ μ,hh,hb,hc]
  ring

private theorem subPrice {E : Type*} [NormedAddCommGroup E] {f g : E→ℝ} (h : priced f) (q : priced g) :
    priced (f-g) := by
  refine ⟨?_,h.2.sub q.2⟩
  rw [sub_eq_add_neg]
  exact h.1.add (q.1.weaken (fun x => by simp))

variable {G : Gauge} {n c : Side} {d : Descent n c}
local notation "E" => Coordinates G d
local notation "μ" => Chart.tangent G d.Links
open WilsonConditionalTaylorThermalWeight WilsonConditionalTaylorThermalLaplace WilsonConditionalTaylorThermalInteraction
open WilsonConditionalTaylorThermalFourthActivity WilsonConditionalTaylorThermalFourthBook

theorem activity (P : ChartRatio G) (t : d.Tags) : priced (second P t) := by
  let C (z : ℝ) : E→ℝ := fun _=>z
  have price (z : ℝ) : priced (C z) := ⟨Zone.Invoice.const _,continuous_const⟩
  let B := jet (d.phase G t) 3
  have b : priced B := angular .. 
  have equal : second P t = jet (haar P d) 2*C (density d P)⁻¹-
      jet (haar P d) 1*C (density d P)⁻¹*B-jet (d.phase G t) 4+B*B*C (2:ℝ)⁻¹ := by
    funext x;simp [second,C,B,div_eq_mul_inv,pow_two]
  rw [equal]
  exact combine (subPrice (subPrice (product (angular ..) (price _))
    (product (product (angular ..) (price _)) b)) (angular ..)) (product (product b b) (price _))

theorem oddMean (Γ : Law E) (F : E→ℝ) (odd : ∀x,F (-x) = -F x) : Γ.average μ F=0 := by
  letI : (Chart.tangent G d.Links).IsNegInvariant :=
    ⟨(measurePreserving_pi _ _ (fun (_ : d.Links)=>Measure.measurePreserving_neg (volume : Measure G.Color))).map_eq⟩
  have sym (x : E) : Γ.kern (-x)=Γ.kern x := by simp [Law.kern]
  have flip := integral_neg_eq_self (fun x=>F x*Γ.kern x) μ
  simp_rw [odd,sym,neg_mul] at flip
  rw [integral_neg] at flip
  simp only [Law.average,Pi.mul_apply]
  rw [show (∫ x, F x*Γ.kern x ∂μ)=0 by linarith,zero_div]

theorem symmetry (P : ChartRatio G) (t : d.Tags) (a : ℕ→ℝ) (Γ : Law E) :
    Γ.average μ (interaction P t)=0 ∧ Γ.average μ (nextVertex t a)=0 ∧
    Γ.average μ (vertex t a*interaction P t)=0 := by
  have ray (f : E→ℝ) (k : ℕ) (x : E) : jet f k (-x)=(-1:ℝ)^k*jet f k x := by
    rw [←neg_one_smul ℝ x,jet_smul]
  have h (x : E) : interaction P t (-x) = -interaction P t x := by
    unfold interaction
    rw [ray,ray]
    ring
  refine ⟨oddMean Γ _ h,oddMean Γ _ ?_,oddMean Γ _ ?_⟩
  · intro x;unfold nextVertex;rw [ray];ring
  · intro x;simp only [Pi.mul_apply,h];unfold vertex;rw [ray];ring

def attached (P : ChartRatio G) (room : d.Room G) (t : d.Tags) (a : ℕ→ℝ) (f : Config G n→ℝ) (w : ℕ) :=
  contribution ((ambient t room).average μ) (field (d:=d) f w) (field f (w+1)) (field f (w+2))
    (vertex t a) (nextVertex t a) (quartic t a) (interaction P t) (second P t)

theorem original (P : ChartRatio G) (R : LocalRatio P) (room : d.Room G) (t : d.Tags)
    (a : ℕ→ℝ) {f : Config G n→ℝ} (test : d.Testable f) {w : ℕ} (old : d.grade f w) :
    WilsonConditionalTaylorThermalFirstDifferential.response P d a f (w+4)=attached P room t a f w := by
  rw [WilsonConditionalTaylorThermalFourthGaussian.original P R room t a test old]
  have unit2 : field (d:=d) (1 : Config G n→ℝ) 2=0 := by
    change jet (fun _ : E=>(1:ℝ)) 2=_
    funext x;simp [jet,iteratedFDeriv_const_of_ne (show 2≠0 by decide)]
  have sym := symmetry P t a (ambient t room)
  unfold WilsonConditionalTaylorThermalFourthGaussian.reading WilsonConditionalTaylorThermalFourthBook.prior submitted
  simp only [unit2,WilsonConditionalTaylorThermalInteractionQuotient.unitNext,
    WilsonConditionalTaylorThermalBook.unitField,zero_mul,zero_add,one_mul]
  exact charged (ambient t room) μ (angular ..) (angular ..) (angular ..)
    (angular ..) (angular ..) (angular ..) (WilsonConditionalTaylorThermalCumulant.prior P t)
    (activity P t) sym.1 sym.2.1 sym.2.2

end YM.Integration.WilsonConditionalTaylorThermalFourthConnected
