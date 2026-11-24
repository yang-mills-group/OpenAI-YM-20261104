import YM.Integration.ActualPolynomialContraction
import YM.Integration.ActualWilsonThermalEndpoints

/-! Removing a genuine event from a normalized positive Wilson law.
The comparison retains the whole marked density and its scalar
normalization before taking the finite connected logarithm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.PhysicalWilsonConditionalRestriction
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker
open Comparison.RG02 Comparison.RG02.Order LocalComparison LocalComparison.MarkedPackets
open ActualPolynomialContraction
open scoped Topology BigOperators Classical

variable {V : Type} [DecidableEq V] {H : Census V}
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set Ω) (f : Ω→Poly H) (w : V→ℝ) (hw : ∀ v,0<w v)

def conditioned : Poly H := (μ.real Aᶜ)⁻¹ • ∫ U in Aᶜ,f U ∂μ

include hw in
theorem part_price (B : ℝ) (hf : Integrable f μ) (bought : ∀ U,Poly.price w (f U)≤B) :
    Poly.price w (∫ U in A,f U ∂μ)≤μ.real A*B := by
  apply (price_integral_le hw hf.integrableOn).trans
  calc ∫ U in A,Poly.price w (f U) ∂μ ≤ ∫ _ in A,B ∂μ :=
          integral_mono (price_integrable w hf.integrableOn) (integrable_const _) bought
       _ = _ := by rw [setIntegral_const,smul_eq_mul]

include hw in
theorem amount (h : 0<μ.real Aᶜ) (B : ℝ) (hf : Integrable f μ) (bought : ∀ U,Poly.price w (f U)≤B) :
    Poly.price w (conditioned μ A f)≤B := by
  rw [conditioned,price_real_smul w _ (inv_nonneg.mpr h.le)]
  calc (μ.real Aᶜ)⁻¹ * _ ≤ (μ.real Aᶜ)⁻¹*(μ.real Aᶜ*B) :=
          mul_le_mul_of_nonneg_left (part_price μ Aᶜ f w hw B hf bought) (inv_nonneg.mpr h.le)
       _ = B := by rw [←mul_assoc,inv_mul_cancel₀ h.ne',one_mul]

include hw in
/-- This cost is proportional to the removed mass even if the retained
positive mass is much smaller than one. -/
theorem ordinary (hA : MeasurableSet A) (h : 0<μ.real Aᶜ) (B : ℝ)
    (hf : Integrable f μ) (bought : ∀ U,Poly.price w (f U)≤B) :
    Poly.price w ((∫ U,f U ∂μ)-conditioned μ A f)≤2*B*μ.real A := by
  let L := conditioned μ A f
  have mass : μ.real A+μ.real Aᶜ=1 := by
    simpa only [probReal_univ] using measureReal_add_measureReal_compl (μ:=μ) hA
  have full : (∫ U,f U ∂μ)=(∫ U in A,f U ∂μ)+μ.real Aᶜ • L := by
    change (∫ U,f U ∂μ)=(∫ U in A,f U ∂μ)+μ.real Aᶜ • ((μ.real Aᶜ)⁻¹ • ∫ U in Aᶜ,f U ∂μ)
    rw [smul_smul,mul_inv_cancel₀ h.ne',one_smul,integral_add_compl hA hf]
  have missing : (∫ U,f U ∂μ)-L=(∫ U in A,f U ∂μ)-μ.real A • L := by
    rw [full,show μ.real Aᶜ=1-μ.real A by linarith,sub_smul,one_smul]
    abel
  change Poly.price w ((∫ U,f U ∂μ)-L)≤_
  rw [missing]
  apply (Order.priced_sub w hw ..).trans
  rw [price_real_smul w L (by positivity : 0≤μ.real A)]
  apply (add_le_add (part_price μ A f w hw B hf bought)
    (mul_le_mul_of_nonneg_left (amount μ A f w hw h B hf bought) (by positivity))).trans_eq
  ring

omit [IsProbabilityMeasure μ] in
theorem quiet (hf : Integrable f μ) (one : ∀ U,(f U).part H.quiet=1) :
    (∫ U in A,f U ∂μ).part H.quiet=(μ.real A:ℂ) := by
  let L := (Poly.get H.quiet).restrictScalars ℝ
  change L (∫ U in A,f U ∂μ)=_
  rw [←L.integral_comp_comm hf.integrableOn]
  change (∫ U in A,(f U).part H.quiet ∂μ)=_
  simp only [one,setIntegral_const,Complex.real_smul,mul_one]

include hw in
theorem connected [Fintype V] (hA : MeasurableSet A) (h : 0<μ.real Aᶜ) (B : ℝ)
    (hf : Integrable f μ) (bought : ∀ U,Poly.price w (f U)≤B) (one : ∀ U,(f U).part H.quiet=1) :
    Poly.price w (Extra.Trajectories.connected (∫ U,f U ∂μ)-
      Extra.Trajectories.connected (conditioned μ A f))≤
        Order.repeats (Fintype.card V) (1+B)*(2*B*μ.real A) := by
  have f₀ : (∫ U,f U ∂μ).part H.quiet=1 := by simpa using quiet μ univ f hf one
  have f₁ : (conditioned μ A f).part H.quiet=1 := by
    rw [conditioned,←Complex.coe_smul,Poly.part_smul,quiet μ Aᶜ f hf one,Complex.ofReal_inv,
      inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr h.ne')]
  have q₀ : Poly.price w (∫ U,f U ∂μ) ≤ B := by
    simpa using part_price μ univ f w hw B hf bought
  have q₁ := amount μ A f w hw h B hf bought
  have hn := (Poly.nonnegative hw _).trans q₀
  have complement (u : Poly H) (hu : Poly.price w u≤B) : Poly.price w (1-u)≤1+B :=
    (Order.priced_sub w hw ..).trans (by rw [Poly.one_price]; linarith only [hu])
  apply (Order.lip _ _ w hw f₀ f₁ (complement _ q₀) (complement _ q₁)
    (Fintype.card V) (fun i=>Finset.card_le_univ _)).trans
  exact mul_le_mul_of_nonneg_left (ordinary μ A f w hw hA h B hf bought)
    (Order.repeats_pos _ _ (by linarith))

section Packet
variable {G : Gauge} {n : Side} [Fintype V] {D : V → ComparisonDensity.Address.Orbit}
    (P : MarkedPackets D G n H) {p : BudgetPoint} {addr : V→Support n}
    {region : Comparison.Density.Testing.Region (fun i=>(D i).Mood) n}
    {weight : V→ℝ} {g width budget : ℝ} {off slope : ℕ}
    (hP : P.Paid p addr region weight g width budget off slope)
    (z : IndependentTests D) (cap : ℕ) (hcap : P.rankCap≤cap)

def marked (U : Config G n) : Poly H := Poly.pass (P.read (testInclusion D z) g U)

include hP hcap in
theorem integrable (ν : Measure (Config G n)) [IsFiniteMeasure ν] :
    Integrable (marked P (g:=g) z) ν := by
  obtain ⟨k,hk,fits⟩ := Poly.equivalent_norm hP.positive
  have meas : Measurable (fun U=>P.read (testInclusion D z) g U) :=
    Measurable.tsum (fun i=>(WilsonThermalReadout.atom P g z i).measurable)
  exact (integrable_const (c:=uniformModelCost cap (Fintype.card V) budget*k)).mono'
    (Poly.pass_cont.measurable.comp meas).aestronglyMeasurable (Eventually.of_forall fun U=>
      (fits _).trans (mul_le_mul_of_nonneg_right (hP.uniform_model cap hcap z U) hk))

include hP hcap in
/-- Actual full original paid nonlinear bank at its genuine coupling.
Every independent marked test and each retained spatial event may vary. -/
theorem packet (ν : Measure (Config G n)) [IsProbabilityMeasure ν] (E : Set (Config G n))
    (hm : MeasurableSet E) (good : 0<ν.real Eᶜ) :
    let B := uniformModelCost cap (Fintype.card V) budget
    Poly.price weight (Extra.Trajectories.connected (∫ U,marked P (g:=g) z U ∂ν)-
      Extra.Trajectories.connected (conditioned ν E (marked P (g:=g) z))) ≤
        Order.repeats (Fintype.card V) (1+B)*(2*B*ν.real E) := by
  apply connected ν E _ weight hP.positive hm good _ (integrable P hP z cap hcap ν)
    (hP.uniform_model cap hcap z)
  intro U
  apply Poly.pass_part
  exact P.quiet_read _ _ U

end Packet
end YM.Integration.PhysicalWilsonConditionalRestriction
end
