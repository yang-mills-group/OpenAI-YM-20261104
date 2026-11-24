import YM.Integration.WilsonIndependentCollarStationEntrance

/-! Original canonical dose restoration when a different basis letter has a
different genuine set of submitted binders. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarVaryingRestoration
open Filter Function Finset Lattice RG Wilson Marker Multi QuadraticLocal QuadraticLocal.Earn PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider
open WilsonIndependentCollarOriginalDose (axisFee)
open WilsonThermometerDeclaredSeeds WilsonReceivedCanonicalVerseBasis WilsonReceivedCanonicalVerseRegister
open WilsonIndependentCollarOrbitalBasisPayment (Choices)
open WilsonIndependentCollarPaidWindingPanel (signed earned yield norm_signed)
open WilsonOriginalSparseFiledOpening (near)
open scoped Classical BigOperators

variable {G:Gauge}{n:ℕ}

theorem original (R:Run G)(simple:G.Simple)(k:Fin n→ℕ)(A seats:ℕ):
    let L:=R.family.path.levels
    ∃C:ℝ,0≤C ∧ ∀ᶠ m:ℕ in atTop,∀K i:ℕ,m≤K →
      L.S.scale K-L.S.scale m≤(A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) →
      ∀(T:Finset (Fin n))(M:Fin n→ℝ)(power pole E:ℕ),
      let H:=R.alloy.B.a.clock.hatBeta (i+1)
      0<H → ∃ε:ℝ,0<ε ∧ ε=(H^(near power pole E))⁻¹/(1+max 0 (earned R k A m C M T seats)) ∧
      ∀N per:ℕ,K≤N → m+1≤N → ∀v:(j:Fin n)→R.family.label (k j),(∀j∈T,axisFee R k v j≤M j) →
      ∀high low:Choices R k T→ℂ,(∀a,‖high a-low a‖≤ε*(2:ℝ)^seats) →
      (∑a:Choices R k T,‖signed R k N per K m v T a*(high a-low a)‖)≤(H^(near power pole E))⁻¹:=by
  intro L
  obtain ⟨C,non,bought⟩:=WilsonIndependentCollarPhysicalBasis.original R simple k A
  refine ⟨C,non,?_⟩
  filter_upwards [bought] with m paid
  intro K i newer span T M power pole E H hot
  let bill:=earned R k A m C M T seats
  let goal:ℝ:=(H^(near power pole E))⁻¹
  let ε:=goal/(1+max 0 bill)
  have den:0<1+max 0 bill:=by linarith only [le_max_left 0 bill]
  have positive:0<ε:=div_pos (inv_pos.mpr (pow_pos hot _)) den
  refine ⟨ε,positive,rfl,?_⟩
  intro N per top base v money high low quote
  have heads (j:Fin n):0≤axisFee R k v j:=sum_nonneg fun c _=>(norm_nonneg _).trans (measured R k N per K top v j c)
  have costs:(∏j:T,axisFee R k v j)≤∏j:T,M j:=prod_le_prod (fun j _=>heads j) (fun j _=>money j j.property)
  have hotN:R.family.path.β N per (m+1)≤2*L.clock.hatBeta (m+1):=(R.makes.wilson.represents N per (m+1) base).band.2
  have bulk:=paid K N per newer top base span v T
  let α:ℝ:=2^seats
  let w:=fun a=>yield R k N per K m v T a
  have absolute:(∑a:Choices R k T,w a)*α≤bill:=by
    apply mul_le_mul_of_nonneg_right _ (by positivity :0≤α)
    exact bulk.trans (mul_le_mul (mul_le_mul_of_nonneg_right costs (pow_nonneg non _))
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hotN) _)
      (pow_nonneg (Real.sqrt_nonneg _) _) (mul_nonneg (prod_nonneg fun j _=>(heads j).trans (money j j.property)) (pow_nonneg non _)))
  calc
    _ ≤ ∑a:Choices R k T,ε*(w a*α):=by
      apply sum_le_sum;intro a _
      rw [norm_mul,norm_signed]
      have pos:0≤w a:=(norm_nonneg _).trans_eq (norm_signed R k N per K m v T a)
      exact (mul_le_mul_of_nonneg_left (quote a) pos).trans_eq (by ring)
    _ = ε*((∑a:Choices R k T,w a)*α):=by rw [Finset.sum_mul,Finset.mul_sum]
    _ ≤ ε*bill:=mul_le_mul_of_nonneg_left absolute positive.le
    _ ≤ ε*(1+max 0 bill):=mul_le_mul_of_nonneg_left (by linarith only [le_max_right 0 bill]) positive.le
    _ = goal:=div_mul_cancel₀ _ den.ne'

end YM.Integration.WilsonIndependentCollarVaryingRestoration
end
