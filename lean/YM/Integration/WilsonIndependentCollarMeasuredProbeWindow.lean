import YM.Integration.WilsonIndependentCollarCanonicalProbe
import YM.Integration.WilsonIndependentCollarOriginalWages

/-! The thermal band turns the original physical dose into a cap fixed before
both regulators, on a collar chosen before the order of the angular test. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarMeasuredProbeWindow
open Filter Function Finset Lattice RG Wilson Marker Multi QuadraticLocal QuadraticLocal.Earn PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider
open WilsonIndependentCollarOriginalDose (weight axisFee)
open WilsonThermometerDeclaredSeeds WilsonReceivedCanonicalVerseBasis WilsonReceivedCanonicalVerseRegister
open WilsonIndependentCollarOrbitalBasisPayment (Choices)
open WilsonIndependentCollarOrbitalPeg (ink)
open WilsonReceivedDepositedOrbitalNamedWage (wages)
open WilsonOriginalMixedBlockRows (room)
open scoped Classical BigOperators Topology

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{n:ℕ}

theorem original (R:Run G)(simple:G.Simple)(k:Fin n→ℕ)(A:ℕ):
    let L:=R.family.path.levels
    ∃C:ℝ,0≤C ∧ ∀ᶠ m:ℕ in atTop,∀(K N per:ℕ),m≤K → K≤N → m+1≤N →
      L.S.scale K-L.S.scale m≤(A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) →
      ∀(target:(Stock.census (Fin n)).Mode)(D:Fin n→ℕ)(M U:Fin n→ℝ),
      (∀v,0≤U v) → ∀(v:(l:Fin n)→R.family.label (k l)),(∀j∈target.val,axisFee R k v j≤M j) →
      ∀(side:Side)(P:Passport side (Fin n))(B:I→Binder P (Stock.census (Fin n))),
      ∀(x:Choices R k target.val→Affinity.Wallet (room (Fin n)))(t:Choices R k target.val→Case D),
      (∀a j,j∈target.val→ ‖(x a j).val‖*‖t a j‖≤U j) →
      let g:=regulatorRun R.family N per K
      let size:=L.S.a m/L.S.a K
      let d:=∑j:target.val,k j
      (∑a:Choices R k target.val,(∏j:target.val,weight R k N per K v j (a j) g size) *
          ∑s:Finset I,‖wages B (x a) target s‖*∏i∈s,‖ink (t a) (B i).mode.val‖) ≤
        ((∏j:target.val,M j)*C^d*(Real.sqrt (2*L.clock.hatBeta (m+1)))^((2*A+1)*d))*
          ((2:ℝ)^(Fintype.card I)*∏j∈target.val,U j) := by
  intro L
  obtain ⟨C,non,bought⟩:=WilsonIndependentCollarPhysicalBasis.original R simple k A
  refine ⟨C,non,?_⟩
  filter_upwards [bought] with m receipt
  intro K N per newer top base span target D M U pos v charged side P B x t rents g size d
  let dose (a:Choices R k target.val):ℝ:=∏j:target.val, weight R k N per K v j (a j) g size
  let fare:ℝ:=(2:ℝ)^(Fintype.card I)*∏j∈target.val,U j
  have fee:0≤fare:=mul_nonneg (by positivity) (prod_nonneg fun j _=>pos j)
  have heat:0≤g:=(inv_nonneg.mpr (Real.sqrt_nonneg _))
  have physical:0 ≤ size:=(div_pos (L.S.a_pos _) (L.S.a_pos _)).le
  have prices(a:Choices R k target.val):0≤dose a:=prod_nonneg fun _ _=>mul_nonneg
    (mul_nonneg (norm_nonneg _) (pow_nonneg (inv_nonneg.mpr heat) _)) (pow_nonneg physical _)
  have heads (j:Fin n):0≤axisFee R k v j:=sum_nonneg fun c _=>(norm_nonneg _).trans (measured R k N per K top v j c)
  have total := receipt K N per newer top base span v target.val
  have cap (a:Choices R k target.val):
      (∑s:Finset I,‖wages B (x a) target s‖*∏i∈s,‖ink (t a) (B i).mode.val‖) ≤ fare:=
    (WilsonIndependentCollarOrbitalDose.original B (x a) (t a) target).trans
      (mul_le_mul_of_nonneg_left (prod_le_prod (fun _ _=>mul_nonneg (norm_nonneg _) (norm_nonneg _)) (rents a)) (by positivity))
  have hot:R.family.path.β N per (m+1)≤2*L.clock.hatBeta (m+1):=(R.makes.wilson.represents N per (m+1) base).band.2
  have costs:(∏j:target.val,axisFee R k v j) ≤ ∏j:target.val,M j:=
    prod_le_prod (fun j _=>heads j) (fun j _=>charged j j.property)
  calc
    _ ≤ ∑a:Choices R k target.val,dose a*fare:=sum_le_sum fun a _=>mul_le_mul_of_nonneg_left (cap a) (prices a)
    _ = (∑a:Choices R k target.val,dose a)*fare:=(Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (total.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right costs (pow_nonneg non _))
      (pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hot) _)
      (pow_nonneg (Real.sqrt_nonneg _) _) (mul_nonneg (prod_nonneg fun j _=>(heads j).trans (charged j j.property)) (pow_nonneg non _)))) fee

end YM.Integration.WilsonIndependentCollarMeasuredProbeWindow
end
