import YM.Integration.WilsonIndependentCollarOrbitalUnweighted

/-! Use the same physical canonical measure for a winding comparison whose
profile ball has already been paid. All residual tests remain their original
ones. The auxiliary canonical flat test only computes this numerical cap. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarPaidWindingPanel
open Filter Function Finset Lattice RG Wilson Marker Multi QuadraticLocal QuadraticLocal.Earn PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonCoeffUV WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider
open WilsonIndependentCollarOriginalDose (weight axisFee)
open WilsonThermometerDeclaredSeeds WilsonReceivedCanonicalVerseBasis WilsonReceivedCanonicalVerseRegister
open WilsonOriginalStarSceneWords (pole)
open WilsonIndependentCollarOrbitalBasisPayment (Choices)
open WilsonReceivedDepositedOrbitalNamedWage (wages)
open WilsonOriginalMixedBlockRows (room)
open WilsonReceivedCanonicalSocketSeed (present)
open scoped Classical BigOperators Topology

variable {G:Gauge}{n:ℕ}{I:Type}[Fintype I][DecidableEq I]

def earned (R:Run G)(k:Fin n→ℕ)(A m:ℕ)(C:ℝ)(M:Fin n→ℝ)(T:Finset (Fin n))(seats:ℕ):ℝ:=
  (∏j:T,M j)*C^(∑j:T,k j)*(Real.sqrt (2*R.family.path.levels.clock.hatBeta (m+1)))^((2*A+1)*(∑j:T,k j))*(2:ℝ)^seats

def yield (R:Run G)(k:Fin n→ℕ)(N per K m:ℕ)(v:(j:Fin n)→R.family.label (k j))(T:Finset (Fin n))
    (a:Choices R k T):ℝ:=∏j:T,weight R k N per K v j (a j) (regulatorRun R.family N per K)
      (R.family.path.levels.S.a m/R.family.path.levels.S.a K)

def signed (R:Run G)(k:Fin n→ℕ)(N per K m:ℕ)(v:(j:Fin n)→R.family.label (k j))(T:Finset (Fin n))
    (a:Choices R k T):ℂ:=
  let g:=regulatorRun R.family N per K
  let size:=R.family.path.levels.S.a m/R.family.path.levels.S.a K
  ∏j:T,dose R k N per K v j (a j)*Complex.ofReal ((g⁻¹)^(pole R k (entry R k j (a j)))*size^(k j))

theorem norm_signed (R:Run G)(k:Fin n→ℕ)(N per K m:ℕ)(v:(j:Fin n)→R.family.label (k j))
    (T:Finset (Fin n))(a:Choices R k T):
    ‖signed R k N per K m v T a‖=yield R k N per K m v T a:=by
  unfold signed yield
  rw [norm_prod]
  apply prod_congr rfl
  intro j _
  have heat:0≤(regulatorRun R.family N per K)⁻¹:=inv_nonneg.mpr (inv_nonneg.mpr (Real.sqrt_nonneg _))
  have scale:0≤R.family.path.levels.S.a m/R.family.path.levels.S.a K:=
    (div_pos (R.family.path.levels.S.a_pos _) (R.family.path.levels.S.a_pos _)).le
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg heat _) (pow_nonneg scale _))]
  unfold WilsonIndependentCollarOriginalDose.weight
  ring

theorem original (R:Run G)(simple:G.Simple)(k:Fin n→ℕ)(A:ℕ):
    let L:=R.family.path.levels
    ∃C:ℝ,0≤C ∧ ∀ᶠ m:ℕ in atTop,∀(K N per:ℕ),m≤K → K≤N → m+1≤N →
      L.S.scale K-L.S.scale m≤(A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) →
      ∀(target:(Stock.census (Fin n)).Mode)(M:Fin n→ℝ)(v:(j:Fin n)→R.family.label (k j)),
      (∀j∈target.val,axisFee R k v j≤M j) →
      ∀(side:Side)(P:Passport side (Fin n))(B:I→Binder P (Stock.census (Fin n)))
        (x:Choices R k target.val→Affinity.Wallet (room (Fin n))),
      (∑a:Choices R k target.val,yield R k N per K m v target.val a *
        ∑s:Finset I,‖wages B (x a) target s‖) ≤ earned R k A m C M target.val (Fintype.card I) := by
  intro L
  obtain ⟨C,non,calendar⟩:=WilsonIndependentCollarMeasuredProbeWindow.original (I:=I) R simple k A
  refine ⟨C,non,?_⟩
  filter_upwards [calendar] with m paid
  intro K N per newer top base span target M v money side P B x
  let D:Fin n→ℕ:=fun _=>0
  have paid:=paid K N per newer top base span target D M (fun _=>1) (fun _=>zero_le_one)
    v money side P B x (fun _=>present D) (fun a j _=>by rw [WilsonIndependentCollarCanonicalProbe.cap,mul_one];exact (x a j).property)
  simpa only [yield,earned,WilsonIndependentCollarOrbitalUnweighted.flat,prod_const_one,mul_one] using paid

end YM.Integration.WilsonIndependentCollarPaidWindingPanel
end
