import YM.Integration.WilsonIndependentCollarEngineeringClock

/-! Complete finite basis wage on the stated polynomial collar. Relative
group and angular salaries can both use its one power per external mark. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.Integration.WilsonIndependentCollarPhysicalBasis
open Filter Finset Function Lattice Wilson RG Source Labels
open PhysicalNext.Repeat.Legato Pert.Asymptotics
open WilsonThermometerDeclaredSeeds WilsonReceivedCanonicalVerseBasis WilsonReceivedCanonicalVerseRegister
open WilsonIndependentCollarOriginalDose
open scoped Classical BigOperators Topology
variable {G:Gauge}{I:Type} [DecidableEq I]

theorem original (R:Run G)(simple:G.Simple)(k:I→ℕ)(A:ℕ):
    let L:=R.family.path.levels
    ∃C:ℝ,0≤C ∧ ∀ᶠ m:ℕ in atTop,∀(K N per:ℕ),m≤K → K≤N → m+1≤N →
      L.S.scale K-L.S.scale m≤(A:ℝ)*(1+Real.log (L.clock.hatBeta (m+1))) →
      ∀ (v:(j:I)→R.family.label (k j))(S:Finset I),
      let g:=regulatorRun R.family N per K
      let z:=Real.sqrt (R.family.path.β N per (m+1))
      let size:=L.S.a m/L.S.a K
      let mass:=∑j:S,k j
      (∑q:(j:S)→Choice R k j, ∏j:S, weight R k N per K v j (q j) g size) ≤
        (∏j:S,axisFee R k v j)*C^mass*z^((2*A+1)*mass):=by
  intro L
  obtain ⟨C,positive,price⟩:=WilsonIndependentCollarEngineeringClock.original R simple A
  have rise:Tendsto L.clock.hatBeta atTop atTop:=tendsto_atTop_add_const_left _ _
    (L.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  refine ⟨C,positive,?_⟩
  filter_upwards [rise.eventually_ge_atTop 2] with m late
  intro K N per newer top header span v S g z size mass
  have hk:L.clock.hatBeta m ≤ L.clock.hatBeta K:=by
    change _+_*L.S.scale m≤_+_*L.S.scale K
    exact add_le_add_right (mul_le_mul_of_nonneg_left ((OPE.scale_mono R.family.S).monotone newer)
      (Gauge.slopeConstant_pos simple).le) _
  have beta:0 < R.family.path.β N per K:=Overlay.beta_positive R.makes.wilson top
  have opening:L.clock.hatBeta K/2 ≤ R.family.path.β N per K:=
    (R.makes.wilson.represents N per K top).band.1
  have cool:g≤1:=(inv_le_one₀ (Real.sqrt_pos.2 beta)).2 (Real.one_le_sqrt.mpr (by linarith only [late,hk,opening]))
  have g0:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr beta)
  have len:0 ≤ size:=(div_pos (L.S.a_pos _) (L.S.a_pos _)).le
  have restored:size/g≤C*z^(2*A+1):=price m K N per top header span
  have basis (j:I):0≤axisFee R k v j:=Finset.sum_nonneg fun c _=>
    (norm_nonneg _).trans (measured R k N per K top v j c)
  calc
    _≤∏j:S,axisFee R k v j*(size/g)^(k j):=
      family R k N per K top v S g size g0 cool len
    _≤∏j:S,axisFee R k v j*(C*z^(2*A+1))^(k j):=Finset.prod_le_prod
      (fun j _=>mul_nonneg (basis j) (pow_nonneg (div_nonneg len g0.le) _))
      (fun j _=>mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (div_nonneg len g0.le) restored _) (basis j))
    _=_:=by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,mul_pow,←pow_mul,mul_assoc]

end YM.Integration.WilsonIndependentCollarPhysicalBasis
end
