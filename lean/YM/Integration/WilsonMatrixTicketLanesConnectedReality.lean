import YM.Integration.WilsonMatrixTicketLanesReflectedGauge

/-! The signed genuine compact covariance of real core stencils inside arbitrary complex filed columns. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesConnectedReality
open Function Finset MeasureTheory Lattice Gauge RG Wilson Tree Precision PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Parcel
open WilsonMatrixTicketLanesDescentWords WilsonMatrixTicketLanesReflectedGauge
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} (S : StepData c f) (u : Directions G c)
variable {I J : Type} [Fintype I] [Fintype J]

omit [Fintype J] in
private theorem read (A : I→Lamp G) (x : I→Site f) (filed : ∀U : Config G f,((tally A x U).re:ℂ)=tally A x U) (g : ℝ) :
    ((reads A S u x g).re:ℂ)=reads A S u x g:=by
  let β:=g⁻¹^2
  let V:=Oven.slice u g
  let h (U : Config G f):=S.density β U V * (bare β U * (tally A x U).re)
  have physical U : S.density β U V • (bare β U • tally A x U) = (h U:ℂ):=by
    simp only [h,Complex.real_smul,Complex.ofReal_mul,filed]
  have exactMean : survey A S u x g = (∫ U,h U ∂(prior G f):ℝ):=by
    change (∫ U,S.density β U V • (bare β U • tally A x U) ∂(prior G f))=_
    simp_rw [physical];rw [integral_complex_ofReal]
  rw [reads,exactMean]
  simp only [Complex.real_smul,←Complex.ofReal_mul,Complex.ofReal_re]

/-- The full complex connected response of source basis terms is the genuine signed real response. -/
theorem covariance (R : Run G) (d : I→ℕ) (h : J→ℕ) (j : ∀i,(R.family.labels.level (d i)).Index)
    (k : ∀i,(R.family.labels.level (h i)).Index) (x : I→Site f) (y : J→Site f) (g : ℝ) :
    let A:=lamps R d j
    let B:=lamps R h k
    reads (pair A B) S u (Sum.elim x y) g - reads A S u x g * reads B S u y g =
      (measured S u R d h j k x y g:ℂ):=by
  intro A B
  have lt (U : Config G f):((tally A x U).re:ℂ)=tally A x U:=WilsonMatrixTicketLanesReflectedGauge.real R d j x U
  have rt (U : Config G f):((tally B y U).re:ℂ)=tally B y U:=WilsonMatrixTicketLanesReflectedGauge.real R h k y U
  have both (U : Config G f):((tally (pair A B) (Sum.elim x y) U).re:ℂ)=tally (pair A B) (Sum.elim x y) U:=by
    rw [value x y A B U,←lt U,←rt U,←Complex.ofReal_mul,Complex.ofReal_re]
  change _ = (↑((reads (pair A B) S u (Sum.elim x y) g).re-(reads A S u x g).re*(reads B S u y g).re):ℂ)
  rw [Complex.ofReal_sub,Complex.ofReal_mul,read S u _ _ both g,read S u _ _ lt g,read S u _ _ rt g]

end YM.Integration.WilsonMatrixTicketLanesConnectedReality
