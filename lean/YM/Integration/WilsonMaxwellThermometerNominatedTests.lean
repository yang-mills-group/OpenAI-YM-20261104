import YM.Integration.WilsonNeutralNominatedScalarFaces

/-! Each reflected normalized test acts on precisely the occupied labels of
the finite prescribed bank. This also holds for its field-dependent vacuum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedTests
open Function Lattice RG Wilson Precision Tree Laurent
open FormalBulk08 Flat Mesa Next.Free Stationary
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonConditionalTaylorWheelConnectedReadout
open scoped Classical BigOperators

variable {I U : Type} {D : I → ℕ}

def applied (t:I→ℝ) (A:Case D) : Case D := fun i=>t i • A i

theorem sheet (t:I→ℝ) (A:Case D) (S:Finset I) :
    seaMark (applied t A) S=(∏i∈S,t i) • seaMark A S := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (∏i∈S,t i * slice (A i) (x i))=(∏i∈S,t i)*(∏i∈S,slice (A i) (x i))
  exact Finset.prod_mul_distrib

theorem evaluated (t:I→ℝ) (A:Case D) (S:Finset I) (P:Pal (Pen D S) U) :
    pPly (applied t A) S P=(∏i∈S,t i) • pPly A S P := by
  funext e r v
  change P e r v (seaMark (applied t A) S)= (∏i∈S,t i) • P e r v (seaMark A S)
  rw [sheet,map_smul]

theorem ordinary {G:Gauge} (t:I→ℝ) (A:Case D) (S:Finset I)
    (Z:Era G (Pen D S)) (n:Side) :
    (tuftV (touch (applied t A) S) Z).1 n=(∏i∈S,t i) • (tuftV (touch A S) Z).1 n ∧
    (tuftV (touch (applied t A) S) Z).2=(∏i∈S,t i) • (tuftV (touch A S) Z).2 :=
  ⟨evaluated t A S (Z.1 n),evaluated t A S Z.2⟩

theorem connected {G:Gauge} [DecidableEq I] (t:I→ℝ) (A:Case D) (S:Finset I)
    (Z:Era G (Pen D S)) (n:Side) :
    finiteRead (applied t A) S n Z=(∏i∈S,t i) • finiteRead A S n Z ∧
    read (applied t A) S Z=(∏i∈S,t i) • read A S Z :=
  ⟨evaluated t A S (Z.1 n),evaluated t A S Z.2⟩

end YM.Integration.WilsonMaxwellThermometerNominatedTests
