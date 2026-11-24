import YM.Integration.WilsonMaxwellThermometerNominatedTrajectory

/-! The numerical labels, group-field polarizations and Laurent weights of
the original three filed arms are restored on their own issued polynomial. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerNominatedPupils
open Lattice RG Wilson Precision Tree Laurent FormalBulk08 Flat Mesa
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Soil
open WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open PhysicalNext.Repeat.Legato Labels Source Next.Foundations
open WilsonNeutralCopiedProgram WilsonNeutralOffsetCutoff WilsonNeutralNominatedFiniteTable
open WilsonMaxwellThermometerNominatedAlgebra WilsonMaxwellThermometerNominatedTrajectory
open scoped BigOperators Classical Topology

variable {G:Gauge} (R:Run G) (A:WilsonPositionThermometerCapStation.Group R.family 6)
variable (N per:ℕ) (caps:Fin 3→ℕ)
local notation "d" => WilsonOriginalThermometerPalette.levels
variable (w:∀i,d i<caps i) (phase:Fin 3→ℂ→ₗ[ℝ]ℝ) (h:Fin 3→ℝ)
local notation "F(" π ")" => top R A N per caps w π
local notation "declared" => named R A N per
local notation "g" => ConnectedActivityE6.Coat.gStep (R.family.beta N per)

private theorem translated {I:Type} [DecidableEq I] {D:I→ℕ} {c:ℝ} {j:I}
    (P:TowerS G (D j)) (z:Cover) : cn D j (c • P) z=c • cn D j P z := by
  unfold cn
  rw [currency]
  apply Prod.ext <;> rfl

theorem same : F(fun i=>h i • phase i) = fun y=>scaled h (F(phase) y) := by
  funext y S
  have input:=birth R d caps w N per declared phase g y
  have moved:=birth R d caps w N per declared (fun i=>h i • phase i) g y
  by_cases single:S.card=1
  · obtain ⟨i,rfl⟩:=Finset.card_eq_one.mp single
    change F(fun j=>h j • phase j) y {i}=pay h {i} • F(phase) y {i}
    rw [show F(fun j=>h j • phase j) y {i}=_ from moved.1 i,
      show F(phase) y {i}=_ from input.1 i]
    simp only [pay,Finset.prod_singleton]
    rw [←translated (D:=caps) (j:=i),Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    congr 1
    unfold fee
    change (h i * _)*_=h i*(_*_)
    exact mul_assoc ..
  · change F(fun j=>h j • phase j) y S=pay h S • F(phase) y S
    rw [show F(fun i=>h i • phase i) y S=0 from moved.2 S single,
      show F(phase) y S=0 from input.2 S single,smul_zero]

theorem fitted (simple:G.Simple) {j:ℕ} (hn:j≤N) (y:Fin 3 → Cover) (S:Finset (Fin 3)) :
    let run:=Gears R.family.path.levels R.metals.O d d N N j
    run F(fun i=>h i • phase i) y S=pay h S • run F(phase) y S ∧
      levelsO (run F(fun i=>h i • phase i) y) S=pay h S • levelsO (run F(phase) y) S := by
  intro run
  have valid:=healthy R A N per caps w phase
  have entry:=same R A N per caps w phase h
  have moved : run F(fun i=>h i • phase i) y=scaled h (run F(phase) y) := by
    funext T
    rw [entry]
    exact history R.family.path.levels R.metals.O d d N N le_rfl simple R.alloy.B.ratio
      F(phase) valid h hn y T
  rw [moved]
  exact ⟨rfl,exponential h _ S⟩

end YM.Integration.WilsonMaxwellThermometerNominatedPupils
