import YM.Integration.PhysicalWilsonPeriodizedMaterial

/-! Evaluate the actual periodic material in its jointly shifted affine chart.
All marked directions use their enrolled power and the original group word.
The quiet coupling letter is the negative cubic of the full measured action. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerAffineVertices
open Finset Function Matrix Lattice Wilson RG RG.Supply Precision Tree Exterior Laurent Bloch
open Marker Multi PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Order
open Comparison.RG02.Cumulants Next.Rank Next.SectorChange WilsonCoeffUV FreeResolvent MeasureTheory
open scoped Classical BigOperators
variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] {Γ : Census V}
variable {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (W : Bulk.Colors Γ G f)
  (y : Bulk.Joint S F (G:=G)) (r : ℕ)
local notation "Z" z:max => Assembly.translate y (Bulk.hinge F) z
local notation "letter" => PhysicalWilsonPeriodizedMaterial.drawn K F W y r

/-- Every enrolled mark, including an inherited mixed entry, has its own
joint field Taylor derivative on this same affine Gaussian. -/
theorem occupied (s : Hot (Board Γ r)) (hs : (Join.left s.val).val.Nonempty)
    (z : Key F G → ℝ) :
    let n := (Join.right s.val).val.card
    Cloud.paint z (letter s) =
      (n.factorial:ℂ)*Assembly.jet (PhysicalWilsonJointMaterial.mark S F W ⟨_,hs⟩)
        (W.power ⟨_,hs⟩+n) (Z z) := by
  intro n
  dsimp only [n]
  simp only [PhysicalWilsonPeriodizedMaterial.drawn,Assembly.generator,dif_pos hs,map_smul,
    smul_eq_mul,Assembly.reading]

/-- The single quiet coupling occurrence contains the whole cubic of the
measured action, taken before the older Wilson vacuum is integrated. -/
theorem quiet (s : Hot (Board Γ r)) (hs : ¬ (Join.left s.val).val.Nonempty)
    (d : (Join.right s.val).val.card=1) (z : Key F G → ℝ) :
    Cloud.paint z (letter s) =
      -(Assembly.jet (PhysicalWilsonJointMaterial.measured S F W p P O) 3 (Z z):ℝ) := by
  simp only [PhysicalWilsonPeriodizedMaterial.drawn,Assembly.generator,dif_neg hs,d,Nat.factorial_one,
    Nat.cast_one,one_smul,Assembly.readingVacuum,Assembly.vacuumLetter,one_ne_zero,↓reduceIte,
    Nat.reduceAdd,Complex.ofReal_neg]

end YM.Integration.WilsonThermometerAffineVertices
