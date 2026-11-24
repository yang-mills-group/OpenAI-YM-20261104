import YM.Integration.WilsonPointChildCenteredFunctional
import YM.Integration.WilsonPointChildDigitHierarchy
import YM.Integration.WilsonPointChildCenteredBasis
import YM.Integration.WilsonPointChildDigitIncome
import YM.Integration.WilsonPointChildNamedSalary
import YM.Integration.WilsonPointChildPairedHistory
import YM.Integration.WilsonPointChildFoldedField
import YM.Integration.WilsonPointChildDigitReturn
import YM.Integration.WilsonPointChildDigitLedger
import YM.Integration.WilsonPointChildHalfCell
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPointChildCenteredTensor
open Function Filter Finset Matrix Lattice Wilson RG Laurent PowerSeries Work.F08
open FormalBulk08 Flat Reef Jets Orb Wick Stationary Series Shore Gorge Lotus Mesa Rift Lava Dawn Kemp Roof Sierra Rial
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Winding
open YM Next.Foundations PhysicalNext.Repeat.Legato Pose Palm Quire Wine Dove WilsonCoeffUV.Embroider
open WilsonPointChildTestCoordinates WilsonNeutralPointCourse WilsonPointChildCoverStep
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{d D:ℕ}
open WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider.Canvas
open WilsonPointChildTestJet WilsonPointChildTestCoordinates WilsonCoeffUV.Wheel.Mark
variable {ι:Type}

open WilsonPointChildNamedBasis WilsonPointChildCenteredBasis
open WilsonCoeffUV.Bank.Carp
open WilsonPointChildCenteredFunctional (issue)

private theorem folded {V τ:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]
    [CompleteSpace V](S:Finset τ)(Z:τ → Era G V)(legal:∀t∈S,Auth d (Z t))
    (n:Side)(e r:ℕ):
    plume ((∑t∈S,Z t).2 e r) n=∑t∈S,plume ((Z t).2 e r) n:=by
  classical
  induction S using Finset.induction_on with
  | empty=>simp [plume_zero]
  | insert t S outside ih=>
    have old:∀b∈S,Auth d (Z b):=fun b hb=>legal b (Finset.mem_insert_of_mem hb)
    obtain ⟨w,A,hw,good⟩:=((legal t (Finset.mem_insert_self _ _)).wing e r).land
    obtain ⟨w',A',hw',good'⟩:=((Auth.sum old).wing e r).land
    simp only [Finset.sum_insert outside,Prod.snd_add,Pi.add_apply]
    rw [plume_add good good' hw hw' n,ih old]

theorem finite {d:ℕ}{τ:Type}[Fintype τ]{V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]
    [CompleteSpace V](Z:τ → Era G ℝ)(L:τ → ℝ →L[ℝ] V)(legal:∀t,Auth d (Z t))
    (n:Side)(e r:ℕ)(x:Fin r → Bloch.Co n (Hooks G)):
    ‖(∑t,tuftV (L t) (Z t)).1 n e r x-plume ((∑t,tuftV (L t) (Z t)).2 e r) n x‖≤
      ∑t,‖L t‖*|(Z t).1 n e r x-plume ((Z t).2 e r) n x|:=by
  classical
  let Y(t:τ):Era G V:=tuftV (L t) (Z t)
  have hY(t:τ):Auth d (Y t):=(legal t).tuft (L t)
  change ‖(∑t,Y t).1 n e r x-plume ((∑t,Y t).2 e r) n x‖≤_
  rw [folded Finset.univ Y (fun t _=>hY t) n e r,Prod.fst_sum]
  simp only [Finset.sum_apply,←Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _=>?_)
  obtain ⟨s,A,hs,bound⟩:=((legal t).wing e r).land
  change ‖L t ((Z t).1 n e r x)-plume (L t ∘ (Z t).2 e r) n x‖≤_
  rw [plume_map _ bound hs (L t) n]
  simpa only [Function.comp_apply,←map_sub,Real.norm_eq_abs] using (L t).le_opNorm (((Z t).1 n e r x)-plume ((Z t).2 e r) n x)

end YM.Integration.WilsonPointChildCenteredTensor
