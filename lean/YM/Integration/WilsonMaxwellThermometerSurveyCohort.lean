import YM.Integration.WilsonMaxwellThermometerSurveyFields
import YM.Integration.WilsonMaxwellThermometerSurveyInversion
import YM.Integration.WilsonPositionProgramInvertedCohort
/-! The complete two-slot polynomial of the public master is the actual public bare Taylor program on this finite pad. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace YM.Integration.WilsonMaxwellThermometerSurveyCohort
open Set Function Filter Finset Matrix PowerSeries Lattice Wilson RG PhysicalNext.Repeat.Legato
open Precision XSpace Labels Source PertExtension.Orb
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Power
open WilsonCoeffUV.Shard WilsonCoeffUV.Embroider WilsonCoeffUV.Blue
open WilsonPositionProgramInversionAlgebra WilsonPositionProgramInvertedStencil
open WilsonPositionProgramInversionMaterial
open scoped Classical BigOperators Topology
open WilsonMaxwellThermometerSurveyIncome (chapter master)
open WilsonMaxwellThermometerReflectedPhysicalColumns (levels)
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G)(W:Initialize G)(p:Period)
variable (d:Fin 2→ℕ)(fit:∀i,levels i<d i)(z:Fin 2 → Cover)
local notation "T" => W.tree p
local notation "F" j => R.family.labels.level (levels j)
local notation "rank" j => WilsonPositionProgramMasterBirth.rank R (d:=levels j)
theorem assembled (w : (j : Fin 2) → Verse (F j)) (b : (j : Fin 2) → Volume (d j))
    (running : Fin 2 → Ink (Woods G p.side))
    (issued : ∀ j, (X:Ink (Woods G p.side))^(rank j) * running j =
      loom (spear (jog (wrap p.side (z j)) : Woods G p.side ≃ Woods G p.side))
        (∑ s, X^((rank j)-valence (F j) s)*soil (w j s)*
          (jewelBloom (fit j) s (b j) • jet (Plies (chapter W (levels j)) (sheet (F j) s) p.side)))) :
    packet T (X^ceiling R levels * ∏ j,running j) =
      WilsonMaxwellThermometerSurveyInversion.raw R W p z (dose R levels w d fit b) := by
  have one j : packet T (X^(rank j)*running j) = ∑ s : Alma (F j),
      (income T (X^((rank j)-valence (F j) s) *
        (PowerSeries.map (algebraMap ℝ ℂ) (w j s)*C ((jewelBloom (fit j) s (b j):ℝ):ℂ)))) *
          Taylor.expandTaylor ((W.tree p).basis G) (fun x=>(chapter W (levels j)).places (Pi.single (sheet (F j) s) 1) (wrap p.side (z j)) ((W.tree p).links x)) := by
    rw [issued j,map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro s _
    rw [WilsonPositionProgramInversionAlgebra.term,WilsonMaxwellThermometerSurveyFields.literal]
  have group : (X:Ink (Woods G p.side))^ceiling R levels * ∏ j,running j =
      ∏ j, X^(rank j)*running j := by rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum];rfl
  rw [group,map_prod]
  simp_rw [one]
  rw [Finset.prod_univ_sum,WilsonMaxwellThermometerSurveyInversion.raw]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.prod_mul_distrib,WilsonPositionProgramInvertedCohort.pay R T levels d fit]
  exact congrArg (fun v=> Bare.scalar T (X^(ceiling R levels-degree R levels a)*dose R levels w d fit b a)*v)
    ((WilsonPositionProgramInvertedWords.multiply T
      (WilsonThermometerPositionTunedChange.letter R W p T levels z (axis R levels a))
      (WilsonThermometerPositionTunedChange.smooth R W p T levels z (axis R levels a)) univ).2).symm

end YM.Integration.WilsonMaxwellThermometerSurveyCohort
end
