import YM.Integration.FVA1Physical.Wilson.RunReadout
import YM.Integration.FVA1Physical.Wilson.ForestNormalization
import YM.Integration.FVA1Physical.Wilson.ClockSmall

/-! Positivity of the new forest mass and the constant-mode normalization on
 the same calibrated physical construction at every inherited stage. -/
set_option autoImplicit false
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk SectorNext.Vacuum Mosaic
open PhysicalNext.Repeat.Legato Extra.Iteration Push.PriceCompiler PhysicalNext.Repeat.Roost
open scoped Classical Topology
variable {G : Gauge}

/-- Both cutoff and period are quantified after choosing the same physical family,
stationary maps and Wilson scene. The cells' stage thresholds, true atmospheric
estimates and full interacting denominators are all discharged. -/
theorem run_normalized_haar {goal : Qlocal.Schedule.Goal G} (extra : Qlocal.Schedule.Obtainable goal)
    (hG : G.Simple) (b₀ : ℝ) (hb : 0<b₀) (p s m : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m) (hp : p+3 ≤ m)
    {D η : ℝ} (hD : 0≤D) (hη : 0<η) (hord : η<(p:ℝ)+1) :
    ∃ (R : Run G) (u : G.ColorIndex) (J : Voice G),
      R.family.path.levels.clock.kernel.penalty=b₀ ∧ goal R.metals R.rolls R.alloy R.kit ∧
      Clear G J ∧ Docket R.family u R.metals.O R.alloy.B.M R.alloy.B.kin ∧
      OPE.Therm.Poetry R.family.path.levels ∧
      ∀ᶠ k:ℕ in atTop, ∀ N n, k≤N → ∃ S : Scene R.family.path.levels n (p+1),
        Realized R.alloy.B.kin N n k (p+1) (Lis.sun G u) S ∧
        ∀ j, k≤j → ∀ hj:j<N, ∀ (T : Slices R.family.path.levels n) (h : (traversal T hj).Room G)
          (tag : (traversal T hj).Tags) (F : Forest (R.family.path.levels.clock.op j n).ratio)
          (choice : (R.family.path.levels.clock.op j n).Choices),
          let L := RunFormalChain.fromRun R
          let A := sceneIssue (N:=N) L S F choice
          let y := R.family.path.levels.clock.hatBeta (j+1)
          let B := boundaryBank L S T hj h tag p A.fClock
          ∀ (z:Positions (Primary A.c G)) (b:Site A.f), ‖z‖≤A.fClock*D →
          let O := represent (tint G (Exterior.Body 1 A.c) z)
          let Z := A.S.push A.pre.beta A.pre.eval O
          let mass := forestMass A J y z b B
          Z/2 ≤ mass 1 ∧ 0 < mass 1 ∧ ∀ φ:Config G A.f→ℝ, GaugeLocal A.S (youth A.F (boxY y b)) φ → 0≤φ → (∀ U,φ U≤1) →
            |mass φ/mass 1-expect A.S A.pre O φ| ≤ 40*A.fClock^((p:ℝ)+1-η) := by
  obtain ⟨R,u,J,penalty,grant,clear,docket,poetry,physical⟩ :=
    run_haar_readout extra hG b₀ hb p s m hs hm hp hD hη hord
  refine ⟨R,u,J,penalty,grant,clear,docket,poetry,?_⟩
  filter_upwards [physical,actual_clock_small R.family.path (sub_pos.mpr hord)
    (by norm_num : 0 < (1/20:ℝ)) hG R.T.choice] with k paid small
  intro N n kN
  obtain ⟨S,scene,out⟩:=paid N n kN
  refine ⟨S,scene,?_⟩
  intro j jk hj T h tag F choice L A y B z b hz O Z mass
  have read := out j jk hj T h tag F choice z b hz
  have high := small (j+1) (jk.trans (Nat.le_succ j)) N n hj
  change A.fClock^((p:ℝ)+1-η) ≤ 1/20 at high
  have cap : 10*A.fClock^((p:ℝ)+1-η) ≤ 1/2 := by linarith only [high]
  let H := R.family.path.levels.params (j+1)
  let clock := R.family.path.levels.clock
  have mass₀ : 0<Z := by
    have eq : (R.family.path.rep N n j).eval O=Z := congrFun (R.T.choice.steps N n j hj).1 O
    exact (strictly R.family.path R.T.choice N n j hj.le O).trans_eq eq
  have adm : Admitted O A.pre A.S H.width H.paths (clock.allowance (j+1)) (clock.loopCap (j+1)) (clock.forcedAllowance (j+1)) :=
    ⟨(R.T.choice.represents N n (j+1) hj).good,
     fun U=>(strictly R.family.path R.T.choice N n (j+1) hj U).le,mass₀,
     R.family.path.levels.transition_mass j n A.pre.beta⟩
  have bill := forest_normalize A J y z b B adm cap read
  refine ⟨bill.1,bill.2.1,fun φ loc pos bounded=>?_⟩
  exact (bill.2.2 φ loc pos bounded).trans_eq (by ring)

end YM.Integration.FVA1Physical.Wilson
