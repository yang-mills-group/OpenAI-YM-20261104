import YM.Integration.FVA1Physical.Wilson.SceneReadout
import YM.Integration.FVA1Physical.Round2.StageThreshold
import YM.Integration.RunFormalChain

/-! Buy the inherited Wilson reading on one genuine physical construction,
including the moving profile thresholds at every RG stage before testing. -/
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
theorem run_haar_readout {goal : Qlocal.Schedule.Goal G} (extra : Qlocal.Schedule.Obtainable goal)
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
          ∀ φ:Config G A.f→ℝ, GaugeLocal A.S (youth A.F (boxY y b)) φ → 0≤φ → (∀ U,φ U≤1) →
            |forestTicket A J y z b B φ-expect A.S A.pre (represent (tint G (Exterior.Body 1 A.c) z)) φ|
              ≤ 10*A.fClock^((p:ℝ)+1-η) := by
  haveI := hG.nontrivial_color
  have degree : 0 < G.lieDim := by rw [Gauge.lieDim,← G.colorIso.finrank_eq]; exact Module.finrank_pos
  let u : G.ColorIndex := ⟨0,degree⟩
  obtain ⟨J,clear⟩ := MSbar.Heath.vocals G
  let gate := forestGate J clear hG hD (sub_pos.mpr hord) (half_pos hη)
  have proposal := (extra.also (Qlocal.Schedule.selectedThreshold_obtainable (G:=G) gate)).also
    (Qlocal.Schedule.vacuumInvoice_obtainable hG u J clear)
  obtain ⟨R,penalty,⟨grant,threshold⟩,invoice⟩ := Run.rampK hG proposal b₀ hb
  obtain ⟨docket,poetry⟩ := Qlocal.Schedule.docket_of_invoice hG R u J invoice
  have growth : Tendsto (fun i=>(R.alloy.B.a.params i).order) atTop atTop := by
    apply tendsto_atTop.2
    intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hj
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hj).1)
  have estate := invoice.1 growth
  have ch := (R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  refine ⟨R,u,J,penalty,grant,clear,docket,poetry,?_⟩
  filter_upwards [inherited_haar_readout (RunFormalChain.fromRun R) u hG R.T.choice docket J clear s p m
    hs hm hp hD hη hord] with k funded
  intro N n hN
  obtain ⟨S,scene,readout⟩ := funded N n hN
  refine ⟨S,scene,?_⟩
  intro j jk hj T h tag F choice L A y B
  have season := auditorium R.b R.Q R.T R.t R.stories R.doors ch J N n j hj hG estate.sees
    (fun k=>invoice.2.1 _ _ (R.alloy.B.valid.pays k) _ (step_paid R.alloy.B.a k))
  exact readout j jk hj T h tag F choice (threshold j n) season

end YM.Integration.FVA1Physical.Wilson
