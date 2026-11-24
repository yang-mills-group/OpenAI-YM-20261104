import YM.Integration.FVA1Physical.Wilson.PurchasedOrbit
import YM.Integration.FVA1Physical.Wilson.SceneReadout
import YM.Integration.FVA1Physical.Wilson.CylinderOscillation
import YM.Integration.FVA1Physical.Wilson.InheritedPatch

/-! The inherited, period-uniform full Haar reading against the independently
descended FVA2 Wilson energy, on one selected physical scene at every depth. -/
set_option autoImplicit false
set_option maxHeartbeats 720000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior RGComparison.Core16
open FVA2.CityHistory PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open MSbar MSbar.Lis MSbar.Whisk MSbar.Rolling MSbar.Midpoint MSbar.Wave MSbar.Bakery MSbar.Cacao Comparison.RG02 Push Push.Uniform
open MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Bulk SectorNext.Vacuum Mosaic
open PhysicalNext.Repeat.Legato
open scoped Classical Topology
variable {G : Gauge}

noncomputable def orbitGate (J : Voice G) (cle : Clear G J) (simple : G.Simple)
    {D q η : ℝ} (hD : 0≤D) (hq : 0<q) (hη : 0<η)
    (H H' : Stage) (P : Patch) (K : KernelChoices) : ℝ :=
  if h : P.Branches K G then orbitThreshold J cle simple H H' P K h hD hq hη else 0

variable {C : Family G} (L : Bulk.Chain C.path) {N n j r : ℕ}

theorem inherited_orbit (u : G.ColorIndex) (simple : G.Simple) (sel : C.path.Selected)
    (docket : Docket C u L.O L.horizon L.kin) (J : Voice G) (cle : Clear G J)
    (s p m : ℕ) (hs : 6 ≤ s) (hm : 4 ≤ m) (hp : p+3 ≤ m)
    {D η : ℝ} (hD : 0≤D) (hη : 0<η) (hpos : η < (p:ℝ)+1) :
    ∀ᶠ k:ℕ in atTop, ∀ N n, k≤N → ∃ S : Scene C.path.levels n (p+1),
      Realized L.kin N n k (p+1) (Lis.sun G u) S ∧
      ∀ j, k≤j → ∀ hj:j<N, ∀ (T : Slices C.path.levels n) (h : (traversal T hj).Room G) (tag : (traversal T hj).Tags)
        (F : Forest (C.path.levels.clock.op j n).ratio) (v : (C.path.levels.clock.op j n).Choices),
        let A := sceneIssue (N:=N) L S F v
        let x := C.path.levels.clock.hatBeta j
        let y := C.path.levels.clock.hatBeta (j+1)
        let q := (p:ℝ)+1-η
        let H := C.path.levels.params j
        let H' := C.path.levels.params (j+1)
        let B := boundaryBank L S T hj h tag p A.fClock
        orbitGate J cle simple hD (sub_pos.mpr hpos) (half_pos hη) H H' A.S.patch A.S.kernel ≤ x →
        Season J H H' x A.pre A.post A.S (courage G A.S.patch.L x) →
        ∀ (z:Positions (Primary A.c G)) (b:Site A.f), ‖z‖≤A.fClock*D →
          ∀ φ:Config G A.f→ℝ, GaugeLocal A.S (youth A.F (boxY y b)) φ → (∀ U,|φ U|≤1) →
          |expect A.S A.pre (represent (tint G (Exterior.Body 1 A.c) z)) (innerOrbit A J y z b B φ) -
           expect A.S A.pre (represent (tint G (Exterior.Body 1 A.c) z)) φ| ≤ 9*A.fClock^q := by
  filter_upwards [uniform_patch_oscillation L u simple sel docket s p m hs hm hp (half_pos hη)] with k funded
  intro N n start
  obtain ⟨S,scene,rows⟩:=funded N n start
  refine ⟨S,scene,?_⟩
  intro j jk hj T h tag F v A x y q H H' B gate season z b hz φ mφ hφ
  have branch := season.bends.1
  rw [orbitGate,dif_pos branch] at gate
  have avail := (eventually_atTop.mp (purchased_orbit J cle simple H H' A.S.patch A.S.kernel branch
    hD (sub_pos.mpr hpos) (half_pos hη))).choose_spec x gate
  have height : tip G A.S.patch.L x = y := (Extra.Iteration.block_beta (a:=C.path.levels) j).symm
  have cont := continuous_bank L S T hj h tag scene (jk.trans (Nat.le_succ j)) p (Nat.le_succ p) A.fClock
  have bill := avail A z b rfl rfl season hz B cont
  dsimp only at bill
  rw [height] at bill
  apply bill _ φ mφ hφ
  intro a v'
  have paid := rows (j+1) (jk.trans (Nat.le_succ j)) hj T h tag a v'
  change _ → _ ≤ _ at paid
  intro ht
  have pr := paid ht
  change _ ≤ (∑ i,|v' i|)*(A.fClock^((p:ℝ)+1-η/2)/Mosaic.vol y) at pr
  rw [show (p:ℝ)+1-η+η/2 = (p:ℝ)+1-η/2 by ring]
  exact pr

end YM.Integration.FVA1Physical.Wilson
