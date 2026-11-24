import YM.Integration.FVA1Physical.Wilson.RunNormalized
import YM.Integration.FVA1Physical.Wilson.OrbitMenu

/-! One measured physical theory pays simultaneously for every finite perturbative
order, every bounded field horizon and every positive loss in the coupling exponent. -/
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

/-- A single purchased Run and one shared independent coupling history for every
fixed order, every finite chart radius and every allowed exponent. The numerical
gate and physical positivity are paid before the initial cutoff, periods and tests. -/
theorem all_orders_orbit {goal : Qlocal.Schedule.Goal G} (extra : Qlocal.Schedule.Obtainable goal)
    (hG : G.Simple) (b₀ : ℝ) (hb : 0 < b₀) :
    ∃ (R : Run G) (u : G.ColorIndex) (J : Voice G),
      R.family.path.levels.clock.kernel.penalty=b₀ ∧ goal R.metals R.rolls R.alloy R.kit ∧
      Clear G J ∧ Docket R.family u R.metals.O R.alloy.B.M R.alloy.B.kin ∧
      OPE.Therm.Poetry R.family.path.levels ∧
      ∀ (p s m : ℕ), 6 ≤ s → 4 ≤ m → p+3 ≤ m →
      ∀ (D η : ℝ), 0 ≤ D → 0 < η → η < (p:ℝ)+1 →
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
          ∀ φ:Config G A.f→ℝ, GaugeLocal A.S (youth A.F (boxY y b)) φ → (∀ U,|φ U|≤1) →
            |expect A.S A.pre O (innerOrbit A J y z b B φ)-expect A.S A.pre O φ| ≤ 9*A.fClock^((p:ℝ)+1-η) := by
  haveI := hG.nontrivial_color
  have degree : 0 < G.lieDim := by rw [Gauge.lieDim,← G.colorIso.finrank_eq]; exact Module.finrank_pos
  let u : G.ColorIndex := ⟨0,degree⟩
  obtain ⟨J,clear⟩ := MSbar.Heath.vocals G
  let gate := orbitMenu J clear hG
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
  intro p s m hs hm hp D η hD hη hηp
  obtain ⟨d,hd⟩ := exists_nat_ge D
  obtain ⟨i,hi⟩ := margin_eventually hη
  have financed := inherited_orbit (RunFormalChain.fromRun R) u hG R.T.choice docket J clear s p m
    hs hm hp (Nat.cast_nonneg (α:=ℝ) d) (margin_pos i) (sub_pos.mp (margin_fits p i))
  let demand := max d (max p i)
  filter_upwards [financed,eventually_ge_atTop (R.t demand),
    actual_clock_small R.family.path (q:=1) zero_lt_one zero_lt_one hG R.T.choice] with k funded menu unit
  intro N n hN
  obtain ⟨S,scene,readout⟩ := funded N n hN
  refine ⟨S,scene,?_⟩
  intro j jk hj T h tag F choice L A y B z b hz O φ loc bound
  have order : demand ≤ (R.alloy.B.a.params j).order :=
    (Nat.le_succ demand).trans (((R.makes.stages demand).2 j (menu.trans jk)).1)
  have actualGate := (orbitMenu_le J clear hG _ _ A.S.patch A.S.kernel
    ((le_max_left d (max p i)).trans order) (((le_max_left p i).trans (le_max_right d _)).trans order)
    (((le_max_right p i).trans (le_max_right d _)).trans order)).trans (threshold j n)
  have season := auditorium R.b R.Q R.T R.t R.stories R.doors ch J N n j hj hG estate.sees
    (fun k'=>invoice.2.1 _ _ (R.alloy.B.valid.pays k') _ (step_paid R.alloy.B.a k'))
  have low : y/2 ≤ A.pre.beta := (R.T.choice.represents N n (j+1) hj).band.1
  have y₀ : 1 < y := R.family.path.levels.fits.delayed (j+1)
  have hg : 0 < A.fClock := inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos (zero_lt_one.trans y₀)).trans_le low))
  have g1 := unit (j+1) (jk.trans (Nat.le_succ _)) N n hj
  change A.fClock^(1:ℝ) ≤ 1 at g1
  rw [Real.rpow_one] at g1
  have H := readout j jk hj T h tag F choice actualGate season z b
    (hz.trans (mul_le_mul_of_nonneg_left hd hg.le))
  have exponent := Real.rpow_le_rpow_of_exponent_ge hg g1 (sub_le_sub_left hi ((p:ℝ)+1))
  exact (H φ loc bound).trans (mul_le_mul_of_nonneg_left exponent (by norm_num))

end YM.Integration.FVA1Physical.Wilson
