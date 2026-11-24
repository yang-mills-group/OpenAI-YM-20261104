import YM.Integration.FVA1Physical.Wilson.DistributedForce
import YM.Integration.FVA1Physical.Wilson.AllOrdersSchur

/-! The distributed action and its inserted force use the actual canonical Haar
chart of the selected FVA2 chain. A finite menu at each stage pays for every
fixed perturbative order and support exponent on one measured trajectory. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Qlocal.Schedule
open Function Filter Set Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Classical Topology
variable {G : Gauge}

/-- This is the chart actually used by the existing launch construction. -/
def fixedWilsonChart : Goal G := fun M _ _ _=>M.O=chart G

theorem fixedWilsonChart_obtainable : Obtainable (fixedWilsonChart (G:=G)) := by
  intro s T C z R E hdr
  refine ⟨fun _=>0,?_⟩
  intro l hl D w v Z F S pocket records admissible P menu V
  refine ⟨V,DelayLe.refl _,?_⟩
  intro V' later cost bar wait price B archive shape exchange η q b bt guide J hf hv hw ha div
  rfl
end YM.Qlocal.Schedule

namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MeasureTheory Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling MSbar.Midpoint
open PhysicalNext.Repeat.Legato Push.Uniform Pressure RGComparison.Core16 Next.SectorChange
open Extra.Iteration Push.PriceCompiler PhysicalNext.Repeat.Roost Next.Foundations
open scoped Classical Topology
variable {G : Gauge}

noncomputable def forceGate (J : Voice G) (clear : Clear G J) (hG:G.Simple)
    (H H' : Stage) (P : Patch) (K : KernelChoices) (p s : ℕ) : ℝ :=
  if h:P.Branches K G then
    (eventually_atTop.mp (distributed_force J clear (chart G) (chart_ok G) hG H H' P K h p s H.order
      (D:=(H.order:ℝ)) (Nat.cast_nonneg _))).choose else 0

noncomputable def forceMenu (J : Voice G) (clear : Clear G J) (hG:G.Simple)
    (H H' : Stage) (P : Patch) (K : KernelChoices) : ℝ :=
  ∑ i:Fin (H.order+1) × Fin (H.order+1), |forceGate J clear hG H H' P K i.1.val i.2.val|

theorem forceMenu_le (J : Voice G) (clear : Clear G J) (hG:G.Simple)
    (H H' : Stage) (P : Patch) (K : KernelChoices) {p s : ℕ} (hp:p ≤ H.order) (hs:s ≤ H.order) :
    forceGate J clear hG H H' P K p s ≤ forceMenu J clear hG H H' P K := by
  let i:Fin (H.order+1) × Fin (H.order+1):=(⟨p,by omega⟩,⟨s,by omega⟩)
  let f (z:Fin (H.order+1) × Fin (H.order+1)):=forceGate J clear hG H H' P K z.1.val z.2.val
  exact (le_abs_self (f i)).trans (single_le_sum (fun j _=>abs_nonneg (f j)) (mem_univ i))

/-- Every part of the input and rooted derivative budget is paid by this one
measured Wilson scene. The cutoff precedes the period, levels, forest, root,
exterior field and tested coefficient. -/
theorem all_orders_distributed_force {goal : Qlocal.Schedule.Goal G} (extra : Qlocal.Schedule.Obtainable goal)
    (hG : G.Simple) (b₀ : ℝ) (hb : 0<b₀) :
    ∃ (R : Run G) (u : G.ColorIndex) (J : Voice G),
      R.family.path.levels.clock.kernel.penalty=b₀ ∧ goal R.metals R.rolls R.alloy R.kit ∧
      R.metals.O=chart G ∧ Clear G J ∧ Docket R.family u R.metals.O R.alloy.B.M R.alloy.B.kin ∧
      OPE.Therm.Poetry R.family.path.levels ∧
      ∀ (p s q : ℕ), 6 ≤ s → ∀ (D:ℝ), 0 ≤ D →
      ∀ᶠ k:ℕ in atTop, ∀ N n, k ≤ N → ∃ S : Scene R.family.path.levels n p,
        Realized R.alloy.B.kin N n k p (Lis.sun G u) S ∧
        ∀ j, k ≤ j → j<N → ∀ (F:Forest (R.family.path.levels.clock.op j n).ratio)
          (v : (R.family.path.levels.clock.op j n).Choices),
          let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
          let y:=R.family.path.levels.clock.hatBeta (j+1)
          ∀ (z:Positions (Primary A.c G)) (e:Joint A.F G), ‖z‖ ≤ A.fClock*D →
            let b:=address A.F G e
            let src:=actionForce A R.metals.O e
            ∀ U∈hotel A.F (boxX y b) (boxY y b) J (represent (tint G (Exterior.Body 1 A.c) z))
              (vest (priced A.F A.v A.pre.clip A.pre.path) z) (pillow y) (room y),
            ∀ i ≤ p, |PowerSeries.coeff i (bulkColumn A R.metals.O z src p)-
              PowerSeries.coeff i (innerColumn A R.metals.O J y z b U src p)| ≤ y^(-(q:ℝ)) := by
  haveI:=hG.nontrivial_color
  have degree : 0<G.lieDim := by rw [Gauge.lieDim,←G.colorIso.finrank_eq]; exact Module.finrank_pos
  let u:G.ColorIndex:=⟨0,degree⟩
  obtain ⟨J,clear⟩:=MSbar.Heath.vocals G
  let gate:=forceMenu J clear hG
  have offer:=((extra.also Qlocal.Schedule.fixedWilsonChart_obtainable).also
    (Qlocal.Schedule.selectedThreshold_obtainable (G:=G) gate)).also (Qlocal.Schedule.vacuumInvoice_obtainable hG u J clear)
  obtain ⟨R,penalty,⟨⟨grant,hchart⟩,threshold⟩,invoice⟩:=Run.rampK hG offer b₀ hb
  obtain ⟨docket,poetry⟩:=Qlocal.Schedule.docket_of_invoice hG R u J invoice
  have growth : Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop := by
    apply tendsto_atTop.2; intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hj
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hj).1)
  have ch := (R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  refine ⟨R,u,J,penalty,grant,hchart,clear,docket,poetry,?_⟩
  intro p s q hs D hD
  obtain ⟨d,hd⟩:=exists_nat_ge D
  let demand:=max (max d q) (max p s)
  filter_upwards [docket.purse s p (p+4) hs (by omega) (by omega),eventually_ge_atTop (R.t demand)]
    with k funds menu
  intro N n hN
  obtain ⟨⟨S,scene⟩,budget⟩:=funds N n hN
  refine ⟨S,scene,?_⟩
  intro j jk hj F v A y z e hz b src U live i hi
  have order : demand ≤ (R.alloy.B.a.params j).order :=
    (Nat.le_succ demand).trans (((R.makes.stages demand).2 j (menu.trans jk)).1)
  have season:=auditorium R.b R.Q R.T R.t R.stories R.doors ch J N n j hj hG (invoice.1 growth).sees
    (fun k'=>invoice.2.1 _ _ (R.alloy.B.valid.pays k') _ (step_paid R.alloy.B.a k'))
  let H:=R.family.path.levels.params j
  let H':=R.family.path.levels.params (j+1)
  let x:=R.family.path.levels.clock.hatBeta j
  have branch : A.S.patch.Branches A.S.kernel G:=season.bends.1
  have cover : forceGate J clear hG H H' A.S.patch A.S.kernel p s ≤ x :=
    (forceMenu_le J clear hG _ _ _ _ (((le_max_left p s).trans (le_max_right ..)).trans order)
      (((le_max_right p s).trans (le_max_right ..)).trans order)).trans (threshold j n)
  rw [forceGate,dif_pos branch] at cover
  have take := (eventually_atTop.mp (distributed_force J clear (chart G) (chart_ok G) hG H H' A.S.patch A.S.kernel branch p s H.order
    (D:=(H.order:ℝ)) (Nat.cast_nonneg _))).choose_spec x cover
  have g0:0 ≤ A.fClock := by change 0 ≤ (Real.sqrt _)⁻¹; positivity
  have d' : d ≤ H.order := ((le_max_left d q).trans (le_max_left ..)).trans order
  have wider:= hz.trans (mul_le_mul_of_nonneg_left (hd.trans (Nat.cast_le.mpr d')) g0)
  have height : tip G A.S.patch.L x=y := (Extra.Iteration.block_beta (a:=R.family.path.levels) j).symm
  have use:=take A z e rfl rfl season wider
  dsimp only at use
  rw [height] at use
  have j₁:=jk.trans (Nat.le_succ j)
  have trend:=(scene.budget (j+1) hj j₁).1
  have wedge:=(budget S scene).2.2 (j+1) j₁ hj
  have claim:=use trend.bond trend.plane wedge U live i hi
  have qq : q ≤ H.order:= ((le_max_right d q).trans (le_max_left ..)).trans order
  have less := Real.rpow_le_rpow_of_exponent_le (R.family.path.levels.fits.delayed (j+1)).le
    (neg_le_neg (Nat.cast_le.mpr qq : (q:ℝ) ≤ H.order))
  change R.metals.O=chart G at hchart
  dsimp only [src]
  rw [hchart]
  exact claim.trans less
end YM.Integration.FVA1Physical.Wilson
