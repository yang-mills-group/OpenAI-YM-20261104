import YM.Integration.FVA1Physical.Round2.PurchasedRootedField
import YM.Integration.FVA1Physical.Round2.CommonWordPrices

/-! The physical trajectory and its forest are selected before all fixed
orders, cutoffs, periods, placements, word backgrounds, and requested losses.
The same trajectory supplies the independently normalized Wilson action. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.Integration.FVA1Physical.Round2.Curvature
open Function Filter Finset Lattice RG YM.Wilson Precision RG.Supply Input Org Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat.Legato Cub Circlet Graces Roost Qlocal.Schedule
open YM.Integration.FVA1Physical.Wilson Integration.FVA1Physical.Marked RGComparison.Core16.Spool
open MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Midpoint MSbar.Cacao MSbar.CrossH MSbar.Whisk MSbar.Lis
open MSbar.Mosaic Tree Pressure Push.Uniform Exterior
open scoped Classical Topology BigOperators
variable {G : Gauge} {I : Type} [Fintype I] {d : ℕ} (a : I → CoverLabel G d)

def rootedFieldMenu : StageThreshold := fun H H' P K =>
  ∑ i : ReadingInputs H.order, |chargeGate a i.1 i.2.1 i.2.2.1 (margin_pos i.2.2.2.1) H H' P K|

theorem bought_field_gate (R : PhysicalNext.Repeat.Legato.Run G)
    (cash : selectedThreshold (rootedFieldMenu a) R.metals R.rolls R.alloy R.kit)
    (q s radius h : ℕ) : LateThreshold R (chargeGate a q s radius (margin_pos h)) := by
  let demand := q+s+radius+h
  filter_upwards [eventually_ge_atTop (R.t demand)] with k cut j kj n
  let H := R.alloy.B.a.params j
  let H' := R.alloy.B.a.params (j+1)
  let P := (R.alloy.B.a.clock.op j n).patch
  let K := (R.alloy.B.a.clock.op j n).kernel
  have ord : demand ≤ H.order := (Nat.le_succ demand).trans (((R.makes.stages demand).2 j (cut.trans kj)).1)
  dsimp only [demand] at ord
  let i : ReadingInputs H.order := (⟨q,by omega⟩,⟨s,by omega⟩,⟨radius,by omega⟩,⟨h,by omega⟩,false)
  let fee := fun i : ReadingInputs H.order => chargeGate a i.1 i.2.1 i.2.2.1 (margin_pos i.2.2.2.1) H H' P K
  exact (le_abs_self (fee i)).trans ((single_le_sum (fun t _ => abs_nonneg (fee t)) (mem_univ i)).trans (cash j n))

theorem rooted_field_trajectory {goal : Goal G} (extra : Obtainable goal) (hG : G.Simple)
    (penalty : ℝ) (pos : 0 < penalty) :
    ∃ (R : PhysicalNext.Repeat.Legato.Run G) (u : G.ColorIndex),
      R.family.path.levels.clock.kernel.penalty=penalty ∧ goal R.metals R.rolls R.alloy R.kit ∧
      R.metals.O=chart G ∧ ThermalConnectedReadings (freshLamps a) R u ∧
      ∀ p q s L radius : ℕ, 0 < q → 6 ≤ s → ∀ D η : ℝ, 0 ≤ D → 0 < η →
        CurrentRooted a R u p q s L radius D η := by
  obtain ⟨R,u,V,clear,fee,⟨keep,menu⟩,frame,words,rows,marks,_⟩ := field_word_trajectory (freshLamps a)
    (extra.also (selectedThreshold_obtainable (G:=G) (rootedFieldMenu a))) hG penalty pos
  refine ⟨R,u,fee,keep,frame,marks,?_⟩
  intro p q s L radius hq hs D η hD hη
  obtain ⟨m,hm⟩ := margin_eventually (derivative_clock p 0 0 le_rfl hη).1
  exact physical_rooted_on a R u hG V clear words rows p q s L radius hq hs hD hη (margin_pos m) hm
    (bought_field_gate a R menu q (s+s) radius m)

end YM.Integration.FVA1Physical.Round2.Curvature
