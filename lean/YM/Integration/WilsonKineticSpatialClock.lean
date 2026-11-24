import YM.Integration.WilsonKineticFullPeriod
import YM.Integration.WilsonKineticRebookingContinuity
import YM.Integration.WilsonConditionalTaylorBulkClock

/-! The two marked renormalization factors of an arbitrary actual
finite spatial course. All finite tori enter and the numerator is its
original complete signed rank-two row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonKineticSpatialClock
open Function Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open FormalBulk08 Flat Reef Orb Series Jets Shore Lava Kemp Wine Roof
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary Lotus
open Mesa Gorge City Cork Rift Pose Glide Bank Dawn Rial Dove
open Planned.PrimaryIntegral295 Source Source.Drops Labels PhysicalNext.Repeat.Legato
open MSbar MSbar.Rolling MSbar.Midpoint MSbar.Heath WilsonMovingPolynomialPull
open WilsonConditionalTaylorKineticRebooking
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) (a : G.ColorIndex) (N j : ℕ)
  (U : (n : Side) → Pap (wire G n))

def finite (n : Side) :=
  WilsonConditionalTaylorBulkClock.field (Lis.sun G a) (R.alloy.B.kin.path N j)
    (R.family.path.levels.params j).clip (U n)

theorem positive (e : ℕ) (paid : 0<e) (n : Side) :
    coeff e (finite R a N j U n) =
      -(WilsonKineticResponseLimit.finite a U e n) / WilsonKineticFullPeriod.bill R a N j n := by
  rw [finite,WilsonConditionalTaylorBulkClock.field,primitive,map_sub,coeff_one,if_neg paid.ne',
    coeff_C_mul,projection,coeff_mk,splitV,map_sub,coeff_C,if_neg paid.ne',sub_zero,coeff_map]
  unfold WilsonKineticResponseLimit.finite WilsonKineticFullPeriod.bill
  simp only [place,coeff_map]
  ring

variable (simple : G.Simple) (roofs : ∀i,Lodge ((R.family.path.levels.clock.op i 0).patch))
  (T : Mesa.Pot G) (p : ℕ) (hi : j≤N)
include simple roofs hi in
theorem full (civic : ∀ᶠ n in atTop,Civic (U n)) (head : Fresh (Wine.scalar a T))
    (paid : ∀ e,0<e → e≤p → ∃η : ℝ,0<η ∧ Kith η (T e 2) (fun n=>rancho (U n) e 2)) :
    let H := finite R a N j U
    let C := Wine.scalar a T
    ∀ e≤p, Tendsto (fun n=>coeff e (H n)) atTop (𝓝 (coeff e C)) ∧
      Tendsto (fun n=>coeff e (bookH (H n))) atTop (𝓝 (coeff e (bookH C))) ∧
      Tendsto (fun n=>coeff e (bookU (H n))) atTop (𝓝 (coeff e (bookU C))) := by
  intro H C
  have born (n) : Fresh (H n) := WilsonConditionalTaylorBulkClock.fresh .. 
  have income (e : ℕ) (bound : e≤p) : Tendsto (fun n=>coeff e (H n)) atTop (𝓝 (coeff e C)) := by
    by_cases eq : e=0
    · subst e
      simp only [show ∀n,coeff 0 (H n)=1 from born,show coeff 0 C=1 from head]
      exact tendsto_const_nhds
    have useful := Nat.pos_of_ne_zero eq
    obtain ⟨η,pos,wire⟩ := paid e useful bound
    have num := WilsonKineticResponseLimit.raw a U e (T e 2) civic pos wire
    have den := WilsonKineticFullPeriod.limit R a simple roofs N j hi
    have cover := num.neg.div den (show (-2:ℝ)≠0 by norm_num)
    have cost : -(2*Cork.value a (T e 2)) / (-2) = coeff e C := by
      rw [show coeff e C=Cork.value a (T e 2) from PowerSeries.coeff_mk ..]
      ring
    rw [cost] at cover
    exact cover.congr (fun n=>(positive R a N j U e useful n).symm)
  intro e he
  exact ⟨income e he,WilsonKineticRebookingContinuity.forward p H C born head income e he,
    WilsonKineticRebookingContinuity.inverse p H C born head income e he⟩

end YM.Integration.WilsonKineticSpatialClock
end
