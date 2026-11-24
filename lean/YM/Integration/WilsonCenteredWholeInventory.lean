import YM.Integration.WilsonCenteredOccupiedFamilies
import YM.Integration.WilsonCenteredFullDensity
import YM.Comparison.RG02.Cumulants.Partition

/-! Expansion of an arbitrary whole occupied face in the original Wilson
gallery. Each selected hard set leaves its exact original eligible complement.
The soft part keeps all partitions, including deposited mixed subwords. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonCenteredWholeInventory
open Finset RG Wilson Marker Lattice QuadraticLocal Multi Comparison.RG02.Cumulants
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {V X ι : Type} [DecidableEq V] [Fintype V]
    {o : V→Site n} {R : Census V} {P : Rep G n}
    (H : Hard X P.p P.activities.forced P.activities.K o R)

def onHard (x : X) (U : Config G n) (s : R.Mode) (F : Finset ℕ) : ℂ :=
  if P.activities.admissible P.p U F then
    ∑ I∈F.powerset.filter (fun I=>I.card ≤ s.val.card),
      (∏j∈F\I,(P.activities.K j U:ℂ)) * (∏ j∈I,WilsonCenteredOccupiedFamilies.dye s (H.hard x j U)).part s
  else 0

omit [Fintype V] in
theorem collection (x : X) (U : Config G n) (s : R.Mode) (F : Finset ℕ) :
    (Fusion.Attached.packet P.activities P.p (H.hard x) U F).part s = onHard H x U s F := by
  by_cases actual : P.activities.admissible P.p U F
  · simpa only [Fusion.Attached.packet,onHard,if_pos actual,H.quiet] using
      WilsonCenteredOccupiedFamilies.original F (fun j=>H.hard x j U) s
  simp [Fusion.Attached.packet,onHard,actual]

variable (A : Gallery X ι o P R)
theorem original (x : X) (U : Config G n) (s : R.Mode)
    (soft : Summable (fun j=>A.E.frame j x U))
    (old : Summable (Fusion.Attached.packet P.activities P.p (A.K.hard x) U)) :
    (A.density x U).part s = (Real.exp (P.exponent U):ℂ) *
      ∑ t:R.Mode,∑ u:R.Mode,if Poly.merges t u s then
        (∑ D∈shards R t, ∏ h∈D.val,(A.E.log x U).part h.val) *
          (∑' F,onHard A.K x U u F) else 0 :=by
  have marked : (A.E.log x U).part R.quiet=0 := Lamps.quiet_of_hasSum x U soft
  have gas (u : R.Mode) : (A.gas x U).part u=∑' F,onHard A.K x U u F :=by
    have h : HasSum (fun F=>(Fusion.Attached.packet P.activities P.p (A.K.hard x) U F).part u)
        ((A.gas x U).part u) := (Poly.get u).hasSum old.hasSum
    exact ((h.congr_fun (fun F=>(collection A.K x U u F).symm)).tsum_eq).symm
  simp only [Gallery.density,Poly.part_smul,Poly.part_mul,pass_partition _ marked,gas]

end YM.Integration.WilsonCenteredWholeInventory
