import YM.Integration.WilsonPositionProgramNormalizedMaster
import YM.WilsonCoeffUV.Root.UV.RawSemi

/-! The independently normalized top report is made of genuine section stencils.
At every angular probe the following identity restores their filed field ranks
before evaluating the full reporting-coupling series. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true

namespace YM.Integration.WilsonPositionProgramMasterBirth
open Finset Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open scoped BigOperators Classical
variable {G : Gauge} {d D : ℕ} (R : Run G)
local notation "F" => R.family.labels.level d
local notation "T" => R.family.localSection d

def rank : ℕ := univ.sup (valence F)

theorem assembly (w : d < D) (N : ℕ) (n : Side) (v : Verse F) (b : Volume D) :
    let Y := Shrine (Peaks R.family.path.levels R.metals.O T w N N) v
    PowerSeries.X ^ rank R (d:=d) * flash (jot b (Y.1 n)) =
      ∑ s, PowerSeries.X ^ (rank R (d:=d) - valence F s) * Blue.soil (v s) *
        (jewelBloom w s b • jet (Plies T (sheet F s) n)) := by
  intro Y
  let H := rank R (d:=d)
  let K := fun s => herald T w s n
  have below s : valence F s ≤ H := Finset.le_sup (f:=valence F) (mem_univ s)
  have shells s : shellK H (K s) := by
    intro k q hq
    exact herald_norm T w s n k q (by have := below s; omega)
  have assembled : Y.1 n = ∑ s, affix (v s) (K s) := by
    dsimp only [Y,Shrine,Stem,vein]
    rw [Peak_initial]
    simp only [Prod.fst_sum, Finset.sum_apply]
    rfl
  rw [assembled, map_sum, flash_term _ (fun s _ => jot_length _ (affix_shell _ _ (shells s))),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [jotAffix, sponsor _ _ (jot_length _ (shells s)),
    ←herald_lit T w s n b (Next.Foundations.valuation G d) R.family.params (R.makes.sections d)]
  change PowerSeries.X ^ H * _ = (PowerSeries.X ^ (H-valence F s) * _ * (PowerSeries.X ^ valence F s * _))
  rw [show H = (H-valence F s)+valence F s from (Nat.sub_add_cancel (below s)).symm,
    pow_add]
  simp only [Nat.add_sub_cancel]
  ring

theorem original (w : d < D) (N m : ℕ) (n : Side) (X : Verse F) (b : Volume D) :
    let Q := BayV (primes G) d D w
    let x := PermuteLens R.family.path.levels R.metals.O Q N m X
    let v := steep R.family.path.levels R.metals.O T w N m (N-m) x
    let Y := WilsonCoeffUV.Wheel.Mark.centralL R.family.path.levels R.metals.O N m N Q x
    PowerSeries.X ^ rank R (d:=d) * flash (jot b (Y.1 n)) =
      ∑ s, PowerSeries.X ^ (rank R (d:=d)-valence F s) * Blue.soil (v s) *
        (jewelBloom w s b • jet (Plies T (sheet F s) n)) := by
  intro Q x v Y
  exact assembly R w N n v b

end YM.Integration.WilsonPositionProgramMasterBirth
end
