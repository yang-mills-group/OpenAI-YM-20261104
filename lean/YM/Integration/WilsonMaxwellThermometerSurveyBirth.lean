import YM.Integration.WilsonMaxwellThermometerSurveyCourse
import YM.Integration.WilsonPositionProgramMasterBirth
/-! The complete independently normalized source returns its own registered Taylor stencil at the honest auxiliary top. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true

namespace YM.Integration.WilsonMaxwellThermometerSurveyBirth
open Finset Lattice Wilson RG Source Labels PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Cosmos WilsonCoeffUV.Soil
open WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Power
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open scoped BigOperators Classical
variable {G : Gauge} {d D : ℕ} (R : Run G)
variable (W:XSpace.Initialize G)
open WilsonMaxwellThermometerSurveyIncome (chapter master)
local notation "T" => chapter W d
local notation "RANK" => WilsonPositionProgramMasterBirth.rank R (d:=d)


theorem assembly (w : d < D) (N : ℕ) (n : Side) (v : Verse ((primes G).F d)) (b : Volume D) :
    let Y := Shrine (Peaks R.family.path.levels R.metals.O T w N N) v
    PowerSeries.X ^ RANK * flash (jot b (Y.1 n)) =
      ∑ s, PowerSeries.X ^ (RANK - valence ((primes G).F d) s) * Blue.soil (v s) *
        (jewelBloom w s b • jet (Plies T (sheet ((primes G).F d) s) n)) := by
  intro Y
  let H := RANK
  let K := fun s => herald T w s n
  have below s : valence ((primes G).F d) s ≤ H := Finset.le_sup (f:=valence ((primes G).F d)) (mem_univ s)
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
    ←herald_lit T w s n b ((master W).pop d) (Next.Foundations.hol G) ((master W).spec d)]
  change PowerSeries.X ^ H * _ = (PowerSeries.X ^ (H-valence ((primes G).F d) s) * _ * (PowerSeries.X ^ valence ((primes G).F d) s * _))
  rw [show H = (H-valence ((primes G).F d) s)+valence ((primes G).F d) s from (Nat.sub_add_cancel (below s)).symm,
    pow_add]
  simp only [Nat.add_sub_cancel]
  ring

theorem original (w : d < D) (N m : ℕ) (n : Side) (X : Verse ((primes G).F d)) (b : Volume D) :
    let Q := BayV (master W) d D w
    let x := PermuteLens R.family.path.levels R.metals.O Q N m X
    let v := steep R.family.path.levels R.metals.O T w N m (N-m) x
    let Y := WilsonCoeffUV.Wheel.Mark.centralL R.family.path.levels R.metals.O N m N Q x
    PowerSeries.X ^ RANK * flash (jot b (Y.1 n)) =
      ∑ s, PowerSeries.X ^ (RANK-valence ((primes G).F d) s) * Blue.soil (v s) *
        (jewelBloom w s b • jet (Plies T (sheet ((primes G).F d) s) n)) := by
  intro Q x v Y
  exact assembly R W w N n v b

end YM.Integration.WilsonMaxwellThermometerSurveyBirth
end
