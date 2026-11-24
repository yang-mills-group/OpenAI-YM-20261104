import YM.Integration.WilsonPositionProgramTrialFittedGrades

/-! Restore the native engineering width on the actual two-date chart before comparing the coordinates. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialGradeRuler
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Blue WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonPositionProgramTrialFittedLens (ticket)
open WilsonPositionProgramTrialFittedTable (head)
open scoped BigOperators Classical

open WilsonPositionProgramTrialFittedGrades (scale)
variable {G:Gauge}{e:ℕ}

theorem ruler (L:Levels G)(m k:ℕ):scale L m k=L.S.a m/L.S.a (m+k):=by
  induction k generalizing m with
  | zero =>simp [scale,(L.S.a_pos m).ne']
  | succ k ih =>
    rw [scale,show (loose L m).L=L.S.block m from rfl,ih,L.S.a_step]
    rw [show m+1+k=m+(k+1) by omega]
    have hn:((L.S.block m).val:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt (L.S.block m).property)
    field_simp [hn,(L.S.a_pos (m+(k+1))).ne']

def restored (L:Levels G)(O:ChartRatio G)(Q:SealR G)(N m K:ℕ):Wall Q.F:=
  fun i j=>identum (forwardW L O Q.ans Q.path N m (K-m)) i j*(L.S.a K/L.S.a m)^(Q.h-weight Q.F j)

theorem signed (H:Hol G)(Q:SealR G){C C':Credit}(T:Theatre H Q.ans Q.path e C C'){m K N:ℕ}
    (admitted:T.V.anchor ≤ m)(before:m ≤ K)(live:K ≤ N)(i j:Alma Q.F)(order:weight Q.F i ≤ weight Q.F j):
    restored T.V.draws T.V.paid Q N m K i j=(1:Wall Q.F) i j:=by
  unfold restored
  rw [WilsonPositionProgramTrialFittedGrades.original H Q T N m (K-m) admitted (by omega) i j order,
    ruler,Nat.add_sub_of_le before,Matrix.one_apply]
  by_cases eq:i=j
  · rw [if_pos eq,if_pos eq,←mul_pow]
    simp [(T.V.draws.S.a_pos m).ne',(T.V.draws.S.a_pos K).ne']
  · simp [eq]

end YM.Integration.WilsonPositionProgramTrialGradeRuler
