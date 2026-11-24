import YM.Integration.WilsonPositionProgramReflectedPurse

/-! The two native separated profile values multiply to the original
mass-one reflected test at its two real, independently displaced positions. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionProgramReflectedRead
open Function Set Filter MeasureTheory WithLp Table.Pairing Lattice Wilson WilsonCoeffUV.Mer
open WilsonCoeffUV.Embroider WilsonMaxwellThermometerReflectedIncidence WilsonPositionProgramReflectedPurse
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge}

theorem sample (a:Axis)(x:E4)(B:Table.Pairing.Bulb (site x) a)(y z:Points 1):
    shape a x B 0 ((closedUp a y z 0).ofLp) * shape a x B 1 ((closedUp a y z 1).ofLp) =
      mass a x B (y,z) := by
  unfold shape mass
  congr 1 <;> apply congrArg B.r <;> apply PiLp.ext <;> intro j <;> fin_cases j
  · change (if (0:Fin 2)=0 then (Signed.reflect a).motion.toContinuousLinearEquiv
      else ContinuousLinearEquiv.refl ℝ _) _ = _
    rw [if_pos rfl]
    change ride a (closedUp a y z (Fin.castAdd 1 (0:Fin 1))) = y 0
    rw [enter,riding]
  · change (if (1:Fin 2)=0 then (Signed.reflect a).motion.toContinuousLinearEquiv
      else ContinuousLinearEquiv.refl ℝ _) _ = _
    rw [if_neg (by decide)]
    exact leave a y z (0:Fin 1)

def reading (Q:Fin 2→SealR G)(a:Axis)(φ:Wilt Q)(w:Pair):ℝ:=
  (φ 0).ψ.val (closedUp a w.1 w.2 0).ofLp * (φ 1).ψ.val (closedUp a w.1 w.2 1).ofLp

theorem original (Q:Fin 2→SealR G)(a:Axis)(x:E4)(B:Table.Pairing.Bulb (site x) a)(δ:ℝ):
    ∃φ:Wilt Q,∃fees:Fin 2→ℝ,(∀ᶠ Z:ℝ in atTop,Bough Q φ δ Z fees) ∧
      reading Q a φ=mass a x B ∧ (∫w:Pair,reading Q a φ w)=1 := by
  obtain ⟨φ,eq,fees,bought⟩:=WilsonPositionProgramReflectedPurse.original Q a x B δ
  have same:reading Q a φ=mass a x B:=by
    funext w
    unfold reading
    rw [eq 0,eq 1]
    exact sample a x B w.1 w.2
  refine ⟨φ,fees,bought,same,?_⟩
  rw [same]
  exact WilsonMaxwellThermometerReflectedIncidence.one a x B

end YM.Integration.WilsonPositionProgramReflectedRead
end
