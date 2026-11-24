import YangMills.WilsonProof.NativeSupport.IssuedBridge.OriginalPhaseWords
set_option autoImplicit false
noncomputable section
namespace IssuedBridge.OriginalTrainGeometry
open YangMills YangMills.Wilson YM YM.Spec YM.OPE.Orbits
open Filter Function Set
open scoped Topology NNReal
variable {g : GaugeGroup} {C : Family g.core}

def shift (j n : ℕ) : YM.E4 := EuclideanSpace.single YangMills.timeAxis ((j : ℝ) * (n : ℝ))

theorem flight {i j : ℕ} (h : i < j) : YM.OS.Ground.flight (shift i) (shift j) := by
  have pos : (0:ℝ) < (j:ℝ)-(i:ℝ) := sub_pos.mpr (by exact_mod_cast h)
  have eqn : (fun n : ℕ => ((shift j n)-(shift i n)) YM.timeAxis) =
      (fun n : ℕ => ((j:ℝ)-(i:ℝ))*(n:ℝ)) := by
    funext n
    simp [shift, PiLp.sub_apply, YM.timeAxis, YangMills.timeAxis, sub_mul]
  rw [YM.OS.Ground.flight, eqn]
  exact Filter.Tendsto.const_mul_atTop pos tendsto_natCast_atTop_atTop

def cars {k : ℕ} (v : Fin k → YM.Row.Core C.book) : List (YM.OS.Ground.Car C.book) :=
  List.ofFn fun j => (v j, shift j.val)

theorem line {k : ℕ} (v : Fin k → YM.Row.Core C.book) : YM.OS.Ground.line (cars v) := by
  apply List.pairwise_ofFn.mpr
  intro i j h
  exact flight h

end IssuedBridge.OriginalTrainGeometry
end
