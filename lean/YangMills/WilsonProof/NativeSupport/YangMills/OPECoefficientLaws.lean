import YangMills.OPECoefficientLaws
import YangMills.WilsonProof.NativeSupport.YangMills.CorrelationHierarchy

/-! Intrinsic laws for the coefficients appearing in the physical OPE sums. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.Hierarchy
open Function Filter
open scoped BigOperators Classical Topology
variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)



/-- A zero actor would have coordinate zero by multilinearity and coordinate one
by duality. This excludes zero-channel padding even if every spectator ignores it. -/
theorem CoefficientLaws.actor_ne_zero {T : Hierarchy C} (laws : T.CoefficientLaws)
    (w : ℕ) (c : T.Channel w) : T.actor w c ≠ 0 := by
  intro zero
  change T.channelField w c = 0 at zero
  obtain ⟨L, hL⟩ := laws.multilinear (fun _ : Unit => w) w c (fun _ => 0) 0
  have dual := laws.dual w c c
  unfold singletonCoordinate at dual
  rw [if_pos rfl, zero, hL, L.map_coord_zero () rfl] at dual
  exact zero_ne_one dual


end YangMills.Hierarchy
