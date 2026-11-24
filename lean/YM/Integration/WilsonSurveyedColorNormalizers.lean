import YM.Integration.WilsonSurveyedColorOpenIndex
import YM.XSpace.Clan

/-! On a connected compact simple color group a Cartan-form isometry
normalizes its adjoint action. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSurveyedColorNormalizers
open Function Filter Set XSpace XSpace.Stab XSpace.Stab.OJoint
open WilsonSurveyedColorTensor WilsonSurveyedColorCurvature WilsonSurveyedColorOpenIndex
open scoped Topology Classical
variable {G : Gauge}

theorem groupAction [PreconnectedSpace G.El] (hG : G.Simple)
    (U : G.Color ≃ₗᵢ[ℝ] G.Color) (same : Preserves U) : Normalizes U := by
  obtain ⟨s, hs⟩ := OJoint.available U
  have acts (x : G.Color) : Spin s x = U x :=
    congrArg (fun f : Module.End ℝ G.Color => f x) hs
  have ha : Homed s := by
    intro x y
    simp only [acts]
    exact bracket U same x y
  let J : G.El →* Knight G :=
    ⟨⟨intoClan G, enters_one G⟩, fun x y => entry_mul x y⟩
  let C : G.El →* Knight G := {
    toFun g := s * intoClan G g * s⁻¹
    map_one' := by rw [enters_one]; group
    map_mul' x y := by rw [entry_mul]; group }
  let H : Subgroup G.El := J.range.comap C
  have hc : Continuous C :=
    (continuous_const.mul (entry_cont G)).mul continuous_const
  have ct : Tendsto C (𝓝 1) (𝓝 1) := by
    simpa only [ContinuousAt, map_one] using (hc.continuousAt (x := 1))
  have hn : (H : Set G.El) ∈ 𝓝 1 := by
    filter_upwards [ct.eventually (around hG)] with g hg
    exact hg ((ha.glob (always g)).glob ha.rev)
  have op := H.isOpen_of_mem_nhds hn
  have cl : IsClopen (H : Set G.El) := ⟨H.isClosed_of_isOpen op, op⟩
  have allH := cl.eq_univ ⟨1,H.one_mem⟩
  intro g
  have hg : g ∈ H := by
    change g ∈ (H : Set G.El)
    rw [allH]
    exact mem_univ g
  obtain ⟨t,ht⟩ := hg
  change intoClan G t = s * intoClan G g * s⁻¹ at ht
  have h : intoClan G t * s = s * intoClan G g := by rw [ht]; group
  exact ⟨t, fun x => by
    simpa only [spin_mul, enters, acts] using
      congrArg (fun k : Knight G => Spin k x) h.symm⟩

end YM.Integration.WilsonSurveyedColorNormalizers
end
