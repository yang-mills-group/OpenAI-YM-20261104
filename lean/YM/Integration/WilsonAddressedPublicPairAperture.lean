import YM.Integration.WilsonOriginalPublicRelativeGramAddresses
import YM.Integration.WilsonAddressedPublicPairGeometry

/-! Genuine discrete reflected probe locations under the purchased physical wall. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonAddressedPublicPairAperture
open Function Filter Finset Lattice RG Wilson Source Labels Extraction
open PhysicalNext.Repeat.Legato
open WilsonOriginalPublicRelativeGramAddresses (ports shape)
open scoped Classical Topology
variable {G:Gauge}(R:Run G)

theorem original {Z L:Type}[Fintype L](l:Filter Z)(sites:Z→ℕ)(zoom wall:Z→ℝ)
    (positive:∀ᶠ z in l,0 < zoom z)(small:Tendsto zoom l (𝓝 0))
    (fine:Tendsto (fun z=>R.family.S.a (sites z)/zoom z) l (𝓝 0))
    (room:Tendsto (fun z=>wall z/zoom z) l (𝓝 0))
    (W:L→Finset E4)(x:L→Points 2)(distinct:∀a,(x a).ofLp 0≠(x a).ofLp 1):
    ∀ᶠ z in l,∀a:L,
    let p:=ports R (W a) (x a) (sites z) (zoom z)
    ‖R.family.S.gridPoint (sites z) (p 0-p 1)‖ ≤ 1 ∧
    2*wall z < ‖R.family.S.gridPoint (sites z) (p 0)-R.family.S.gridPoint (sites z) (p 1)‖:=by
  classical
  let δ:=fun z=>R.family.S.a (sites z)/zoom z
  apply eventually_all.mpr
  intro a
  let trial:=fun z=>shape (W a) (x a) (δ z)
  have shaped:Tendsto trial l (𝓝 (x a)):=WilsonOriginalPublicRelativeGramAddresses.limit
    (W a) (x a) (positive.mono fun z hp=>div_pos (R.family.S.a_pos _) hp) fine
  let coord:Points 2 ≃L[ℝ] (Fin 2→E4):=PiLp.continuousLinearEquiv 2 ℝ _
  have projected:=tendsto_pi_nhds.mp ((coord.continuous.tendsto (x a)).comp shaped)
  let span:=fun z=>‖(trial z).ofLp 0-(trial z).ofLp 1‖
  have current:Tendsto span l (𝓝 ‖(x a).ofLp 0-(x a).ofLp 1‖):=( (projected 0).sub (projected 1)).norm
  have nonzero:0<‖(x a).ofLp 0-(x a).ofLp 1‖:=norm_pos_iff.mpr (sub_ne_zero.mpr (distinct a))
  have below:(∀ᶠ z in l,2*(wall z/zoom z)<span z):=
    Filter.Tendsto.eventually_lt (show Tendsto (fun z=>2*(wall z/zoom z)) l (𝓝 0) by
      simpa only [mul_zero] using room.const_mul 2) current nonzero
  have upper:∀ᶠ z in l,zoom z*span z ≤ 1:= (show Tendsto (fun z=>zoom z*span z) l (𝓝 0) by
    simpa only [zero_mul] using small.mul current).eventually_le_const zero_lt_one
  filter_upwards [positive,below,upper] with z hp h₁ h₂
  intro p
  have atPoint(i:Fin 2):R.family.S.gridPoint (sites z) (p i)=zoom z • (trial z).ofLp i:=
    congrArg (fun y:Points 2=>y.ofLp i) (WilsonOriginalPublicRelativeGramAddresses.placed
      R (W a) (x a) (sites z) hp)
  rw [Frontier6.Road.grid_sub R.family,atPoint 0,atPoint 1,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hp]
  refine ⟨h₂,?_⟩
  have paid:2*wall z/zoom z<span z:=by simpa only [mul_div_assoc] using h₁
  simpa only [mul_comm (span z)] using (div_lt_iff₀ hp).mp paid

end YM.Integration.WilsonAddressedPublicPairAperture
end
