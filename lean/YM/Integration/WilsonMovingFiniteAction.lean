import YM.Integration.WilsonMovingForestRestriction
import YM.Integration.WilsonMovingJointAction
import YM.Integration.WilsonMovingPolynomialPull
import YM.Integration.WilsonMovingVacuumRows

/-! Full identification of the normalized finite action on the original
geometric block. The incoming polynomial is arbitrary and may retain all
interactions and all coupling orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMovingFiniteAction
open Function Filter PowerSeries Matrix Lattice RG Wilson Precision Tree Exterior Push.Uniform
open FormalBulk08 Jets Series Orb Reef MSbar.Rolling WilsonMovingPolynomialPull
open scoped Classical Topology ContDiff Matrix
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio)

theorem inherited (p : Pap (wire G f)) :
    place (WilsonMovingJointAction.index F) (Reef.seat F p) =
      PowerSeries.map (rail (taps F G)).toRingHom
        (place (WilsonMovingGaussianCoordinates.link G f).symm p) := by
  apply detected
  intro v
  rw [placed, linear, placed]
  change glimpse (WilsonMovingJointAction.joint F v) (Reef.seat F p) = _
  rw [WilsonMovingForestRestriction.seat]
  unfold taps
  rw [LinearMap.toMatrix'_mulVec]
  apply congrArg (fun y => glimpse y p)
  funext i
  have h := congrFun (WilsonMovingJointAction.fine F v) ((WilsonMovingGaussianCoordinates.link G f).symm i)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.comp_apply] using h

theorem penalty (branch : S.patch.Branches S.kernel G) (t : S.Choices) :
    place (WilsonMovingJointAction.index F) (Jets.paste (Reef.clack S t ∘ Reef.graft F)) =
      Jets.paste (pushChart F G t) := by
  have h : ContDiffAt ℝ ∞ (clack S t ∘ graft (G:=G) F) 0 := by
    apply ContDiffAt.comp (f:=graft F) 0
    · rw [graft_origin]
      exact (discord S branch t).of_le le_top
    · exact (graft_receipt F).of_le le_top
  rw [place, WilsonMovingTaylorConvention.placed _ _ h]
  exact congrArg Jets.paste (funext (WilsonMovingJointAction.noise F t))

theorem haar (O : ChartRatio G) (hO : LocalRatio O) :
    place (WilsonMovingJointAction.index F)
      (Jets.paste (fun v : Rays (Pine G S F ⊕ wire G c) => Real.log (sap F O (v ∘ Sum.inl)))) =
        Jets.paste (swung F O) := by
  have sub : ContDiffAt ℝ ∞ (fun x : Rays (Pine G S F ⊕ wire G c) =>
      x ∘ Sum.inl (β:=wire G c)) 0 := by
    change ContDiffAt ℝ ∞ (fun (x : Rays (Pine G S F ⊕ wire G c)) (i : Pine G S F) => x (.inl i)) 0
    fun_prop
  have hlog := (sap_smooth F O hO).log (by rw [sap_root F O hO]; exact one_ne_zero)
  have h : ContDiffAt ℝ ∞ (fun v : Rays (Pine G S F ⊕ wire G c) =>
      Real.log (sap F O (v ∘ Sum.inl))) 0 :=
    hlog.comp (f:=fun x : Rays (Pine G S F ⊕ wire G c) => x ∘ Sum.inl) 0 sub
  rw [place, WilsonMovingTaylorConvention.placed _ _ h]
  apply WilsonMovingPolynomialPull.germ
  exact (WilsonMovingJointAction.jacobian F O hO).symm

private theorem after {I J : Type} (s : I → J) (T : Pap I) (k : ℕ) :
    place s (Jets.afterX T k) = Jets.afterX (place s T) k := by
  ext n
  simp only [place, PowerSeries.coeff_map, Jets.after_one]

private theorem atZero {I : Type} (T : Pap I) : Jets.afterX T 0 = T := by
  ext n
  simp only [Jets.after_one,zero_add]

theorem primitive (p : Pap (wire G f)) (branch : S.patch.Branches S.kernel G)
    (t : S.Choices) (O : ChartRatio G) (hO : LocalRatio O) :
    place (WilsonMovingJointAction.index F) (Reef.flush F t O p) =
      PowerSeries.map (rail (taps F G)).toRingHom
        (place (WilsonMovingGaussianCoordinates.link G f).symm p) -
        singularity (pushChart F G t) 2 + singularity (swung F O) 0 := by
  have prep := strip _ _ _ _ (Primer.prepare S F p branch t hO)
  rw [prep]
  rw [show ∀ a b d : Pap (Pine G S F ⊕ wire G c),
    place (WilsonMovingJointAction.index F) (a-b+d) =
      place (WilsonMovingJointAction.index F) a - place (WilsonMovingJointAction.index F) b +
        place (WilsonMovingJointAction.index F) d from fun a b d => by
          simp only [place,map_add,map_sub]]
  change place (WilsonMovingJointAction.index F) (Reef.seat F p) -
    place (WilsonMovingJointAction.index F) (Jets.afterX (Jets.paste (clack S t ∘ graft F)) 2) +
    place (WilsonMovingJointAction.index F) (Jets.paste (fun v => Real.log (sap F O (v ∘ Sum.inl)))) = _
  rw [inherited, after, penalty F branch t, haar F O hO, WilsonMovingVacuumRows.shifted,
    WilsonMovingVacuumRows.shifted, atZero]

theorem positive (p : Pap (wire G f)) (branch : S.patch.Branches S.kernel G)
    (t : S.Choices) (O : ChartRatio G) (hO : LocalRatio O) :
    splitV (place (WilsonMovingJointAction.index F) (Reef.flush F t O p)) =
      barbed F t O (splitV (place (WilsonMovingGaussianCoordinates.link G f).symm p)) := by
  rw [primitive F p branch t O hO]
  unfold barbed splitV
  simp only [map_sub, map_add, PowerSeries.coeff_map, PowerSeries.map_C]
  ring

end YM.Integration.WilsonMovingFiniteAction
end
