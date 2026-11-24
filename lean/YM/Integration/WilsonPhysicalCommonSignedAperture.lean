import YM.Integration.WilsonPhysicalNormalizedSignedMenu

/-! One event for all reported target positions, after the genuine public phase determination. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalCommonSignedAperture
open WilsonPhysicalNormalizedSignedMenu
open Filter Function Set Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionTargetRows WilsonPhysicalPositionSurveyTariff WilsonPhysicalNormalizationSurvey
open scoped Classical BigOperators ContDiff Topology
variable {G:Gauge}{d n:ℕ}{I:Type}{A:Screen G d}(D:Fray A)(H:A.Prepared)
variable (home:Fin n→I)(v:Fin n→Sec G d)

theorem original {ι:Type*}(u:Filter ι)[Fintype I]:
    ∃ C:ℝ,0<C ∧ ∀ (P Q:ι→I→Prediction G d)(s:ι→I→Change G d)
      (_:∀ h,D.Via (fun i=>P i h) (u:=u))(_:∀h,D.Via (fun i=>Q i h) (u:=u))
      (_:∀h,Tendsto (fun i=>guide G d (s i h)) u (𝓝 0)),
      ∀ᶠ i in u,∀M W:Row G d n,‖positioned D H home v (P i) M-positioned D H home v (Q i) W‖≤
        C*(‖rows M-rows (offered home (s i) W)‖+
          ‖docket D (P i)-docket D (retag (s i) (Q i))‖*‖rows (offered home (s i) W)‖):=by
  obtain ⟨C,hC,U,hU,pay⟩:=invoice D H home v
  refine ⟨C,hC,?_⟩
  intro P Q s warm bare oriented
  have ready:Tendsto (fun i=>docket D (P i)) u (𝓝 (fun _:I=>D.opening.1)):=
    tendsto_pi_nhds.mpr warm
  have other:Tendsto (fun i=>docket D (retag (s i) (Q i))) u (𝓝 (fun _:I=>D.opening.1)):=
    tendsto_pi_nhds.mpr fun h=>admitted D _ _ (bare h) (oriented h)
  have same:∀ᶠ i in u,∀h:I,stand (s i h)*stand (D.firstPass H (retag (s i) (Q i) h))=
      stand (D.firstPass H (Q i h)):=
    Filter.eventually_all.mpr fun h=>slice D _ _ H (bare h) (oriented h)
  filter_upwards [ready.eventually hU,other.eventually hU,same] with i actual model exactFrame M W
  have bound:=pay _ actual _ model (rows M) (rows (offered home (s i) W))
  change ‖operator D H home v (fun h=>D.purse (P i h)) (rows M)-
    operator D H home v (fun h=>D.purse (retag (s i) (Q i) h)) (rows (offered home (s i) W))‖≤_ at bound
  rw [published,published] at bound
  have exactTarget:offered home (s i) W (fun j=>stand (D.firstPass H (retag (s i) (Q i) (home j))) (v j))=
      positioned D H home v (Q i) W:=by
    change W (fun j=>(stand (s i (home j))*stand (D.firstPass H (retag (s i) (Q i) (home j)))) (v j))=_
    simp_rw [exactFrame]
    rfl
  rw [exactTarget] at bound
  exact bound

end YM.Integration.WilsonPhysicalCommonSignedAperture
