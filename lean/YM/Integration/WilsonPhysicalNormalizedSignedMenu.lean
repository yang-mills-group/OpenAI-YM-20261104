import YM.Integration.WilsonPhysicalNormalizationSurvey
import YM.Integration.WilsonPhysicalPositionSurveyTariff

/-! The authentic finite position fit consumes only its signed determining bank and the appointed target row. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalNormalizedSignedMenu
open Filter Function Set Maxwell Maxwell.Free XSpace XSpace.Normalize
open WilsonPhysicalPositionTargetRows WilsonPhysicalPositionSurveyTariff WilsonPhysicalNormalizationSurvey
open scoped Classical BigOperators ContDiff Topology
variable {G:Gauge}{d n:ℕ}{I:Type}{A:Screen G d}(D:Fray A)(H:A.Prepared)
variable (home:Fin n→I)(v:Fin n→Sec G d)

abbrev Row (G:Gauge)(d n:ℕ):=MultilinearMap ℂ (fun _:Fin n=>Sec G d) ℂ

def docket (P:I→Prediction G d):I→D.Bag:=fun h=>D.purse (P h)
def retag (s:I→Change G d)(P:I→Prediction G d):I→Prediction G d:=fun h=>recruit (stand (s h)) (P h)
def offered (s:I→Change G d)(M:Row G d n):Row G d n:=M.compLinearMap (fun j=>stand (s (home j)))
def positioned (P:I→Prediction G d)(M:Row G d n):ℂ:=
  M (fun j=>stand (D.firstPass H (P (home j))) (v j))

theorem original {ι:Type*}(u:Filter ι)[Fintype I]:
    ∃ C:ℝ,0<C ∧ ∀ (P Q:ι→I→Prediction G d)(s:ι→I→Change G d)
      (_:∀ h,D.Via (fun i=>P i h) (u:=u))(_:∀h,D.Via (fun i=>Q i h) (u:=u))
      (_:∀h,Tendsto (fun i=>guide G d (s i h)) u (𝓝 0))(M W:ι→Row G d n),
      ∀ᶠ i in u,‖positioned D H home v (P i) (M i)-positioned D H home v (Q i) (W i)‖≤
        C*(‖rows (M i)-rows (offered home (s i) (W i))‖+
          ‖docket D (P i)-docket D (retag (s i) (Q i))‖*‖rows (offered home (s i) (W i))‖):=by
  obtain ⟨C,hC,U,hU,pay⟩:=invoice D H home v
  refine ⟨C,hC,?_⟩
  intro P Q s warm bare oriented M W
  have ready:Tendsto (fun i=>docket D (P i)) u (𝓝 (fun _:I=>D.opening.1)):=
    tendsto_pi_nhds.mpr warm
  have other:Tendsto (fun i=>docket D (retag (s i) (Q i))) u (𝓝 (fun _:I=>D.opening.1)):=
    tendsto_pi_nhds.mpr fun h=>admitted D _ _ (bare h) (oriented h)
  have same:∀ᶠ i in u,∀h:I,stand (s i h)*stand (D.firstPass H (retag (s i) (Q i) h))=
      stand (D.firstPass H (Q i h)):=
    Filter.eventually_all.mpr fun h=>slice D _ _ H (bare h) (oriented h)
  filter_upwards [ready.eventually hU,other.eventually hU,same] with i actual model exactFrame
  have bound:=pay _ actual _ model (rows (M i)) (rows (offered home (s i) (W i)))
  change ‖operator D H home v (fun h=>D.purse (P i h)) (rows (M i))-
    operator D H home v (fun h=>D.purse (retag (s i) (Q i) h)) (rows (offered home (s i) (W i)))‖≤_ at bound
  rw [published,published] at bound
  have exactTarget:offered home (s i) (W i) (fun j=>stand (D.firstPass H (retag (s i) (Q i) (home j))) (v j))=
      positioned D H home v (Q i) (W i):=by
    change W i (fun j=>(stand (s i (home j))*stand (D.firstPass H (retag (s i) (Q i) (home j)))) (v j))=_
    simp_rw [exactFrame]
    rfl
  rw [exactTarget] at bound
  exact bound

end YM.Integration.WilsonPhysicalNormalizedSignedMenu
