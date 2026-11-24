import YM.Integration.WilsonIndependentCapturedValence
import YM.Integration.WilsonIndependentFreshScalar

/-! A complete marked history and a newly filed word agree on their later
coefficients through any order authenticated at capture. The finite winding
at capture is kept separate from the corresponding cover coefficients. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedHistory
open RegulatorIR RegulatorIR.Budget RegulatorIR.Diagram RegulatorIR.Ledger RegulatorIR.Ledger.Sky
open RegulatorIR.Step RegulatorIR.Sources RegulatorIR.Cluster RegulatorIR.Uniform
variable {W : Type} {M : W → ℕ} {X Y : Page M → Type} (S : Sky X Y) (T : S.Accounts)
variable {p m n u : ℕ} {L : Meter W} (B : S.Primitive L p u) (b : Choice M)
variable (old : T.Report m) (filed : (b.after.part S T B).Report n)

private theorem survivesFinite {A C U V : Type} {P : ℝ} {D : Deck P A U} {F : Deck P C V}
    (step : GridStep D F) (quiet : Orders U) {R Z : Orders U}
    (same : ∀ i, i ≤ p → R i = Z i) {e : ℕ} (he : e ≤ p) (cap : ℕ) :
    step.island cap quiet R e = step.island cap quiet Z e := by
  ext1 r
  unfold GridStep.island
  apply congrArg
  unfold endHeat heated
  apply Finset.sum_congr rfl
  intro age _
  exact survivesH _ (fun i hi => by rw [same i hi]) he age

theorem cover (entered : ∀ w i, i ≤ p →
    old.main (b.choose w) i = filed.main (Page.opening b.after.spans w) i) :
    ∀ j : Page b.after.spans, ∀ i, i ≤ p → old.main (b.after.page j) i = filed.main j i := by
  apply Page.proves (g := fun j => ∀ i, i ≤ p → old.main (b.after.page j) i = filed.main j i)
  · exact entered
  · intro f heard i hi
    let step := S.frames (b.after.wing f)
    let quiet := T.bulk (b.after.wing f).prev
    let R := old.main (b.after.wing f).prev
    let Z := filed.main f.prev
    have vac := step.joint_vac_shape (T.cap_b B.grade _) (B.grade (b.after.wing f))
    have hR := WilsonIndependentCapturedValence.cover step quiet R vac
      (old.cap_b B.grade _) (le_max_left m n)
    have hZ := WilsonIndependentCapturedValence.cover step quiet Z vac
      (filed.cap_b (b.after.sector S B).grade _) (le_max_right m n)
    change old.main (b.after.wing f).next i = filed.main f.next i
    rw [← old.step_m (b.after.wing f),← filed.step_m f]
    change step.each m quiet R i = step.each n quiet Z i
    rw [hR,hZ]
    exact survivesP step quiet heard hi

theorem finite (entered : ∀ w i, i ≤ p →
    old.point (b.choose w) i = filed.point (Page.opening b.after.spans w) i) :
    ∀ j : Page b.after.spans, ∀ i, i ≤ p → old.point (b.after.page j) i = filed.point j i := by
  apply Page.proves (g := fun j => ∀ i, i ≤ p → old.point (b.after.page j) i = filed.point j i)
  · exact entered
  · intro f heard i hi
    let step := S.frames (b.after.wing f)
    let quiet := T.orb (b.after.wing f).prev
    let R := old.point (b.after.wing f).prev
    let Z := filed.point f.prev
    have vac := step.joint_fold_shape (T.cap_o B.grade _) (B.grade (b.after.wing f))
    have hR := WilsonIndependentCapturedValence.finite step quiet R vac
      (old.cap_o B.grade _) (le_max_left m n)
    have hZ := WilsonIndependentCapturedValence.finite step quiet Z vac
      (filed.cap_o (b.after.sector S B).grade _) (le_max_right m n)
    change old.point (b.after.wing f).next i = filed.point f.next i
    rw [← old.step_p (b.after.wing f),← filed.step_p f]
    change step.island m quiet R i = step.island n quiet Z i
    rw [hR,hZ]
    exact survivesFinite step quiet heard hi _

end YM.Integration.WilsonIndependentCapturedHistory
