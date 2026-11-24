import YM.Push.LOCAL_SPLITTING.Transport
import YM.Extra.MULTISOURCE_BOUNDS.Columns

/-! Moving one insertion by a lattice translation preserves its whole
marked budget, including the old forced slots in their actual permutation. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonTranslatedSourceBudget
open Function Lattice RG Wilson Source Push.Local Extra.Multi
open scoped BigOperators Classical
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}

private lemma sites (y : Site n) : ⇑(turnSites (1 : Signed) y) = (· + y) := by
  funext z; change (1 : Signed).act z + y = z + y; rw [Signed.act_one]

theorem covering (y : Site n) (X : Support n) (B : ℕ) :
    coverNumber B (Relocate.shift y X) = coverNumber B X := by
  refine le_antisymm (Relocate.cover_shift ..) ?_
  have h := Relocate.cover_shift (-y) (Relocate.shift y X) B
  have e : Relocate.shift (-y) (Relocate.shift y X) = X := by
    unfold Relocate.shift; rw [Finset.image_image]
    rw [show ((fun x : Site n => x + -y) ∘ (fun x => x+y)) = id by
      funext x; exact add_neg_cancel_right x y,Finset.image_id]
  rwa [e] at h

theorem mass (p : BudgetPoint) (y : Site n) (X : Support n) (c : ℝ) :
    p.mass (X.image (turnSites (1 : Signed) y)) c = p.mass X c := by
  rw [sites]; change p.mass (Relocate.shift y X) c = _
  simp only [BudgetPoint.mass,covering]

variable {R : Rep G n} {o : Site n} {P : Coefficient F n} {k t : ℝ}
theorem translated (y : Site n) (m : R.activities.Moves 1 y)
    (h : P.remBound o R k t) :
    (reorient m P).remBound (o+y) R k t := by
  obtain ⟨a,b,ha,hb,hs,hk,⟨e,he,hr⟩,⟨f,hf,hd⟩⟩ := h
  refine ⟨a,b,ha,hb,hs,hk,⟨e,?_,?_⟩,⟨fun i => f (m.kp.symm i),?_,?_⟩⟩
  · simpa only [reorient,mass] using he
  · intro i; have hfun : (pull (1 : Signed) y : Config G n → Config G n) = translate y := funext (pull_one y)
    simpa only [reorient,sites,Relocate.shift,hfun] using
      (Relocate.sup_translate (y:=y) (hr i))
  · have eq (i : ℕ) : R.p.mass (R.activities.forced i).support (f (m.kp.symm i)) =
        R.p.mass (R.activities.forced (m.kp.symm i)).support (f (m.kp.symm i)) := by
      obtain ⟨j,rfl⟩ := m.kp.surjective i
      rw [m.kp.symm_apply_apply,m.forced_support]; exact mass ..
    simp_rw [eq]
    refine ⟨fun i => hf.1 _,m.kp.symm.summable_iff.mpr hf.2.1,?_⟩
    exact (m.kp.symm.tsum_eq (fun i => R.p.mass (R.activities.forced i).support (f i))).le.trans hf.2.2
  · intro i; obtain ⟨j,rfl⟩ := m.kp.surjective i
    simp only [m.kp.symm_apply_apply,forced_reorient]
    exact ⟨(hd j).1,fun U => (hd j).2 (pull 1 y U)⟩

end YM.Integration.WilsonTranslatedSourceBudget
