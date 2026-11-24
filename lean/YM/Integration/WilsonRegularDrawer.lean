import YM.RG3.Law.Retrieve

/-! A drawer with zero forced component pays its actual regular price,
independently of the auxiliary price of the marked hard shelf in its deck. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegularDrawer
open Lattice Wilson RG Marker Overlay RG3.Forms Push.AbsoluteSums Source Function Finset MeasureTheory
open RG3.Law
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {V : Type} [DecidableEq V] {R : Census V} {G : Gauge} {n : Side} {P : Rep G n}
    {v : V} {D : Deck R P} {d : ℕ} {F : Labels.Frame G d} {H : Hol G} {C : SectionData F}

theorem price (t : Canonical v D H C) {w a c δ b u} (hb : D.Budget w a c δ b u)
    (clear : t.index.forced=0) : t.index.remBound (D.contents.origins v) P b (c/(w v)) := by
  have hr := hb.radial
  have hw := hr.pure v
  obtain ⟨f,hf,hh⟩ := hr.bulk
  have hCp := budget_nonneg (hh v)
  let z i := if t.keep i then f i else 0
  refine ⟨c/(w v),0,by positivity,le_rfl,by simp,hr.factor,
    ⟨z,?_,fun i => ?_⟩,⟨fun _=>0,?_,fun i=>⟨le_rfl,fun U=>by simp [clear]⟩⟩⟩
  · rw [div_eq_inv_mul]
    refine budget_mono (budget_scale (x:=(w v)⁻¹) (by positivity) (hh v)) (fun i => ?_) (fun i => ?_)
    · unfold z; split
      · exact (hf i).1.trans (P.p.loMass _ _ (hf i).1)
      unfold BudgetPoint.mass; simp
    unfold z Canonical.index; dsimp only; split
    next hu =>
      rw [hu.2,if_pos (show v∈ (R.fire v).val from mem_singleton_self _),Poly.solo_toll,←mul_assoc,inv_mul_cancel₀ hw.ne',one_mul]
    unfold BudgetPoint.mass; rw [mul_zero]
    exact mul_nonneg (inv_nonneg.mpr hw.le) ((hh v).1 i)
  · unfold Canonical.index z; dsimp only; split
    next hu => exact (hf i).2 v (hu.2.symm ▸ mem_singleton_self _)
    change P.p.supBounds _ _ (fun _ => (0:ℂ)) _; simpa using Push.Local.bound_const (G:=G) (B:=P.p) (X:=univ) (o:=D.contents.origins v) (0:ℂ)
  simp only [BudgetPoint.mass,mul_zero]
  exact ⟨fun _ => le_rfl, summable_zero, by simp⟩
end YM.Integration.WilsonRegularDrawer
