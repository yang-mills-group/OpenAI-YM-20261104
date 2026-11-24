import YM.OPE.Compatible.Fathom.Was
import YM.OPE.Compatible.Nock.Beachy
/-!
# Unrestricted Gaussian marginals. Positive Def matrix even empty stencil.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Jargon
open MeasureTheory Function Set Finset Filter Module
open scoped Topology BigOperators Classical ContDiff
open PertExtension Series Libra Stranded ScriptJ GaussianScore Flock Radial Silt
variable {E F X Y:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup X] [NormedSpace ℝ X]
variable {I J:Type}{i j k r:ℕ}
local notation "z" => Radial.zone (E:=E)
section
variable (P:Law E)
lemma keptZ (x:E)(h:x≠0):0<P.P x x:=by
       obtain ⟨c,hc,H⟩:=P.slope; linarith only [mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr h)), H x]
variable [FiniteDimensional ℝ E]
lemma wick_pos (p: Dual' E)(hp:p≠0):0<P.wick p p:=by
       let a:=P.inverse p; have h: a≠0:=fun h=>hp ((P.applies _).symm.trans ( (congrArg P.P h).trans (map_zero _))); change 0<p a; rw[← (show P.P a=p from P.applies _)]; exact keptZ _ _ h
lemma wickTurn (p q:Dual' E): P.wick p q=P.wick q p:=by
       let a:= P.inverse p; let b:=P.inverse q; change q a=p b; calc
            _= P.P b a:=congr_arg (fun r:Dual' E=>r a) (P.applies _|>.symm)
            _= P.P a b:=P.turns b a
            _= _:= congr_arg (fun r:Dual' E=>r b) (P.applies _)
variable (S:E→ₗ[ℝ] X)(A:Law E)
noncomputable abbrev rackL : Dual' X→ₗ[ℝ] Dual' E := S.dualMap
noncomputable abbrev towerM : Dual' X→ₗ[ℝ] X:= S ∘ₗ P.inverse ∘ₗ rackL S
lemma spinR (p q:Dual' X): P.wick (p.comp S) (q.comp S)=q (towerM P S p):=rfl
-- equality images
variable [FiniteDimensional ℝ X]
omit [FiniteDimensional ℝ X] in lemma livid (hx:Surjective S): Injective (towerM P S):= LinearMap.ker_eq_bot.mp (by
       refine le_bot_iff.mp fun i hi=>?_ ; change i=0; change towerM P S i=0 at hi; rw [← LinearMap.cancel_right hx] -- easier by contradiction
       suffices h:i.comp S=0 by simp [h]
       by_contra h; have hp:= wick_pos P (i.comp S) h; rw [spinR P S i i, hi,map_zero] at hp; exact lt_irrefl _ hp)
noncomputable abbrev frameR (hx:Surjective S): Dual' X≃ₗ[ℝ] X:= LinearEquiv.ofBijective _ ⟨livid P S hx,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [Subspace.dual_finrank_eq])).1 (livid P S hx)⟩
noncomputable def claspR (hx:Surjective S):X→ₗ[ℝ] E:= P.inverse ∘ₗ rackL S ∘ₗ (frameR P S hx).symm.toLinearMap
lemma Chwist (hx:Surjective S)(x:X)(e:E): P.P (claspR P S hx x) e=(frameR P S hx).symm x (S e):=by rw [claspR,LinearMap.comp_apply,P.applies];rfl -- composition_parens
lemma drapeB (hx:Surjective S)(x:X): S (claspR P S hx x)= x:= (frameR P S hx).apply_symm_apply _
noncomputable abbrev chiselR (hx:Surjective S):Law X:=by
      let f:=(frameR P S hx).symm; refine Libra.giraffe f.toLinearMap ?_ ?_
      · intro x y; change f x y=f y x; rw [← drapeB P S hx y] -- also rhs
        rw [← Chwist]; rw [P.turns]; rw [Chwist]; simp only[drapeB]; rfl
      intro x h; let a:=claspR P S hx x; have he : S a=x:=drapeB ..; have ha:a≠0:= fun b=> h (he.symm.trans ((congr_arg _ b).trans (map_zero S))); refine (keptZ P a ha).trans_eq ((Chwist ..).trans ?_); rw [he]; rfl
lemma chipQ (hx:Surjective S)(p:Dual' X): (chiselR P S hx).inverse p=towerM P S p :=by
      let C:=frameR P S hx; let R:=chiselR P S hx; let x:=C p; apply Eq.trans _ (R.solves x); exact congr_arg R.inverse (C.symm_apply_apply p).symm
lemma tunesB (hx:Surjective S)(p q:Dual' X): (chiselR P S hx).wick p q=P.wick (p.comp S) (q.comp S):=congr_arg q (chipQ P S hx p)
-- range for equal visions
variable (T: F→ₗ[ℝ] X) [FiniteDimensional ℝ F]
omit [FiniteDimensional ℝ X] in lemma Cher (a:Dual' X): (rackL S a)=0 ↔ towerM P S a=0:=by
       constructor; intro h; rw [towerM,LinearMap.comp_apply, LinearMap.comp_apply,h,map_zero,map_zero]
       intro h; by_contra hp; change a.comp S ≠ 0 at hp; have hh:= wick_pos P _ hp; rw[spinR,h,map_zero] at hh; exact lt_irrefl _ hh
omit [FiniteDimensional ℝ X] in
lemma Plum (A:Law F)(h:∀ p q:Dual' X,P.wick (p.comp S) (q.comp S)=A.wick (p.comp T) (q.comp T)):LinearMap.range S= LinearMap.range T:=by
       have he(p:Dual' X): towerM P S p=towerM A T p:= (SeparatingDual.eq_iff_forall_dual_eq (R:=ℝ)).2 (fun q=> h p q.toLinearMap)
       have hp:LinearMap.ker (rackL S)=LinearMap.ker (rackL T):=by ext1 p; change rackL S p=0↔ rackL T p=0; rw [Cher P S p,Cher A T p,he]
       apply Subspace.dualAnnihilator_inj.mp; rw[← LinearMap.ker_dualMap_eq_dualAnnihilator_range, ← LinearMap.ker_dualMap_eq_dualAnnihilator_range]; exact hp
end
end YM.OPE.Jargon
