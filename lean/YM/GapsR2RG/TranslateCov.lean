import YM.GapsR2RG.FiberDoor
/-!
# Translating full tangent-column budgets without paying a derivative-turn penalty.

Signed rotations can eat a power-dependent derivative constant at each step.
Pure fine translations preserve all radii and complete flags termwise. Keep the
supplied actual `Moves`, do not pick new masks.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option quotPrecheck false
noncomputable section
namespace YM.GapsR2RG
open Lattice Wilson RG Source Labels Function Filter Set MeasureTheory Finset Push.Local Extra.Histories
open Planned.GuardedAtom
open scoped Classical Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G:Gauge}{n:Side}
namespace Anchor
variable (b: Site n)
private def shiftD (A:Directions G n): Directions G n := fun e=>A (e.1+b,e.2)
private lemma translate_inc (U:Config G n)(A:Directions G n)(t:ℝ):
     translate b (increment U (t • A)) = increment (translate b U) (t • shiftD b A) :=rfl -- perhaps definitional
private lemma slide_jets {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X] (q:List (Directions G n))(f:Config G n→X)(V:Config G n) : leftDerivs (f ∘ translate b) q V = leftDerivs f (q.map (shiftD b)) (translate b V) :=by
    induction q generalizing V with
    | nil=> rfl
    | cons A l ih=> simp only [List.map_cons,leftDerivs,ih,translate_inc]
lemma slide_bound {X:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][MeasurableSpace X] {o:Site n}{S:Support n} {f:Config G n→X}{P:BudgetPoint}{a:ℝ}(hc:P.supBounds o S f a):
    P.supBounds (affine 1 b o) (S.image (affine 1 b)) (f ∘ pull 1 b) a :=by
   rw [funext (pull_one (K:=G.El) b)];
   have he x : affine 1 b x=x+b:=by simp [affine]
   refine ⟨hc.1,fun U hu l hl ht=> ?_⟩
   rw [slide_jets]
   refine hc.2 (translate b U) (by rw [← pull_one]; exact (healthy_pull ..).1 hu) _ ((List.length_map _).le.trans hl) ?_
   intro A hA; rw [List.mem_map] at hA; obtain ⟨B,hB,rfl⟩:=hA
   intro e
   simpa only [shiftD,he,separation_translate] using ht B hB (e.1+b,e.2)
variable {o:Site n}{R:Rep G n}{d:ℕ}{F:Labels.Frame G d}{P:Coefficient F n}{a κ k:ℝ}{b}
lemma Tab_slide (S:R.activities.Moves 1 b)(h:Tab P o R κ a k): Tab (reorient S P) (affine 1 b o) R κ a k:=by
  let r := turnSites (1:Signed) b
  have hm (Z : Support n) (v : ℝ) : R.p.mass (Z.image r) v = R.p.mass Z v := by unfold BudgetPoint.mass; rw [cover_map r (turn_sep (1:Signed) b)]
  obtain ⟨v,hx,hy⟩ := h.regular
  obtain ⟨w,hz,hw⟩ := h.forced
  refine ⟨h.divisor,h.first,h.second,⟨v,?_,fun i => slide_bound b (hy i)⟩,
    ⟨fun i => w (S.kp.symm i),sumBudget_pass S.kp.toEmbedding _ ?_ (fun i hi => absurd (S.kp.surjective i) hi),
      fun i => ⟨(hw _).1, fun U => (hw _).2 _⟩⟩⟩
  · change SumBudget (fun i => R.p.mass ((P.support i).image r) _) _
    simp_rw [hm]; exact hx
  simpa only [patch,Equiv.coe_toEmbedding,S.forced_support,S.kp.symm_apply_apply,show affine 1 b=⇑r from rfl,hm] using! hz
lemma cost_slide (S:R.activities.Moves 1 b)(h:P.remBound o R κ k): (reorient S P).remBound (o+b) R κ k:=by
    obtain ⟨q,w,hq,hw⟩:= rem_tabs.mp h; simpa [affine] using (rem_tabs.mpr ⟨q,w,Tab_slide S hq,hw⟩)
lemma rule_slide {H:Hol G} (S:R.activities.Moves 1 b)(h:P.Format o H R)(hn:2≤n.val): (reorient S P).Format (o+b) H R:=by simpa [affine] using format_reorient S h hn
lemma convey_slide {H:Hol G} {T:SectionData F}(S:R.activities.Moves 1 b)(h:T.Sound H): (reorient S P).density (o+b) T R = P.density o T R ∘ translate b:=by
   have he:= density_reorient (o:=o) S h P
   rw [funext (pull_one (K:=G.El) b),affine,Signed.act_one] at he
   exact he
end Anchor
end YM.GapsR2RG
