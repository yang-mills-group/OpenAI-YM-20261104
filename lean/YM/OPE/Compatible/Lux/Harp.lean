import YM.OPE.Compatible.Atlas.Commission
/-!
# Eventual polymer score through true detector integrals
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Function Set Filter Table MeasureTheory
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {X Y Z L:Type}{φ:Filter L}{T:L→ℝ}
lemma Score.goes [SeminormedAddCommGroup X] {f g :L→ X} (hf:Score φ T f)(hg:Score φ T g)(ht:Tendsto T φ atTop):Score φ T (fun i=>f i-g i):=by
   obtain ⟨a,ha⟩:=hf; obtain ⟨c,hc⟩:=hg; -- rate both mono
   exact ⟨max a c,RateLE.sub (ha.mono (le_max_left ..)) (hc.mono (le_max_right ..)) (Real.tendsto_log_atTop.comp ht)⟩ -- indentation
lemma Score.utility [NormedAddCommGroup X][NormedAddCommGroup Y][NormedAddCommGroup Z] {f:L→X}{g:L→ Y} (hf:Score φ T f)(hg:Score φ T g){w:L→ Z}(h:∀ᶠ i in φ, ‖w i‖ ≤ ‖f i‖ * ‖g i‖) : Score φ T w:=by obtain ⟨a,ha⟩:=hf; obtain ⟨c,hc⟩:=hg; exact ⟨_, ha.bil hc h⟩
variable [Norm X]
lemma Score.allPi [Fintype Y] {w:L→ Y→ℂ} (ht:Tendsto T φ atTop)(h:∀ y, Score φ T (fun i=> w i y)): Score φ T w:=by
    choose K hK using h; by_cases he:Nonempty Y
    · let A:=Finset.univ.sup' Finset.univ_nonempty K; refine ⟨A,?_⟩; intro b hb; filter_upwards [eventually_all.mpr fun i=> hK i b (lt_of_le_of_lt (Finset.le_sup' K (Finset.mem_univ _)) hb)] with i hi; exact (pi_norm_le_iff_of_nonneg (Real.exp_nonneg _)).mpr hi
    have hz:IsEmpty Y:= not_nonempty_iff.mp he; exact (Score.steady (0:Y→ℂ) ht).congr (Eventually.of_forall fun _=> Subsingleton.elim ..)
variable {l:Type} {ψ: Filter l}{u:l→ℝ}
lemma Score.lift_l [NormedAddCommGroup Y][NormedSpace ℝ Y][NormedAddCommGroup Z][NormedSpace ℝ Z] {g:l→Y}(hp:Tendsto u ψ atTop) (h:Score ψ u g)(G:Y→L[ℝ] Z): Score ψ u (fun i=> G (g i)):= by obtain ⟨a,ha⟩:=h; exact ⟨_, ha.linear (Real.tendsto_log_atTop.comp hp) G⟩
open Cov
lemma Score.grasp [NormedAddCommGroup Y][NormedSpace ℝ Y](_ht:Tendsto u ψ atTop)(P : l→ Ortho→Y)(h:∀ i:l→Ortho, Score ψ u (fun j=> P j (i j)))(hP:∀ᶠ i in ψ, Continuous (P i)): Score ψ u (fun j=>∫ g,P j g ∂angles):=by
   have hx(i:l)(h:Continuous (P i)): ∃ g,∀ g', ‖P i g'‖ ≤ ‖P i g‖:=by
       obtain ⟨g,-,hg⟩:= isCompact_univ.exists_isMaxOn univ_nonempty (Continuous.continuousOn (continuous_norm.comp h))
       exact ⟨g, fun _=> hg (mem_univ _)⟩
   choose! g hg using hx -- chooses independent h
   refine (h g).liftp ?_; filter_upwards [hP] with i hi; exact (norm_integral_le_of_norm_le (integrable_const ‖P i (g i)‖) (ae_of_all _ (hg i hi))).trans (by simp)
end YM.OPE
