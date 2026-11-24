import YM.OPE.Compatible.Lines.Azure
/-!
# analytic one direction. cost explicit height; uniform over attachments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FrameRead
open Function Set Filter Analysis Table Lattice MeasureTheory Complex Boundary EveryPhase Spec OPE
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}{U:Final C F S}(L : Almanac U) {n:ℕ} {R:ℝ}
-- Fin names reindex. e permutation gives ALL real parameter points sorted.
include L
lemma shining_path (p:Fin n→ C.book.Token)(a:ℕ)(e:Equiv.Perm (Fin n)) : ∃ m:ℕ,∃ c:ℝ,0≤c∧∀ i:Viewers U,∀ x: ℝ→Fin n→ E4,∀ (b:Fin n→ℝ), (∀ t j,x t j=x 0 j+(t*b j) • trail a)→ ∀ k R:ℝ,k∈Ioc 0 1 → (∀ t:ℝ,|t| ≤ R→ broad (shade a ∘ x t ∘ e) k)→ Shines R (c*k⁻¹^m) (fun t=>observe (spectator U i) (x t) p):=by
    let f:=polar a; let r:= (Ward.expose (S:=S)) ∘ U.sector.turns.label f ∘ S.classTokens ∘ p; let q:= r∘e
    let z(j:Fin n):S.Union:= S.pin _ (S.project _ ((q j).2)); obtain ⟨m,c,hc,hM⟩:= ocean L z; refine ⟨m,c,hc,fun i x b hx k R hk hw=>?_⟩
    let Y(t:ℝ):= points (Ortho.move f ∘ x t ∘ e); let Z(i:ℂ)(j:Fin n):ℂ:=(↑(shade a (x 0 (e j))) + i*(↑(b (e j)))* ↑‖trail a‖)*Complex.I
    let H:= orb L i; let X:= trace (Y 0); let W(t:ℂ):=H.F _ (Z t) X z
    have hY(s j): Y s j=Y 0 j+(s*b (e j)*‖trail a‖) • (YM.basis timeAxis):=by
       change Ortho.motion f (x s (e j))=Ortho.motion f (x 0 (e j))+ _; rw [hx s (e j),map_add,map_smul,mul_smul]; rw [show (Ortho.motion f) _=_ from north a]; module -- associativity
    have hp(t:ℂ) : (fun j=> (Z t j).im)=shade a ∘ x t.re ∘ e:=by
       ext1 j; change _= time (Y _ j); rw [hY t.re j]; simp [Z]; rfl
    refine ⟨W,?_,?_,?_⟩
    · refine ((region_for L i).hol n z X).comp (f:=Z) (by unfold Z; fun_prop) (fun t ht=>?_)
      have hv:= hw _ (t.abs_re_le_norm.trans (by simpa using Metric.mem_closedBall.mp ht)); rw [← hp] at hv; exact fun u v hl=> sub_pos.mp (hk.1.trans_le (hv _ _ hl))
    · intro t ht; let S':= spectator U i; have ho : StrictMono (fun j=> time (Y t j)):=fun _ _ h=>sub_pos.mp (hk.1.trans_le ((hw t ht) _ _ h))
      have hc:Y t∈ conf n:= fun i j hi=> ho.injective (congr_arg time hi); have hs : Injective (x t):=by
          intro i j hi; obtain ⟨i,rfl⟩:=e.surjective i; obtain ⟨j,rfl⟩:=e.surjective j; exact congr_arg e ((show Injective (Y t).ofLp from hc) (congr_arg (Ortho.move f) hi))
      have he :U.sector.turns.Oriented S':=by cases i; exact U.phase.transport.motion; exact U.phase.phase.sym _
      have hT: trace (Y t)=X:= by funext j; change spatial (Y t j)= spatial (Y 0 j); rw [hY]; simp
      have hh: Z (↑t:ℂ)=fun j=>↑(time (Y t j))*Complex.I:=by funext j; rw [hY]; simp [Z]; rfl
      change H.F _ _ _ _=_; rw [hh,← hT]
      have hz:=spectate U i
      calc
         _ = S'.read (Y t) q := H.root_raw hz.laws.toSymmetric (spectate_respects U i) (region_for L i) q (Y t) ho
         _ = observe S' (Y t).ofLp q := (named_fin _ hz.laws.toSymmetric _ hc).symm
         _ = observe S' (Ortho.move f ∘ x t) r := perm_observe S' hz.laws.toSymmetric e r ((Ortho.motion f).injective.comp hs)
         _ = observe S' (x t) p := by
             rw [← Cov.kernel_observe hz.laws.toSymmetric (spectate_respects U i) hs p, ← Cov.kernel_move he _ hs f, Cov.kernel_expose]
    intro t ht; apply hM _ _ _ hk; have hv:= hw t.re (t.abs_re_le_norm.trans_eq ht); rwa [hp]
end YM.FrameRead
