import YM.QuadraticLocal.Lamps
/-! # report from arbitrary submuster/reindex

 Use only on the EXACT records. Includes superscripts order origin transactions.
 Compare doesn't substitute Spin on all frames for the output. -/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Lamps
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open Next.Foundations
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}{n:Side}{V α ι μ : Type*}[DecidableEq V] {R:Census V}{o:V→Site n}{P:BudgetPoint}
variable (L:Lamps α ι G P o R)(w: V→ℝ) {b c d:ℝ} {B:ℕ}
noncomputable def summon (f:μ→ι) : Lamps α μ G P o R where
    mode := L.mode ∘ f
    live i:= L.live (f i)
    address := L.address ∘ f
    roots i:= L.roots (f i)
    nominal t:= L.nominal t ∘ f
    legal t i:= L.legal t (f i)
    clear := L.clear ∘ f
    pure t i:= L.pure t (f i)
lemma summonPaid (f:μ→ι)(hf:Injective f)(h:L.Paid w B b c): (L.summon f).Paid w B b c:=by
    obtain ⟨F,hF,hH,hK⟩:=h.budget; exact ⟨F ∘ f,(fun i=>hF (f i)),(fun i t=> hH (f i) t),fun i=>budget_pull f hf (hK i)⟩
lemma summonLight (f:μ→ι)(t:α)(i:μ)(v:Config G n): (L.summon f).light t i v=L.light t (f i) v:= by unfold Lamps.light; dsimp only [summon,ground,Function.comp_apply]; congr
lemma summonFrame (f:μ→ι)(t:α)(i:μ)(v:Config G n): (L.summon f).frame i t v=L.frame (f i) t v:= by unfold Lamps.frame; rw [summonLight]; rfl
lemma summonLog (f: μ→ι)(hf:Injective f)(t:α)(v:Config G n)(hp:Function.support (fun i=> L.frame i t v)⊆ Set.range f): (L.summon f).log t v=L.log t v:=by unfold Lamps.log; simp_rw [summonFrame]; exact Function.Injective.tsum_eq hf hp
variable {X:Lamps α ι G P o R}{Y:Lamps α μ G P o R}
lemma pureJoin (t:α)(v:Config G n)(i:ι): (X.join Y).frame (.inl i) t v=X.frame i t v:=by unfold Lamps.frame Lamps.light; dsimp only [join,Sum.elim_inl,Lamps.ground]; congr
lemma pureJoin' (t:α)(v:Config G n)(i:μ): (X.join Y).frame (.inr i) t v=Y.frame i t v:=by unfold Lamps.frame Lamps.light; dsimp only [join,Sum.elim_inr,Lamps.ground]; congr
end YM.QuadraticLocal.Lamps
