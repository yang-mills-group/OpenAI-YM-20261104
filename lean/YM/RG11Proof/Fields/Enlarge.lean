import YM.RG11Proof.Fields.Elevate

/-! The homogeneous physical basis need not be selected anew at each horizon.
Expose injections and compatibility with `Position.Buffer` constraints, so that
finite `Mesh` gluing applies on exactly these spaces (including d1 if desired,
though actual coupling diagnostic starts with larger cap). -/
set_option autoImplicit false
set_option maxHeartbeats 650000
noncomputable section
namespace YM.RG11.Fields
open PowerSeries YM.RG11.Jets Function Set Labels Maxwell YM.Pert.Position Extra.FD MvPolynomial YM.Pert.RawLabels
open scoped Classical BigOperators ContDiff
variable {G : Gauge} {F : Frames G} {d e n:ℕ}

namespace Adapted

def Gives (B:Adapted F e)(M:Adapted F d) (h:e≤d) (f:B.toBasis.J↪ M.toBasis.J) :=
   ∀ i, M.b (f i)=up F h (B.b i)

-- Algebraic extension preserving real bigraded basis and marked unit.
private def qualified (F:Frames G)(d:ℕ) := {v:E F d| ∃ w:ℕ×ℕ,w.1≤d ∧ w.2≤d ∧
    (writes F d v).IsWeightedHomogeneous compileW w ∧ Basis.overReals v}

private lemma belongs (B:Adapted F d) (i:B.toBasis.J):B.b i∈qualified F d:=⟨_,B.heights i,B.lengths i,B.alive i,B.pinned i⟩

theorem after (B : Adapted F e)(h:e ≤ d):∃ (M:Adapted F d) (f:B.toBasis.J↪M.toBasis.J), B.Gives M h f:= by
  classical
  let g(i:B.toBasis.J):=up F h (B.b i)
  let Q:=qualified F d
  have hu : Set.range g ⊆ Q := by
    rintro v ⟨i,rfl⟩
    unfold g
    refine ⟨B.w i,(B.heights i).trans h,(B.lengths i).trans h,?_⟩
    rw [up_write]
    refine ⟨B.alive i,?_⟩
    unfold Basis.overReals
    apply writes_inj F d
    rw [writes_bar,up_write, ←writes_bar F (table_spin F),B.pinned]
  have he : LinearIndependent ℂ g:=B.b.linearIndependent.map' (up F h) (LinearMap.ker_eq_bot.mpr (up_inject F h))
  obtain ⟨S,h₁,h₂,h₃,h₄⟩ := exists_linearIndepOn_id_extension (he.linearIndepOn_id) hu
  have ht : Submodule.span ℂ (Set.range (⇑(eachBasis F d).b)) ≤ Submodule.span ℂ S:= by
    refine Submodule.span_le.mpr (fun v hv=>?_)
    obtain ⟨i,rfl⟩:=hv; exact h₃ (belongs ..)
  have hB: ⊤≤ Submodule.span ℂ (Set.range (Subtype.val:S→E F d)) := by
    rw [Subtype.range_coe]; rw [Module.Basis.span_eq] at ht; exact ht
  let p:Module.Basis S ℂ (E F d):=Module.Basis.mk (show LinearIndependent ℂ (Subtype.val:S→_) from h₄.linearIndependent_restrict) hB
  let t(i:B.toBasis.J):S := ⟨g i,h₂ (Set.mem_range_self _)⟩
  have hr(x:S): p x=x.val:=by simp [p]
  choose w hw hs hb hj using fun i:S=> h₁ i.property
  letI := Module.Finite.finite_basis p
  letI := Fintype.ofFinite S
  haveI : Nonempty S:= ⟨t B.unitIndex⟩
  let m:=Fintype.card S-1
  let c:= (Fintype.equivFin S).trans (finCongr (show Fintype.card S=m+1 by have he:=Fintype.card_pos (α:=S); dsimp [m]; omega))
  let ε:B.toBasis.J↪Fin (m+1):= ⟨fun i=>c (t i),fun i j h=> he.injective (congrArg (fun v:S=>v.val) (c.injective h))⟩
  let P := p.reindex c
  have hP (i):P (c i)=i.val:=by simp [P,hr i]
  let u:=ε B.unitIndex
  let D:Basis F d:={
    m:=m
    b:=P
    unitIndex:=u
    unitAt:= (hP _).trans (show up F h (B.b B.unitIndex)= (freeTable F).unit d by rw [B.unitAt]; apply writes_inj F d; rw [up_write,writes_unit,writes_unit])
    pinned i:= by obtain ⟨b,rfl⟩:=c.surjective i; rw [hP]; exact hj b }
  let M:Adapted F d:= {
    toBasis:=D
    w:=fun i=>w (c.symm i)
    alive i:= by obtain ⟨b,rfl⟩:=c.surjective i; rw [show D.b=P from rfl,hP,c.symm_apply_apply]; exact hb b
    heights i:=hw _
    lengths i:=hs _ }
  exact ⟨M,ε,fun i=> hP (t i)⟩

variable {B:Adapted F e} {M:Adapted F d} {h:e≤d} {f:B.toBasis.J↪ M.toBasis.J}

theorem Gives.weights (H : Gives B M h f) i : M.w (f i)= B.w i := by
  have ht:= M.alive (f i); rw [H,up_write] at ht
  exact IsWeightedHomogeneous.inj_right (fun hy=>B.b.ne_zero i ((writes_inj F _) (hy.trans (map_zero _).symm))) ht (B.alive i)

theorem Gives.paths {W:Adapted F n} {hi:d≤n} {g:M.toBasis.J↪W.toBasis.J} (hf:Gives B M h f) (hg:Gives M W hi g):
    Gives B W (le_trans h hi) (f.trans g):=by
  intro i; rw [Function.Embedding.trans_apply,hg,hf,up_up]

-- Any output of low grade in the new basis is in the OLD subsystem.
theorem Gives.retain (H : Gives B M h f) (j:M.toBasis.J) (hj:(M.w j).1 ≤ e): j∈Set.range f := by
   by_contra! he
   have hw:=stairs M j hj; rw [← staircase F h] at hw; obtain ⟨x,hx⟩:=hw
   have hp := congrArg (fun v=> M.b.equivFun v j) hx
   rw [←B.b.sum_equivFun x,_root_.map_sum,_root_.map_sum, Finset.sum_apply] at hp
   simp_rw [_root_.map_smul, ← (show ∀ i, _=up F h (B.b i) from H),Pi.smul_apply,Module.Basis.equivFun_self] at hp
   have hh (i): f i ≠ j:= fun hy=> he ⟨i,hy⟩
   simp_all
end Adapted
end YM.RG11.Fields
