import YM.OPE.Sparse.Circuit

/-! Costs transfer from a genuine unary tree reading only where all erased
slots are literal units. Keep both kinds of aperture from true tree in use.
(copies of the elementary sum uniqueness argument in Measuring/Charts)
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Sparse
open Orbits Orbits.Reader Nesting Nesting.Tree Function Filter Set Table Composite Tracing Nesting.Motion
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
local notation "Q"=>U.sector.derivatives
namespace Evaluation
open Circuit
variable {n:ℕ}{f:Fin n→Nesting.Tree}
local notation "nodes"=> Nesting.Tree.fork n f
variable (w:(Nesting.Tree.fork n f).Leaf→S.Tag) {m:ℕ} {z:(fork n f).Plot}{D:(fork n f).Inner→ℕ}
   (hc:z∈Kernel.aperture U R (Nesting.Tree.fork n f) m D)
private lemma sum_unique {a b:R.channels m→ℂ}(h:(∑ i:R.channels m,a i • R.actor m i) = ∑ i,b i • R.actor m i):a=b:=by
    have h': (∑ i,a i • R.basis m i) = ∑ i,b i • R.basis m i:=Subtype.ext (by change (R.stratum m).subtype _ = (R.stratum m).subtype _; simp only [map_sum,map_smul]; exact h)
    exact Eq.trans ((R.basis m).repr_sum_self a).symm ((congr_arg (fun v:R.stratum m=>(fun i=>(R.basis m).repr v i)) h').trans ((R.basis m).repr_sum_self b))
variable (p:(fork n f).Leaf)(h:Sparse w p)
local notation "trail"=> pathTree nodes p

include hc
include h in
lemma stacking(i:R.channels m) :Kernel.chord U R z w i D=Kernel.chord U R (f:=fun (_:Fin 1)=>pathTree (f p.1) p.2) (z ∘ layout nodes p) (fun _=>w p) i (D ∘ inlet nodes p):=by
    apply congr_fun (_: (fun i:R.channels m=>Kernel.chord U R z w i D) = _ ) i
    refine sum_unique U R ((Motion.chord_vector U R z (voices w) D m).trans ((Circuit.Children.step_selected U R (w:=w) (hc.1 (Fin.last _)) _ ?_ ?_).trans ((Motion.chord_vector U R (f:=fun (_:Fin 1)=>pathTree (f p.1) p.2) (z ∘ layout nodes p) (voices (fun _=>w p)) (D ∘ inlet nodes p) m).symm)))
    · intro j hj; exact Children.perfect U R _ _ _ (hc.2 j) (fun k=>h ⟨j,k⟩ (fun he=>hj (Sigma.ext_iff.mp he).1))
    exact Children.interpret U R (f p.fst) p.snd (childPlace p.1 z) (childWages p.1 w) (childAge p.1 D) (fun b hb=> h ⟨p.fst,b⟩ (fun he=> hb (eq_of_heq ((by cases p; exact (Sigma.mk.inj he).2))))) (hc.2 p.fst)
lemma full_unit (h:∀ j,literal (w j))(hg:orbitMargin R.port m (Tree.profile z) (anchor z))(i:R.channels m): Kernel.chord U R z w i D=Kernel.output U R z w i:=by
   refine congr_fun (sum_unique U R (b:= Kernel.output U R z w) ((Motion.chord_vector U R z (voices w) D m).trans (Eq.trans ?_ (Eq.trans (fill U R h hg).symm (R.assemble .. |>.symm))))) i
   exact fill U R (w:=Children.each U R z w D) (fun j=>Children.perfect U R _ _ _ (hc.2 j) (fun k=>h ⟨j,k⟩)) (hc.1 (Fin.last _))
omit hc

include h in
lemma leading (hz:orbitMargin R.port m (Tree.profile z) (anchor z))(i:R.channels m): Kernel.output U R z w i = Kernel.output U R (t:=trail) (z ∘ layout nodes p) (fun _=>w p) i:=congr_arg ((R.basis m).repr · i) (Subtype.ext (Circuit.line U R p z h hz))

lemma killed (h:∀ j,literal (w j))(hg:orbitMargin R.port m (Tree.profile z) (anchor z))(hm:0 < m)(i:R.channels m): Kernel.output U R z w i=0:=by
    have hf := (fill U R h hg).trans (R.kills_lower m 0 hm (S.unit 0))
    exact (congr_arg ((R.basis m).repr · i) (Subtype.ext (a2:=(0:R.stratum m)) (hf: R.fresh m _ _ _ = ((0:R.stratum m).val:S.Field m)))).trans (by rw [map_zero]; rfl)

lemma constant_unit (h:∀ j,literal (w j))(hg:orbitMargin R.port m (Tree.profile z) (anchor z))(i:R.channels m):Kernel.output U R z w i = R.coef m i (sole 0) (sole (S.unit 0):Labels S fun _:Unit=>0) 0 := by
    have hf:= (fill U R h hg).trans (Orbits.Reader.single R _ _ _).symm
    exact congr_arg ((R.basis m).repr · i) (Subtype.ext hf)

section Test
variable {J:Type}[Fintype J](v:J→S.Tag)(q:Viewers U){y:J→ E4}
lemma source (t:Tree)(z:t.Plot)(w:t.Leaf→S.Tag)(hz:Injective (beside (Tree.profile z) y))(p:t.Leaf)(h:Sparse w p):
 whole (spectator U q) (Tree.profile z) (voices w) y (voices v)=whole (spectator U q) (Tree.profile (z ∘ layout t p)) (voices (fun _:(pathTree t p).Leaf=>w p)) y (voices v) :=by
    let e: (pathTree t p).Leaf → t.Leaf:=fun _=>p; let a: (pathTree t p).Leaf⊕J → t.Leaf⊕J:= Sum.map e id
    have hP := name_unique t p
    let x:=beside (Tree.profile z) y
    let d:= Orbits.tags (stages (voices w) (voices v))
    have he:=Undo.restrict (momentIdentity (S:=S) (spectator U q) (spectate U q) (spectate_respects U q)) x hz a (Sum.map_injective.mpr ⟨fun p q hah=>hP.2.allEq p q,injective_id⟩) d ?_ -- only implication
    swap
    · intro i hi; rcases i with j|j; · exact h j (hi (.inl (Nonempty.some hP.1)) <| congr_arg Sum.inl ·.symm)
      exact (hi (.inr j) (by rfl)).elim
    rw [Tracing.points]
    apply he.trans; change Undo.apply (fun I _ (x:I→E4) v=>moment (spectator U q) x (voices v)) (x ∘ a) (d ∘ a) = Undo.apply (fun I _ (x:I→E4) v=>moment (spectator U q) x (voices v)) (beside (z ∘ _) y) (Orbits.tags (stages _ (voices v)))
    congr 1
    all_goals funext u; cases u with | _ _=> rfl

include h
variable {D':ℕ}
lemma stream (hz: Injective (beside (Tree.profile z) y))(hc:∀ m ≤ D',orbitMargin R.port m (Tree.profile z) (anchor z)):Kernel.pipe U R z w q D' y v= Kernel.pipe U R (t:=trail) (z ∘ layout nodes p) (fun _=>w p) q D' y v:=by
   unfold Kernel.pipe formula Orbits.trunc; rw [Tracing.root]
   apply congr_arg₂ Sub.sub (source U v q _ z w hz p h) (Finset.sum_congr rfl fun m hm=>Finset.sum_congr rfl fun i hi=>congr_arg (· * _) ?_)
   exact leading U R w p h (hc m (Nat.le_of_lt_succ m.isLt)) i
end Test
end Evaluation
end YM.OPE.Sparse
