import YM.OPE.Short.Leading
/-!
# Contracted scalar transfer through low intermediate horizons

Values only at an internal horizon≤3. We substitute the physically summed
children in the exact same vector circuit. At those intermediate projections
one may carry normalized vacant branches while retaining all active bud slots
in a common rotated and translated word. `flow` records the actual amplitudes
of these circuits when the intermediate spectrum is trivial. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Short
open Orbits Orbits.Reader Nesting Nesting.Tree Function Filter Set Table Composite Sparse.Tracing Nesting.Motion Extraction Pert
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(X:Climb.Scaling S) (hG:G.Simple) (H:Pert.FirstExtension U X)
local notation "Q"=>U.sector.derivatives

namespace Currency
open Sparse.Circuit.Children
abbrev pulses (t:Tree)(z:t.Plot)(w:t.Leaf→S.Tag)(D:t.Inner→ℕ) := Vector.pulse U R z (voices w) D
def flow : (t:Tree)→t.Plot→(t.Leaf→S.Tag)→(t.Inner→ℕ)→ℂ
 | .bud,_,_,_=>1
 | .fork n f,z,w,D=> scalar U R (skyline z) (each U R z w D) (anchor z)
def fledged(t:Tree)(D:t.Inner→ℕ) := ∀i,D i≤3
variable {t:Tree}(z:t.Plot)(w:t.Leaf→S.Tag)(D:t.Inner→ℕ)
include hG X
section
lemma issued (ht:t≠bud)(hd:fledged t D): (issue U R z w D).snd = flow U R t z w D • S.unit _:=by cases t with
  | bud=>exact (ht rfl).elim
  | fork n f=>
     let m:=boundNow (fork n f) D
     let g (j:Fin (m+1)):=U.sector.derivatives.rise (d:=j.val) (e:=m) (Nat.le_of_lt_succ j.isLt) (R.fresh j.val (Tree.skyline z) (anchor z) (voices (each U R z w D)))
     change (Vector.pulse U R z (voices w) D) = _
     rw [pulse_pack]
     change ∑ j:Fin (m+1),g j = _
     let j:Fin (m+1):=⟨0,Nat.succ_pos m⟩
     refine (Finset.sum_eq_single j ?_ (by simp)).trans ?_
     · intro k hk he; unfold g
       change ∀i,D i≤3 at hd
       have hm:m≤3:=hd (.inl ())
       have h' : R.fresh k.val (Tree.skyline z) (anchor z) (voices (each U R z w D)) = 0 := low_annihilator U R X hG (Nat.pos_of_ne_zero (fun (hx:k.val=0)=>he (Fin.ext hx))) (lt_of_lt_of_le k.isLt (Nat.add_le_add_right hm 1)) _ (R.fresh_mem _ _ _ _)
       exact (congr_arg ((Q).rise (d:=k.val) (e:=m) _) h').trans (map_zero _)
     unfold g flow
     erw [←(scalarizes U R X hG (skyline z) (each U R z w D) (anchor z)), map_smul, U.sector.derivatives.fixs R.lifts R.continuum.laws]
end

omit X hG
abbrev levy (t:Tree) : ℕ:= exponent t.Leaf
 variable {n:ℕ}{f:Fin n→Nesting.Tree}
local notation "nodes"=> Nesting.Tree.fork n f
abbrev Bare (f:Fin n→Nesting.Tree):= {i:Fin n//f i=bud}
def entry (t:Tree)(he:t=bud):t.Leaf:=cast (congr_arg Nesting.Tree.Leaf he.symm) (show bud.Leaf from ())
def displaying(ab:Picture (Leaf nodes))(i:Bare f) : Axis×Axis:=ab ⟨i,entry _ i.property⟩
def fee (i: Fin n) : ℕ :=if f i=bud then 0 else exponent (f i).Leaf
-- beware captured `f`; definitions require auto params. Use `fee (f:=f)`
omit w D
namespace Entries
variable (ab:Picture (Nesting.Tree.Leaf (Nesting.Tree.fork n f)))(z:(fork n f).Plot)(D:(fork n f).Inner→ℕ)
private abbrev slots(p:(fork n f).Leaf):S.Tag:=stressTag U ab p
private def age (i : Fin n) : ℕ := (each U R z (slots U ab) D i).fst
private def post (i : Fin n) : ℂ := flow U R (f i) (childPlace i z) (childWages i (slots U ab)) (childAge i D)
private def token (i : Fin n) : S.Field (age U R ab z D i) :=
   if f i=bud then (each U R z (slots U ab) D i).snd else S.unit _
private abbrev borders := skyline z ∘ ((↑) : Bare f→Fin n)
-- literal payment inside child. Revealed by substituting its whole truncated field.
include X hG
private lemma unit_token (hd:fledged nodes D)(i:Fin n): (post U R ab z D i) • (token U R ab z D i)= (each U R z (slots U ab) D i).snd :=by
    by_cases hi:f i=bud
    · rw [show post U R ab z D i=1 from bud_flow U R (f i) (childPlace i z) _ _ hi]
      rw [one_smul,token,if_pos hi] -- if not dif
    unfold token; rw [if_neg hi]; exact (issued U R X hG _ _ _ hi fun p=>hd (.inr ⟨i,p⟩)).symm
where bud_flow(U:Spec.Final C F S)(R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(t:Tree) (z:t.Plot)(w:t.Leaf→S.Tag)(D:t.Inner→ℕ)(h:t=bud):flow U R t z w D=1:=by cases h; rfl
omit X hG in
private lemma unpaid(i:Bare f) : Orbits.tags (d:=age U R ab z D) (token U R ab z D) i = stressTag U (displaying ab) i:=by
    -- if then (`f i=bud`)
    unfold Orbits.tags; change (let x:=(each U R z (slots U ab) D (i:Fin n)); (⟨x.fst,if f i=bud then x.snd else S.unit x.fst⟩:S.Tag))= _
    dsimp only; rw [if_pos i.property]
    exact bud_eq (t:=f i) (i.property) (entry _ i.property) _ _ _
where bud_eq {t:Nesting.Tree} (ht:t=bud)(j:t.Leaf)(z:t.Plot)(w:t.Leaf→S.Tag)(D:t.Inner→ℕ): issue U R z w D=w j:=by cases ht; haveI:Subsingleton bud.Leaf:=inferInstanceAs (Subsingleton Unit); exact (Sparse.Circuit.Children.bud_eq U R z w D).trans (congr_arg w (Subsingleton.elim ..))
omit X hG in
private lemma rest_empty(i:Fin n)(h:∀k:Bare f,k.val≠i): Sparse.literal (Orbits.tags (d:=age U R ab z D) (token U R ab z D) i) := if_neg ((fun hi:f i=bud=> h ⟨i,hi⟩ rfl):f i≠bud)

set_option maxHeartbeats 530000 in
lemma charge (hd:fledged nodes D)(hm:orbitMargin R.port 0 (skyline z) (anchor z)) : flow U R nodes z (stressTag U ab) D = (∏ i:Fin n,flow U R (f i) (childPlace i z) (childWages i (stressTag U ab)) (childAge i D)) * scalar U R (skyline z ∘ ((↑):Bare f→Fin n)) (stressTag U (displaying ab)) (anchor z):=by -- multiplication
    let s:= stressTag U ab; let d:= age U R ab z D; let a:=token U R ab z D; let p:=post U R ab z D; let x:=skyline z
    let w:=each U R z s D; let F':=R.fresh 0 (Tree.skyline z) (anchor z) (d:=d)
    have hg:voices w = fun i:Fin n=>p i • a i:=funext fun i=> (unit_token U R X hG ab z D hd i).symm
    have h:=Sparse.Undo.restrict (Sparse.readingIdentity U R (anchor z) 0) (skyline z) hm ((↑):Bare f→Fin n) Subtype.val_injective (Orbits.tags a) (fun i=>rest_empty U R ab z D i)
    have hw': (Orbits.tags a) ∘ ((↑):Bare f→Fin n) = stressTag U (displaying ab) :=funext fun i=> unpaid U R ab z D i
    let g:=upon S 0 (anchor z) gapPos (voices (fun z=>extra (S:=S) (z:=z)))
    calc _ = (∏ i,p i)*g (F' a) := by change g (F' (voices w)) = _; rw [hg,F'.map_smul_univ,map_smul]; rfl
         _ = _:= congr_arg ((∏ i,p i)*·) (congr_arg g (h.trans (congr_arg (fun v'=> R.fresh 0 (x ∘ _) (anchor z) (voices v')) hw')))
end Entries
end Currency
end YM.OPE.Short
