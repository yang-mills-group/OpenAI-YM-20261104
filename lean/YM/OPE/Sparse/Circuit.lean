import YM.OPE.Sparse.Spine
/-!
# Evaluating a circuit with only one occupied ray

All ancestor field, horizon and field comparison choices remain the same.
Other slots, if *literal units* already in this hierarchy, can be deleted
using the exact multilinear construction AFTER summing each subtree (on the
stated apertures). Truncated outputs at intermediate centers are physical
fields, not a basis treated as scaling-diagonal. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Sparse
open Orbits Orbits.Reader Nesting Nesting.Tree Function Filter Set Table Composite Tracing Nesting.Motion
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
local notation "Q"=>U.sector.derivatives
namespace Circuit
local notation "pump" => Vector.pulse U R
local notation "Stage" => S.Field
variable {I J:Type}[Fintype I][Fintype J]{m:ℕ}{x:I→E4}{o:E4}{w:I→S.Tag}

lemma fill (h:∀ i:I, literal (w i))(hz:orbitMargin R.port m x o): R.fresh m x o (voices w)=R.cutTest m 0 (S.unit 0):=by
    have eq(x':Empty→I):R.fresh m x o (voices w)=R.fresh m (fun (_:Empty)=>0) o (voices (fun _:Empty=>(⟨0,S.unit 0⟩:S.Tag))):=by
        have he:=Undo.restrict (readingIdentity U R o m) x hz x' (fun a=> nomatch a) w (fun i hh=>h i)
        exact he.trans (congr_arg₂ (fun x' v' => R.fresh m (d:=degrees (v':Empty→S.Tag)) x' o (voices v')) (Subsingleton.elim _ _) (Subsingleton.elim _ _))
    let z:Unit→E4:=sole 0
    have hi : orbitMargin R.port m (fun i=>z i+o) (0+o):=(translateMargin (m:=m) (x:=z) (o:=0) o).2 (centerMargin R.port _)
    let p:Unit→S.Tag:=fun _=>⟨0,S.unit 0⟩
    obtain he:=Undo.restrict (readingIdentity U R (0+o) m) (fun i=>z i+o) hi (fun _:Empty=>()) (fun q=> nomatch q) p (fun i he=>rfl)
    calc _ = _:=eq (fun i=> nomatch i)
         _ = R.fresh m (fun i=>z i+o) (0+o) (voices p) := by
              apply Eq.trans _ he.symm; unfold Undo.apply -- placeholder unnecessary? readingIdentity is Identity not kernel
              rw [zero_add]; congr; funext x; cases x
         _ = R.fresh m z 0 ((sole (S.unit 0)):Labels S (fun _:Unit=>0)):= R.fresh_transport ..
         _ = _ := Orbits.Reader.single R m 0 (S.unit 0) -- check

abbrev Sparse (v:I→S.Tag)(j:I) :Prop:=∀ i:I,i≠j→literal (v i)

section Selected

lemma line {t:Nesting.Tree} {m:ℕ} (j:t.Leaf)(z:t.Plot){v:t.Leaf→S.Tag}(hv:Sparse v j)(hm:orbitMargin R.port m (Tree.profile z) (anchor z)):
    R.fresh m (Tree.profile z) (anchor z) (voices v)= R.fresh m (Tree.profile (z ∘ layout _ j)) (anchor (z ∘ layout _ j)) (voices fun _:(pathTree t j).Leaf=>v j):=by
    rw [root,Tracing.points]
    haveI:= (name_unique t j)
    let e: (pathTree t j).Leaf→t.Leaf:=fun _=>j
    change _=R.fresh m (Tree.profile z ∘ e) (anchor z) (voices (v ∘ e))
    exact Undo.restrict (readingIdentity U R (anchor z) m) (Tree.profile z) hm e (fun a b hh=>this.2.allEq a b) v (fun i hi=> hv i (hi (Nonempty.some this.1)).symm)

lemma mark(j:I)(m:ℕ){v:I→S.Tag}(hv:Sparse v j)(hm:orbitMargin R.port m x o):
 R.fresh m x o (voices v) = R.fresh m (fun (_:Fin 1)=>x j) o (voices (fun (_:Fin 1)=> v j)):=by
 let e:=fun (_:Fin 1)=>j
 change _=R.fresh m (x ∘ e) (o) (voices (v ∘ e))
 exact Undo.restrict (readingIdentity U R o m) x hm e (fun a b hh=>Subsingleton.elim ..) v (fun i hi=> hv i (hi 0).symm)
end Selected

namespace Children
variable {t:Nesting.Tree} (z:t.Plot)(v:t.Leaf→S.Tag)(D:t.Inner→ℕ)
local notation "pulse" => Vector.pulse U R
abbrev issue : S.Tag:= ⟨_, pulse z (voices v) D⟩
variable {n:ℕ}{f:Fin n→Nesting.Tree}
local notation "tree"=> fork n f
local notation "book"=> fun j:tree.Inner=>D j
abbrev each (z:(fork n f).Plot)(v:(fork n f).Leaf→S.Tag)(D: (fork n f).Inner→ℕ): Fin n→S.Tag:=fun i=> issue U R (childPlace i z) (childWages i v) (childAge i D)
lemma perfect (hx:z∈Kernel.aperture U R t (boundNow t D) D) (hv:∀ j:t.Leaf,literal (v j)): literal (issue U R z v D) :=by induction t with
  | bud=>rw [show issue U R z v D=v () from Sigma.ext rfl (heq_of_eq (Vector.pulse_bud ..))]; exact hv _
  | fork n f ih=>
      have hp:=hx.1
      change pulse z (voices v) D=S.unit (boundNow (fork n f) D)
      have he (q:Fin (boundNow (fork n f) D+1)): R.fresh q.val (skyline z) (anchor z) (emitted U R z (voices v) D) = R.cutTest q.val 0 (S.unit 0):= fill U R (w:=each U R z v D) (fun i=>ih i _ _ _ (hx.2 i) (fun k=>hv ⟨i,k⟩)) (hp q)
      rw [pulse_pack]; simp_rw [he]; rw [R.reconstruct (boundNow (fork n f) D) 0 (Nat.zero_le _), U.sector.derivatives.fixs R.lifts R.continuum.laws (d:=0)]

variable {D:(fork n f).Inner→ℕ}{z:(fork n f).Plot}{w:(fork n f).Leaf→S.Tag}
local notation "next" p => childWages p w
set_option quotPrecheck false
local notation "strip" p => (fun (_: (pathTree (fork n f) p).Leaf)=> w p)
lemma step_selected {m:ℕ}(hx : orbitMargin R.port m (skyline z) (anchor z))(p:(fork n f).Leaf)(ht: ∀ i:Fin n, i≠ p.1→ literal (each U R z w D i)) (he : each U R z w D p.1 = issue U R (childPlace p.1 z ∘ layout (f p.1) p.2) ((fun _:(pathTree (f p.fst) p.snd).Leaf=>w p)) (childAge p.fst D ∘ inlet (f p.fst) p.snd)):
 R.fresh m (skyline z) (anchor z) (voices (each U R z w D)) = R.fresh m (skyline (z ∘ layout (fork n f) p)) (anchor (z ∘ layout (fork n f) p)) (voices (each U R (f:=fun (_:Fin 1)=>pathTree (f p.1) p.2) (z ∘ layout (fork n f) p) (strip p) (D ∘ inlet _ p))):=by
    refine (mark U R (x:=skyline z) p.1 m (v:=each U R z w D) ht hx).trans ?_
    have h_z (i:Fin 1):skyline z p.fst = skyline (z ∘ layout (fork n f) p) i:= by change z (.inr ⟨p.fst,(f p.fst).topSeat⟩)= z (layout _ p (Sum.inr ⟨i,(pathTree ..).topSeat⟩)); unfold layout; rw [← Tracing.top (f p.fst) p.snd]; rfl
    have h_o:= (Tracing.root (fork n f) p z)
 --   have hL (i:Fin 1):= he
    let F (f:Fin 1→S.Tag)(x:Fin 1→E4):=R.fresh m x (anchor z) (voices f)
    rw [h_o]; change F (fun _=>_) _=F _ _
    exact congr_arg₂ F (funext fun i=>show _ from he) (funext h_z)

-- Prevent dependent casts of the assembled field tuple while recursing
def fuse(d:ℕ)(g:∀j:ℕ,S.Field j) : S.Tag := ⟨d,∑ q:Fin (d+1), U.sector.derivatives.rise (d:=q.val) (Nat.le_of_lt_succ q.isLt) (g q)⟩
lemma fuse_eq (d d':ℕ)(h:d=d')(g g':∀j:ℕ,S.Field j)(he:∀ j≤d,g j=g' j):fuse U d g=fuse U d' g':=by
  subst d'; refine Sigma.ext rfl (heq_of_eq ?_)
  unfold fuse; dsimp only; exact Finset.sum_congr rfl (fun i _=>congr_arg ((Q).rise (d:=i.val) _) (he i.val (Nat.le_of_lt_succ i.isLt)))
lemma bud_eq (z:Nesting.Tree.bud.Plot)(w:Nesting.Tree.bud.Leaf→S.Tag)(D:Nesting.Tree.bud.Inner→ℕ): issue U R z w D = w () := Sigma.ext rfl (heq_of_eq (Vector.pulse_bud ..))
lemma compiled {n:ℕ}{f:Fin n→Nesting.Tree}(z:(Nesting.Tree.fork n f).Plot)(w:(Nesting.Tree.fork n f).Leaf→S.Tag)(D:(Nesting.Tree.fork n f).Inner→ℕ):issue U R z w D = fuse U (Composite.boundNow _ D) (fun i:ℕ=> R.fresh i (skyline z) (anchor z) (voices (each U R z w D))) := Sigma.ext rfl (heq_of_eq (pulse_pack U R z (voices w) D))


set_option maxHeartbeats 500000 in
lemma interpret (t:Tree)(p:t.Leaf)(z:t.Plot)(w:t.Leaf→S.Tag)(D:t.Inner→ℕ) (hv:Sparse w p) (hx: z∈Kernel.aperture U R t (boundNow t D) D): issue U R z w D=issue U R (z ∘ layout t p) (fun _=> w p) (D ∘ inlet t p):=by induction t with
  | bud=>cases p; exact (bud_eq U R z w D).trans (bud_eq U R (z ∘ layout bud ()) _ (D ∘ inlet bud ())).symm -- issue
  | fork n f ih=>
     let t:=Nesting.Tree.fork n f
     let Z:=z ∘ layout t p; let D':=D ∘ inlet t p
     let v':(pathTree t p).Leaf→S.Tag:=fun _=> w p
     refine (compiled U R z w D).trans (Eq.trans (?_) ((compiled U R (f:=fun (_:Fin 1)=>pathTree (f p.fst) p.snd) Z v' D').symm))
     refine fuse_eq U _ _ rfl _ _ fun j hj=>?_ -- adjust
     exact step_selected U R (f:=f) (z:=z) (m:=j) (D:=D) (hx.1 ⟨j,Nat.lt_succ_of_le hj⟩) p (fun i hi=>perfect U R (childPlace i z) (fun l=> w ⟨i,l⟩) (childAge i D) (hx.2 i) (fun k=> hv ⟨i,k⟩ (fun he=>hi (Sigma.ext_iff.mp he).1))) (ih p.fst p.snd (childPlace p.1 z) (childWages p.1 w) (childAge p.1 D) (fun b hb=> hv ⟨p.fst,b⟩ (fun he=> hb (eq_of_heq ((by cases p; exact (Sigma.mk.inj he).2))))) (hx.2 p.fst))
end Children
end Circuit
end YM.OPE.Sparse
