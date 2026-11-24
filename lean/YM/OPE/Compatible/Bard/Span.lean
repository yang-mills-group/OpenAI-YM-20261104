import YM.OPE.Compatible.Bower.Tender
/-!
# Initialize lifts of the unknown negative match, in orientation goals

Use true registered C labels at the correspondingly measured grade,
so propagated markings are available directly. Certified axis is the
inverse **finite cutoff** index from the `Music` which will also be
used in `Fortune`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG Wilson MeasureTheory MergeProof Finset
open Push Marker Source Accent Ribbon Menu Local Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open PhysicalNext.Repeat.Legato Bandage
open Extra.Multi GridApprox.Nil Next.Rank
open Extra.Trajectories MergeProof.Float Ribbons Ribbons.ManyCopies Ribbons.ManyCopies.Stem
open scoped Topology BigOperators Classical
variable {V:Type} {G:Gauge}{C:Family G}{A:Allot C}{P:Ensemble V}
    {d b k N p:ℕ}(X:Extra.Histories.Music (C.labels.level d) C.path N p)
structure Solvent (X:Extra.Histories.Music (C.labels.level d) C.path N p) : Prop where
    bank : (C.factory d N p).entries=(X.draft C.path).inits
    pull : Sung (C.localSection d) C.path N p C.params A.W (C.ref d) X
    rolls i : C.ref d ≤ i→∀ hi:i<N, Carol (C.localSection d) C.path N p i (A.D N p i hi) (X.tone (i+1)) (X.tone i) (waybill C.path.levels i)
lemma recital (A:Allot C) (p:ℕ) (h:C.ref d ≤ N): ∃ X:Extra.Histories.Music (C.labels.level d) C.path N p, Solvent (A:=A) X:=by
   obtain ⟨X,hF,h,hM,hZ⟩:= (A.buy.system.costs.aim d N p h).lyrics; exact ⟨X,hF,h,hM⟩
set_option quotPrecheck false
local notation "Q"=> C.factory d N p
local notation "F"=> C.labels.level d
local notation "V!"=>(F).Index
def sonnet (C:Family G)(X:Extra.Histories.Music (C.labels.level d) C.path N p)(k:ℕ)(i:(C.labels.level d).Index): (C.labels.level d).Coeff := (X.tone k).index.symm (Size.axis (C.labels.level d) i)
def lyric (C:Family G) (X:Extra.Histories.Music (C.labels.level d) C.path N p)(k:ℕ)(i:(C.labels.level d).Index) : C.label d := (C.factory d N p).terminal (sonnet C X k i)
variable (h:Solvent (A:=A) X)
include h
lemma ink_note (i:V!) {k:ℕ}: (C.factory d N p).entries k ((C.factory d N p).terminal.symm (lyric C X k i))=(X.tone k).plays (sonnet C X k i):=by
    unfold lyric; rw [LinearEquiv.symm_apply_apply,h.bank]; rfl
lemma lyrics_value (hp:C.ref d ≤ k)(hk:k ≤ N) (i:V!) : Spindle.paid C d k N p (lyric C X k i)=‖alto C.path k d‖:=by
   unfold Spindle.paid Price.awake Price.columns; rw [Size.smul]; dsimp only; rw [ink_note X h,h.pull.earned k hp hk|>.currents (sonnet C X k i)]; unfold sonnet; rw [LinearEquiv.apply_symm_apply,Size.size_axis,mul_one]; rfl

def ballot (C:Family G)(k d:ℕ):= fly C.path.levels d k*C.S.a k^d/2
omit h
lemma ballot_pos (C:Family G)(k d:ℕ): 0<ballot C k d:=by
    unfold ballot; rw [fly_eq]; have he:= β_pos C k; have hp:=C.S.a_pos k; positivity
variable [Fintype V][DecidableEq V]
include X h
-- start arbitrary base, index chosen
lemma pointer {E o:Track C.path V p}(hg:C.Makes)(hp:C.ref d < k)(hk:k ≤ N)(hP:C.ref 0≤k)(he:Migrating C.path k p N E) (hy:Migrating C.path k p N o) (hb: 1 ≤ b)
    (hx:∀ j,k ≤ j→ j ≤ N→ ∀ x:V,x≠P.v→ o j x=affine (P.move x).1 (E j x) (o j P.v))(i:(C.labels.level d).Index):
    let f:= fun x y=> stepUp (P.move x) (o N x) (C.O N p (lyric C X k i) 0) y
    ∃ L:Line A P N p k N b E o, L.w k=ballot C k d ∧ Budges P C.path N p (far C.path.levels N) (L.w N) (E N) (L.X N) f∧ Stamp (N:=N) P (C.localSection d) (E k) ((X.tone k).plays (sonnet C X k i)) (L.X k):=by
    cases k
    next=> omega
    next k=>
       intro z; let w:= ballot C (k+1) d; have hw:0<w:= ballot_pos ..; have hZ:2*w*‖alto C.path (k+1) d‖=fly C.path.levels d (k+1):=by
          rw [alto_norm]; unfold w ballot; have hx:= C.S.a_pos (k+1); change 2*(fly C.path.levels d (k+1)*C.S.a (k+1)^d/2)*(C.S.a (k+1)^d)⁻¹=_; field_simp
       obtain ⟨L,hL,hB,hT⟩:= fresh_line A P (p:=p) (lyric C X (k+1) i) hg hb hP (Nat.le_of_lt_succ hp) le_rfl hk he hy (fun j hi ht=>False.elim (by omega)) hx hw ((lyrics_value X h hp.le hk i).symm ▸ hZ.le) -- C.ref d proof used hp type succ
       exact ⟨L,hL.trans (Run.below_main _),hB, ink_note X h i ▸ hT (k+1) le_rfl hk⟩
end YM.OPE.Allot
