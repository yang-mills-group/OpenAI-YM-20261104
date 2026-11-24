import YM.RGComparison.Core16.Silk.Wages
/-!
# Period-cover replay on the unmasked Θ analytic sector (Moments)

Local perturbative Price matrix chart-compatible closeness; Halo estimates POINTED. Does
not change rooted field configs, e.g. using a lifted orientation is consumer's responsibility (we supply for the physical tree).
Price forecast Fk can use this after explicit sinc weights. No analytic covariance claim for true f-variation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Silk
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial Gravity
open Push.AbsoluteSums.Animals Push.Uniform Precision Finset Matrix
open scoped Topology ContDiff PowerSeries Classical BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S F:Side}{ι J k K T Y A D L: Type}[Fintype ι][Fintype J][Fintype k][Fintype K][Fintype T][Fintype Y][Fintype A][Fintype D][Fintype L]
variable {X:Shelf G A D} {P:Planet X S ι k T} {Q:Planet X F J K Y}
    (f:ι→J) {p:Stuff G ι L} {W:ℕ→ℕ→ℝ} {u:Rail G ι}

def cover (p:Stuff G ι L)(f:ι→J):Stuff G J L:= Sum.map f id ∘ p

def relic (f:ι→J) : Wire G ι → Wire G J:= Prod.map f id

def unfoldR (R:Rail G J→Roll)(f:ι→J)(u:Rail G ι) := R (u.map (relic f))

omit [Fintype ι] [Fintype J] [Fintype L] in
lemma projects (i:Wire G L) : field (cover p f) i= (field p i).map (relic f) ∧ clip (cover p f) i= clip p i:=by unfold cover clip field; dsimp only [Function.comp_apply]; cases h:p i.1 <;> exact ⟨rfl,rfl⟩
omit [Fintype ι] [Fintype J] [Fintype L] in
lemma replay (p:Stuff G ι L) (r:ℕ)(i:Wires G L r) : weave (cover p f) i= (weave p i).map (relic f) ∧ gauge (cover p f) i=gauge p i:=⟨by unfold weave; rw [List.map_flatMap]; exact congr_arg (fun x=> List.flatMap x _) (funext fun y=> (projects (p:=p) f y).1), Finset.prod_congr rfl (fun j _=> (projects f (i j)).2)⟩

omit [Fintype ι] [Fintype J] in
lemma night_reels (p:Stuff G ι L) (ψ:(L→G.Color)→ℝ) (R:Rail G J→Roll)(r) : night (cover p f) ψ R (u.map (relic f)) r= night p ψ (unfoldR R f) u r := by
     unfold night tagPrice unfoldR; refine sum_congr rfl (fun i _=>?_); rw [List.map_append,(replay f p r i).1,(replay f p r i).2]

-- Prefix `f` shares handles of all actual-periodic replications. Stencil exactly certified.
def SliceMap {ι J:Type} (a:Finset ι)(b:Finset J)(f:ι→J): Prop:= Set.BijOn f a b
omit [Fintype ι] [Fintype J] in
lemma bonds {F:Type*}[AddCommMonoid F] {a:Finset ι}{b:Finset J}(f:ι→J)(he:SliceMap a b f) (u:ι→F)(v:J→F)(h:∀ i∈ a,v (f i)=u i): ∑ i∈b,v i = ∑ i∈a,u i:= by
  refine (sum_bij (s:=a) (t:=b) (fun i _=>f i) (fun i hi=> he.mapsTo hi) (fun i hi u hu hh=> he.injOn hi hu hh) ?_ (fun i hi=>(h i hi).symm)).symm
  intro j hj; obtain ⟨i,hi,hf⟩:= he.surjOn hj; exact ⟨i,hi,hf⟩

structure Overset (P:Planet X S ι k T)(Q:Planet X F J K Y)(f:ι→J)(s:k→K) : Prop where
    glyph (a:k): P.glyph a= Q.glyph (s a)
    ray (a:k): P.ray a= Q.ray (s a)
    stem (a:k)(i:D): Option.map f (P.stem a i)= Q.stem (s a) i
    soil (a:k): SliceMap (P.soil a) (Q.soil (s a)) f
    within (i:ι): SliceMap (P.within i) (Q.within (f i)) s

variable {f}{s : k→K} (H:P.Steady)(D':Overset P Q f s)(R:Rail G J→Roll)
include D'
omit [Fintype A] [Fintype T] [Fintype Y] [Fintype D] in
private lemma path_map (i:Wire G ι) (a:k) : path Q (relic f i) (s a)=cover (path P i a) f := by
    funext u; rcases u with (_|_)|v; exact rfl; change Sum.inr (Q.ray (s a))= Sum.inr (P.ray a); rw [D'.ray]
    unfold path cover; dsimp only [Function.comp_apply,Sum.elim_inr]; rw [←D'.stem]; cases P.stem a v <;> rfl
include H
omit [Fintype A] [Fintype Y] in
lemma hint_budget (a:k)(i:ι)(h:i∈ P.soil a) : Q.hint (s a) (f i) = P.hint a i:=by
    ext u; unfold Planet.hint; rw [← D'.stem]; rcases he:P.stem a u with _|y; rfl
    by_cases hY:y=i; · simp [hY]
    have hv : f y≠f i:=fun e=> hY ((D'.soil a).injOn (H.thread a u y he) h e)
    simp [hv,hY]
omit [Fintype A] [Fintype Y] in
lemma cheaper_covered {i:Wire G ι} {a:k}(h:a∈ P.within i.1) (n:ℕ) :
    cheaper Q (relic f i) (s a) n R (u.map (relic f))= cheaper P i a n (unfoldR R f) u:=by
    unfold cheaper; rw [path_map D',← D'.glyph a,show (relic f i).1=f i.1 from rfl,show Q.hint (s a) _= _ from hint_budget H D' a i.1 ((P.in_heat ..).2 h)]; exact night_reels ..

omit [Fintype A] [Fintype Y] in
lemma due_covered {i:Wire G ι} : due Q (relic f i) R (u.map (relic f))= due P i (unfoldR R f) u:= by
    apply bonds s (D'.within _) ; intro j hj; exact congr_arg (day · 1) (funext fun y=>cheaper_covered H D' R hj y) -- binder order
omit [Fintype A] [Fintype Y] in
lemma shoulder (i:Wire G ι)(a:k) (h:i.1∈P.soil a) : Q.tip (s a) (relic f i) = P.tip a i:=by rw [←Q.hint_eq,show (relic f i).1=f i.1 from rfl,show Q.hint (s a) _=_ from hint_budget H D' _ _ h]; exact P.hint_eq i a
omit [Fintype A] [Fintype Y] in
lemma tilt_covered (i: Wire G ι) : Gravity.tilt Q (relic f i)= Gravity.tilt P i := by
    apply bonds s (D'.within _) ; intro j hj; unfold tether; rw [D'.ray,D'.glyph,shoulder H D' _ _ ((P.in_heat ..).2 hj)]

-- No T-dependent contacts considered in Wing receipts. Site i.Pointers enough.
omit D' H [Fintype ι] [Fintype J] in
lemma wing_throat (i j:Wire G ι)(h: f i.1= f j.1 → i.1=j.1):
    wingK R (u.map (relic f)) (relic f i) (relic f j) = wingK (unfoldR R f) u i j := by
   have he: guide (relic f i)=cover (guide i) f:=rfl
   have hv: scorecard i j=scorecard (relic f i) (relic f j):=by
       unfold scorecard; change _=if f _=f _ then some (i.2,j.2) else none; by_cases hz:i.1=j.1; · simp [hz]
       rw [if_neg hz,if_neg (mt h hz)]
   unfold wingK; rw [he,←hv]; exact congr_arg (day · 0) (funext fun z=> night_reels f (guide i) _ _ _)
omit H D' [Fintype ι] [Fintype J] in
lemma wing_cover (i: Wire G ι)(h:∀ j∈u, f i.1=f j.1 → i.1=j.1) :
    windDown R (relic f i) (u.map (relic f)) = windDown (unfoldR R f) i u:= by
    let u':= u.map (relic f); let B:=relic (G:=G) f; let e: u'.length=u.length:=List.length_map _; let p:= finCongr e; refine Finset.sum_equiv p (by simp) ?_; intro j hj
    let r:Fin u.length:=p j; change wingK R (u'.eraseIdx j) (B i) u'[j]=wingK (unfoldR R f) (u.eraseIdx r) i u[r]
    rw [show u'[j]=B u[r] from (List.getElem_map ..), show u'.eraseIdx j= (u.eraseIdx r).map B from ?_]; exact wing_throat R i _ (h _ (List.getElem_mem ..))
    exact (List.eraseIdx_map ..)
end YM.RGComparison.Core16.Silk
