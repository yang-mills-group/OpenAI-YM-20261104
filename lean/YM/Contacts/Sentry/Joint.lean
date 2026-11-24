import YM.Contacts.Sentry.Environs

/-!
# Convenient center and satellite maps

As physical maps in the common unselected quotient. Symmetry statements will still use only Conf. Express sum spaces also for higher arity root expansions. Keeps `Viewer` estimates transparent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Sensor
open Function Set Filter MeasureTheory Extraction Table Org Spec Power Next.UVStress Costar Analysis Ward
open scoped Topology BigOperators ContDiff

variable {α X:Type*}{ι J M:Type}{G:Gauge}{L:Register G}{S:Table L}
scoped infixr:67 " ⌢ " => Sum.elim
@[simp] lemma comp_both (v:X→α)(x:ι→X)(y:J→X): v ∘ (x ⌢ y)=(v∘x)⌢(v∘y) := by ext1 (i|i)<;> rfl

-- a unit arity at a furnished location
abbrev solo (v:X) : Unit→ X := fun _=> v

/-- `Tag` arrays and their physical typed payload; convenient during additive splitting. -/
abbrev Names (S:Table L)(d:ι→ℕ):= (i:ι)→ S.Field (d i)
def named (d:ι→ℕ) (x:Names S d):ι→ S.Tag:=fun i=>⟨d i,x i⟩
def combine {d:ι→ℕ}{l:J→ℕ}(x:Names S d)(y:Names S l): Names S (d ⌢ l):= Sum.rec x y
@[simp] lemma combine_left {d:ι→ℕ}{l:J→ℕ}(x:Names S d)(y:Names S l)(i:ι): combine (S:=S) (d:=d) (l:=l) x y (.inl i)=x i:=rfl
@[simp] lemma combine_right {d:ι→ℕ}{l:J→ℕ}(x:Names S d)(y:Names S l)(i:J): combine (S:=S) (d:=d) (l:=l) x y (.inr i)=y i:= rfl
lemma two_names {d:ι→ℕ}{l:J→ℕ}(x:Names S d)(y:Names S l): named d x ⌢ named l y = named (d⌢l) (combine x y):=by ext1 (i|i)<;> rfl
lemma recover_names (x:ι→ S.Tag): named (fun i=>(x i).1) (fun i=>(x i).2)=x:= rfl
lemma remove_right_tags {a:ι⊕J→ S.Tag} : (a ∘ Sum.inl) ⌢ (a ∘ Sum.inr)=a:=by ext1 (i|i)<;> rfl
lemma names_only {d:ℕ}(x:S.Field d): (solo (⟨d,x⟩:S.Tag))= named (solo d) (fun _=>x):=rfl

section update
variable [DecidableEq ι][DecidableEq J]{d:ι→ℕ}{l:J→ℕ}(x:Names S d)(y:Names S l)
lemma combine_before (i:ι)(c:S.Field (d i)): combine (update x i c) y= update (combine x y) (.inl i) c:=by ext1 k; cases k with
    | inl a=>by_cases h:a=i; subst a; simp; simp [h,update_of_ne]
    | inr b=> simp [update_of_ne]
lemma combine_after (j:J)(c:S.Field (l j)): combine x (update y j c)= update (combine x y) (.inr j) c:=by ext1 k; cases k with
    | inr a=>by_cases h:a=j; subst a; simp; simp [h,update_of_ne]
    | inl b=> simp [update_of_ne]
end update

variable [Fintype ι][Fintype J](T:Table L)

lemma measured' {x:ι⊕J→ E4}{d:ι→ℕ}{l:J→ℕ}(w:Names S d)(v:Names S l): corr T x (named d w ⌢ named l v)= measure (S:=S) T x (d⌢l) (combine w v):=by rw [two_names]; rfl
lemma queried (P:DiffPlan S) (h:P.Inclusions T)(H:T.Symmetric){d e:ℕ}(he:d≤e)(v:S.Field d)(x:ι→ E4)(hx:Injective x) (w:ι→ S.Tag) [DecidableEq ι](i:ι): corr T x (update w i ⟨e,P.rise he v⟩)=corr T x (update w i ⟨d,v⟩):=by
    let f:= Fintype.equivFin ι; rw [← read_corr T x _ hx H f.symm, ← read_corr T x _ hx H f.symm]; have he' (v) : (update w i v) ∘ f.symm= update (w∘ f.symm) (f i) v:=by
        ext1 k; by_cases h:k=f i; subst k; simp; simp [h,update_of_ne, f.symm_apply_eq]
    rw [he',he']; exact P.inclusion_slot h H he (hx.comp f.symm.injective) (f i) _ _

-- multilinear in one side only too

def observeRight (S:Table L) (x:ι⊕J→ E4)(w:ι→ S.Tag)(l:J→ℕ): MultilinearMap ℂ (fun j=> S.Field (l j)) ℂ:= by
    let d i:= (w i).1; let z : Names S d:= fun i=>(w i).2; let f:= measure (S:=S) T x (d⌢l)
    exact {
        toFun:=fun y=> f (combine z y)
        map_update_add' := fun {h} y v i j=>by classical
                                              simp_rw [combine_after z]; exact f.map_update_add ..
        map_update_smul':= fun {h} y v c i=>by classical
                                             simp_rw [combine_after z]; exact f.map_update_smul .. }
-- if binder implicit {h:? DecidableEq} passed use include [DecidableEq]?. test
lemma observeR {x:ι⊕J→ E4}{w:ι→ S.Tag}{l:J→ℕ}(y:Names S l): observeRight T S x w l y= corr T x (w ⌢ named l y):= (measured' T (fun i=>(w i).2) y).symm

def centerOne (x:E4)(y:J→ E4)(w:J→ S.Tag)(d:ℕ): S.Field d →ₗ[ℂ] ℂ:= by
  let e i:=(w i).1
  let L:= measure (S:=S) T (solo x ⌢ y) (solo d ⌢ e)
  classical
  exact L.toLinearMap (combine (S:=S) (d:=solo d) (l:=e) (solo (0:S.Field d)) (fun i=>(w i).2)) (.inl ())
-- explicit `d` argument despite reducible `solo d`
lemma center_eval (x:E4)(y:J→ E4)(w:J→ S.Tag)(d)(v:S.Field d) : centerOne T x y w d v=corr T (solo x⌢ y) (solo (⟨d,v⟩:S.Tag)⌢ w):=by
   classical
   let F:= measure (S:=S) T (solo x ⌢ y) ((solo d) ⌢ fun i=> (w i).1); let g (p:S.Field d):=combine (S:=S) (d:=solo d) (l:=fun i=>(w i).1) (solo p) (fun i=>(w i).2)
   have he: centerOne T x y w d v = F (g v):=by
        change F (update (g 0) (Sum.inl ()) v) = F _
        congr 1
        ext1 k
        rcases k with i | j; cases i; simp [g,solo]; simp [g,update_of_ne]
   rw [he]; exact (measured' (d:=solo d) (l:=fun i=> (w i).1) T (solo v) (fun i=>(w i).2)).symm
lemma center_rise (P:DiffPlan S) (h:P.Inclusions T)(H:T.Symmetric){d e:ℕ}(he:d≤e)(v:S.Field d){x:E4}{y:J→ E4} (w:J→ S.Tag)(hx:Injective (solo x⌢ y)): centerOne T x y w e (P.rise he v)=centerOne T x y w d v:= by
   classical
   let D:=solo (⟨d,v⟩:S.Tag) ⌢ w
   have hw (t:S.Tag) : update D (Sum.inl ()) t=solo t⌢ w:=by ext1 (i|i); simp [solo]; simp [update_of_ne, D]
   rw [center_eval,center_eval,← hw,← hw]; exact queried T P h H he v _ hx D _
variable {C:Family G}{R:Table C.book}{f:Extraction.Order}
-- motion and shape using Lit estimates
variable (V:Final C f R)(g:Grill C f){P:Pace α} (U:α→Viewer V)
variable (x:α→ E4)(y:α→ J→ E4){b l:ℝ}(h: Trailhead P y x b l)(p:0≤b)(hh:b≤l)(d:J→ℕ)(u:α→Names R d)

def salary (d:ι→ℕ):ℝ:=∑ i, (d i:ℝ) -- d duplicate auto mismatch shadow
include g h p hh
-- test point projections use one new high slot at price b against all other slots
lemma wage_center [DecidableEq J](t:J→ℝ)(z:ℕ)(w:α→ R.Field z){c:ℝ}(hc:P.Priced c w)(hp:∀ j,P.Priced (t j) (fun i=>u i j)): P.Priced ((c+∑ i,t i)+((z:ℝ)*b+l*salary d)) fun i=> centerOne (watches V (U i)) (x i) (y i) (named d (u i)) z (w i):=by
   -- production uses canonical sum DecEq (Unit)
   have he:Lit (Sum.inl ()) P (fun i=>solo (x i)⌢ y i) b l:=h.lit hh
   let s (j:J) i:= u i j
   let F i:= combine (S:=R) (d:= solo z) (l:=d) (solo (w i)) (u i)
   have hx (j) : P.Priced ((solo c⌢ t) j) (fun i=> F i j):=by cases j; exact hc;exact hp _
   simp_rw [center_eval,names_only,two_names]
   apply Pace.Priced.shift (moving V g (Sum.inl ()) (solo z⌢ d) U _ he p hh F _ hx)
   unfold income' salary; rw [Fintype.sum_sum_type,Fintype.sum_sum_type]; simp [solo,Finset.mul_sum,mul_comm]
end YM.Contacts.Sensor
