import YM.Frontier6.Exact.AnchorDual
import YM.Work.A04
import YM.Work.D06

/-!
# Hand detectors of the unselected hierarchy

Finite point formulas centered at zero, translate everywhere. Include empty
word capability. Later orbit-average for equivariant detector projections.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6
open Function Set Filter Lattice Wilson Spec Table Ortho
open scoped Topology BigOperators ContDiff Classical -- Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G}{F:Extraction.Order}{S:Table C.book}
variable (K:Final C F S) (s:StateIndex K) {n d:ℕ}

def conjug (x:S.Tag): S.Tag:= Work.D06.realTag K.room.kernel.spin x
lemma use_conj {x : Points n} (hx:x ∈ conf n) (v:Fin n → S.Tag) :
  S.useAt (state K s) x (conjug K ∘ v) = star (S.useAt (state K s) x v):=by
  let w:= Ward.expose ∘ v
  have he:S.classTokens ∘ (C.book.conjugate ∘ w) = conjug K ∘ v:=by
    funext i
    change (⟨(v i).1, S.project _ (star (S.representative _ (v i).2))⟩:S.Tag) = _
    rw [← S.conj_project K.room.kernel.spin,S.rep]; rfl
  rw [← he, S.at_project _ (hierarchy K s).laws.toSymmetric (respects K s) hx,(hierarchy K s).spin.real hx]; rfl
lemma read_conj (x:E4)(y:Points n)(v:Fin n→ S.Tag)(B:S.Field d)(hx: Points.cons x y ∈ conf _):
  reading K s x y (conjug K ∘ v) d (S.conj K.room.kernel.spin d B) = star (reading K s x y v d B):=by
  rw [reads_at, reads_at]; simpa only [Fin.comp_cons, conjug, Work.D06.realTag] using use_conj K s hx (Fin.cons ⟨d,B⟩ v)

lemma use_across {x:Points n}(hx:x∈conf _)(v:Fin n→ S.Tag)(a:E4):
  S.useAt (state K s) (Points.across a x) v = S.useAt (state K s) x v:= (hierarchy K s).translations _ _ hx a (Ward.expose ∘ v)

lemma across_cons (a x:E4)(y:Points n): Points.across a (Points.cons x y)=Points.cons (x+a) (Points.across a y):=by
  ext1 i; refine Fin.cases ?_ (fun j=> ?_) i <;> rfl
lemma readings_shift (x:E4)(y:Points n)(v:Fin n→ S.Tag)(B:S.Field d)(hx:Points.cons x y∈conf _)(a:E4):
  reading K s (x+a) (Points.across a y) v d B = reading K s x y v d B:=by
  rw [reads_at, reads_at, ← across_cons]; exact use_across K s hx _ a

/-- Uses *literally* the exterior hierarchy to extract with first point at zero. -/
structure Probe (S:Table C.book) where
  length : ℕ
  letter : Fin length → S.Tag
  exterior : Points length
  clear : Points.cons 0 exterior ∈ conf _

def Probe.form (p:Probe S)(K:Final C F S)(s:StateIndex K)(d:ℕ) := reading K s 0 p.exterior p.letter d
lemma Probe.faithful (d:ℕ): Injective (LinearMap.pi (fun i:Probe S =>(i.form K none d).toLinearMap)):=by
  intro x y h; apply S.field_ext K.room.kernel.laws.toSymmetric; intro n q p hp
  let z:= Points.across (-(p 0)) p
  let w:= Points.tail z; have hz:Points.cons 0 w=z:=by ext1 i; refine Fin.cases ?_ (fun j=> ?_) i; simp [Points.cons,z]; rfl
  have he:Points.cons 0 w∈conf _:=hz.symm ▸ Points.across_in _ hp
  have ht:= congr_fun h (⟨n,q,w,he⟩:Probe S); change reading K none 0 w q d x=reading K none 0 w q d y at ht; rw [reads_at, reads_at,hz] at ht
  exact (use_across K none hp (Fin.cons ⟨d,x⟩ q) (-(p 0))).symm.trans (ht.trans (use_across K none hp (Fin.cons ⟨d,y⟩ q) (-(p 0))))

/-- Finite cap detector before covariance. -/
structure Hand (K:Final C F S) (d:ℕ) where
  list : Finset (Probe S)
  recover : (list → ℂ) →L[ℂ] S.Field d
  exacts (x:S.Field d) : recover (fun i=> i.val.form K none d x) = x

def hand (d:ℕ): Hand K d:= by
  let a (i:Probe S):= (i.form K none d).toLinearMap
  let l:= (Work.A04.finite_faithful a (Probe.faithful K d)).choose
  let h:= (LinearMap.pi (fun i:l=> a i)).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr (Work.A04.finite_faithful a (Probe.faithful K d)).choose_spec)
  exact ⟨l,LinearMap.toContinuousLinearMap h.choose,fun x=> LinearMap.congr_fun h.choose_spec x⟩
end YM.Frontier6
