import YM.Integration.WilsonOriginalCensusPageCumulant

/-! Choose a complete inherited binder at every occupied node before opening
its independent relative page. A quiet node has exactly one choice of page. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusPageAssignments
open Finset
open scoped Classical BigOperators
variable {ι I U:Type} [Fintype ι]

def occupied (m:ι→Option I):Finset ι:=univ.filter (fun v=>(m v).isSome)

def names (a:ι→Option (I × U))(v:ι):Option I:=(a v).map Prod.fst

def bind (m:ι→Option I)(p:occupied m→U)(v:ι):Option (I×U):=
  if h:v∈occupied m then some ((m v).get (mem_filter.mp h).2,p ⟨v,h⟩) else none

def pages (a:ι→Option (I×U))(v:occupied (names a)):U:=
  ((a v.val).get (by simpa [names] using (mem_filter.mp v.property).2)).2

theorem label (m:ι→Option I)(p:occupied m→U)(v:ι):names (bind m p) v=m v:=by
  classical
  cases h:m v with
  | none=>simp [names,bind,occupied,h]
  | some i=>simp [names,bind,occupied,h]

theorem unpack (a:ι→Option (I×U))(v:ι):bind (names a) (pages a) v=a v:=by
  classical
  cases h:a v with
  | none=>simp [bind,names,occupied,h]
  | some z=>rcases z with ⟨i,p⟩;simp [bind,names,occupied,h,pages]

omit [Fintype ι] in
private theorem sameSite {s t:Finset ι}(same:s=t){v:s}{z:t}(identify:HEq v z):v.val=z.val:=by
  subst t
  exact congrArg Subtype.val (eq_of_heq identify)

def book:(Σm:ι→Option I,occupied m→U) ≃ (ι→Option (I×U)) where
  toFun a:=bind a.1 a.2
  invFun p:=⟨names p,pages p⟩
  right_inv a:=funext (unpack a)
  left_inv:=by
    rintro ⟨m,p⟩
    have eq:names (bind m p)=m:=funext (label m p)
    apply Sigma.ext eq
    apply Function.hfunext
    · exact congrArg (fun m:ι→Option I=>↥(occupied m)) eq
    intro v z hv
    have vals:v.val=z.val:=sameSite (congrArg occupied eq) hv
    dsimp only
    have hp:v.val∈occupied m:=vals.symm ▸ z.property
    unfold pages
    simp only [bind,hp,dif_pos,Option.get_some]
    congr 1
    exact Subtype.ext vals

theorem recorded [Fintype I] [Fintype U] (K:(ι→Option (I×U))→ℂ):
    (∑a,K a)=∑m:ι→Option I,∑p:occupied m→U,K (bind m p):=by
  classical
  rw [←book.sum_comp K,Fintype.sum_sigma]
  rfl

end YM.Integration.WilsonOriginalCensusPageAssignments
end
