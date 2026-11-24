import YM.Integration.WilsonOriginalCensusPageAssignments
import YM.Integration.WilsonReceivedDepositedAlias

/-! A surviving temporary source set chooses one physical page for each
original pupil that is used. The other pupils require no choice of page. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusCopyGraphs
open Finset Function Marker Multi RG05Readout.Many
open scoped Classical BigOperators
variable {I U:Type}[DecidableEq I][DecidableEq U]

def graph (q:Finset I)(p:q→U):Finset (I×U):=q.attach.image (fun i=>(i.val,p i))

theorem member {q:Finset I}{p:q→U}{z:I×U}:
    z∈graph q p ↔ ∃h:z.1∈q,p ⟨z.1,h⟩=z.2:=by
  obtain ⟨i,u⟩:=z
  constructor
  · intro inside
    obtain ⟨⟨v,hv⟩,_,id⟩:=mem_image.mp inside
    obtain ⟨rfl,eq⟩:=Prod.mk.inj id
    exact ⟨hv,eq⟩
  · rintro ⟨h,eq⟩
    exact mem_image.mpr ⟨⟨_,h⟩,mem_attach ..,Prod.ext rfl eq⟩

theorem homes (q:Finset I)(p:q→U):(graph q p).image Prod.fst=q:=by
  ext i
  constructor
  · intro h
    obtain ⟨z,hz,rfl⟩:=mem_image.mp h
    exact (member.mp hz).choose
  · intro h
    exact mem_image.mpr ⟨(i,p ⟨i,h⟩),member.mpr ⟨h,rfl⟩,rfl⟩

theorem one (q:Finset I)(p:q→U):Set.InjOn Prod.fst (graph q p:Set (I×U)):=by
  rintro ⟨i,u⟩ hu ⟨j,v⟩ hv ij
  change i=j at ij
  subst j
  obtain ⟨hi,first⟩:=member.mp hu
  obtain ⟨_,second⟩:=member.mp hv
  exact Prod.ext rfl (first.symm.trans second)

abbrev Catalog (I U:Type):=Σq:Finset I,q→U
abbrev Valid (I U:Type):={q:Finset (I×U)//Set.InjOn Prod.fst (q:Set (I×U))}

def listed (c:Catalog I U):Valid I U:=⟨graph c.1 c.2,one _ _⟩

private theorem exactGraph (q:Finset (I×U))(unique:Set.InjOn Prod.fst (q:Set (I×U))):
    ∃p:(q.image Prod.fst)→U,graph (q.image Prod.fst) p=q:=by
  classical
  have stock(i:q.image Prod.fst):∃u,(i.val,u)∈q:=by
    obtain ⟨⟨j,u⟩,placed,same⟩:=mem_image.mp i.property
    exact ⟨u,same ▸ placed⟩
  let p(i:q.image Prod.fst):U:=(stock i).choose
  have valid(i:q.image Prod.fst):(i.val,p i)∈q:=(stock i).choose_spec
  refine ⟨p,?_⟩
  ext ⟨i,u⟩
  constructor
  · intro entered
    obtain ⟨h,eq⟩:=member.mp entered
    change p ⟨i,h⟩=u at eq
    exact eq ▸ valid ⟨i,h⟩
  · intro marked
    have h:i∈q.image Prod.fst:=mem_image.mpr ⟨(i,u),marked,rfl⟩
    exact member.mpr ⟨h,congrArg Prod.snd (unique (valid ⟨i,h⟩) marked rfl)⟩

def registry:Catalog I U≃Valid I U:=Equiv.ofBijective listed (by
  constructor
  · rintro ⟨q,p⟩ ⟨s,t⟩ same
    have ink:graph q p=graph s t:=congrArg Subtype.val same
    have names:q=s:=(homes q p).symm.trans ((congrArg (Finset.image Prod.fst) ink).trans (homes s t))
    subst s
    apply congrArg (Sigma.mk q)
    funext i
    have placed:(i.val,p i)∈graph q t:=ink ▸ member.mpr ⟨i.property,rfl⟩
    obtain ⟨_,eq⟩:=member.mp placed
    exact eq.symm
  · rintro ⟨q,unique⟩
    obtain ⟨p,ink⟩:=exactGraph q unique
    exact ⟨⟨q.image Prod.fst,p⟩,Subtype.ext ink⟩)

theorem sum [Fintype I][Fintype U](K:Finset (I×U)→ℂ):
    (∑q:Valid I U,K q.val)=∑s:Finset I,∑p:s→U,K (graph s p):=by
  rw [←registry.sum_comp (fun q:Valid I U=>K q.val),Fintype.sum_sigma]
  rfl

omit [DecidableEq I] [DecidableEq U] in
theorem admissible {V:Type}[DecidableEq V](B:Census V)(mode:I→Hot B)(q:Finset (I×U))
    (approved:Lit (parts B) (fun z:I×U=>mode z.1) q):Set.InjOn Prod.fst (q:Set (I×U)):=by
  intro x hx y hy same
  exact approved.2 hx hy (congrArg mode same)

end YM.Integration.WilsonOriginalCensusCopyGraphs
end
