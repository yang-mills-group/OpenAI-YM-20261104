import YM.AveragedStep.Parcel.Forms
/-! Table of actual factors for a GIVEN pair of tori. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Lattice RG Wilson Function MeasureTheory Filter Loops RG.Patch
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius
abbrev Parcel (c f:Side):= Face (Per f) ⊕ (Site c × Option Axis)
variable {G:Gauge}{c f:Side}(S:StepData c f)
def sort : Parcel c f → Mold:= Sum.map Prod.snd Prod.snd
-- default station tether maps unused parts to any; no indicators collapsed in actual product
def leads (i:S.Choices):Parcel c f→Leash S.patch:=Sum.elim (fun _=> Classical.arbitrary _) (fun p=>
  (i.1 p.1, p.2.elim (i.1 p.1) (fun a=>i.1 (p.1+step a)),p.2.elim S.patch.center (fun a=>i.2 (p.1,a))))
-- Classical.arbitrary needs Nonempty Leash

def point : Parcel c f→Site f := Sum.elim Prod.fst (S.ratio.embed ∘ Prod.fst)
def header : Parcel c f→ Option (Edge (Site c)):= Sum.elim (fun _=> none) (fun p=> p.2.map fun a=> (p.1,a))
-- unused none port read at 1 ; prefer option addresses
def hook (p:Parcel c f): Interior S.patch → Option (Rim c f)
 | none=> (header p).map Sum.inr
 | some j=> some (Sum.inl (wrap f j.val.1+point S p,j.val.2))
def aim (X:Rim c f→G.El)(o:Option (Rim c f)) := o.elim 1 X
def gathers (p : Parcel c f) (X : Rim c f → G.El): Values S.patch G := fun i=> aim X (hook S p i)
lemma cursor (p:Parcel c f)(w:Board G c f):
    let i:=point S p; let v:CoverConfig G:=expandAt i w.1
    let hi:=(header p).elim 1 w.2
    let X:=Sum.elim w.1 w.2
    gathers S p X=limitTo S.patch v hi:=by
  intro i v j X
  funext a; cases a; cases he: header p <;> simp [gathers,aim, hook,he,j,limitTo,X]
  rfl

def costume (P:Patch)(K:KernelChoices)(a:Mold)(r:Leash P)(X:Values P G) :ℝ:= temperatures P K a r (pretend P X) (X none)
def mark (P:Patch)(K:KernelChoices)(a:Mold)(r:Leash P)(X:Values P G) :ℝ:= bands P K a r (pretend P X) (X none)
def temperature (i:S.Choices)(a:Parcel c f)(w:Board G c f) := costume S.patch S.kernel (sort a) (leads S i a)
    (gathers S a (Sum.elim w.1 w.2))
def marked (i:S.Choices)(a:Parcel c f)(w:Board G c f):= mark S.patch S.kernel (sort a) (leads S i a)
    (gathers S a (Sum.elim w.1 w.2))
variable (h:S.patch.Branches S.kernel G)
include h
lemma costume_bill (i:S.Choices)(a:Parcel c f)(w:Board G c f):
    let T:= expandAt (point S a) w.1
    let l:= leads S i a
    let V:= (header a).elim 1 w.2
    temperature S i a w = temperatures S.patch S.kernel (sort a) l T V ∧ marked S i a w=bands S.patch S.kernel (sort a) l T V := by
   intro T l V
   unfold temperature marked costume mark; simp_rw [cursor]
   exact prices_agree S.patch S.kernel h _ l T V

lemma terrace_face (i:S.Choices)(a:Face (Per f))(w:Board G c f):
    temperature S i (.inl a) w=G.price (faceValue w.1 a)∧marked S i (.inl a) w=1:=by
 obtain ⟨hh,hv⟩:=costume_bill S h i (Sum.inl a) w
 rw [hh,hv]; change G.price (faceValue (expandAt a.1 w.1) ((0:Cover),a.2))=_ ∧ _
 rw [faceValue,travel_at,map_zero,zero_add]; exact ⟨rfl,rfl⟩
lemma terrace_station (i:S.Choices)(x:Site c)(w:Board G c f):temperature S i (.inr (x,none)) w=0∧
    marked S i (.inr (x,none)) w=S.patch.frameMass S.kernel (expandAt (S.ratio.embed x) w.1) (i.1 x):=by
 obtain ⟨hh,hv⟩:=costume_bill S h i (Sum.inr (x,none)) w; rw [hh,hv]; exact ⟨rfl,rfl⟩
lemma terrace_bond (i:S.Choices)(e:Edge (Site c))(w:Board G c f):temperature S i (.inr (e.1,some e.2)) w=
    S.kernel.penalty*G.price (w.2 e*(S.prediction w.1 i e)⁻¹)∧
    marked S i (.inr (e.1,some e.2)) w=S.patch.predictorMass S.kernel (S.connector w.1 i.1 e) (i.2 e):=by
 obtain ⟨hh,hv⟩:=costume_bill S h i (Sum.inr (e.1,some e.2)) w; rw [hh,hv]
 let P:=S.patch; let K:= S.kernel
 let U:=expandAt (S.ratio.embed e.1) w.1
 let l (u:Site c) := i.1 u; let Z:=U
 change K.penalty*G.price (w.2 e*(P.predict K (coverY P _ (l e.1) (l (e.1+step e.2)) e.2 U) _)⁻¹)= _ ∧ P.predictorMass K (coverY P _ (l e.1) (l (e.1+step e.2)) e.2 U) (i.2 e)=_
 rw [show coverY P K (l e.1) (l (e.1+step e.2)) e.2 U=S.connector w.1 i.1 e from ?_]; exact ⟨rfl,rfl⟩
 unfold coverY StepData.connector StepData.frames l U P
 rw [S.leap, show expandAt (S.ratio.embed e.1+S.patch.L.val • step e.2) w.1 = translate (S.patch.L.val • step e.2) (expandAt (S.ratio.embed e.1) w.1) from ?_]
 funext z; simp only [expandAt,translate,map_add,map_nsmul,wrap_step,add_right_comm,add_assoc]

lemma invoice (i:S.Choices)(β:ℝ)(w:Board G c f) :
    weightQ S β i w*bare β w.1 = (S.penaltyZ β G)⁻¹^(Fintype.card (Edge (Site c)))*
      (∏ p,marked S i p w)*Real.exp (-β*∑ p,temperature S i p w) := by
  classical
  unfold weightQ StepData.likelihood StepData.noise bare energy StepData.penaltyWeight
  rw [Finset.prod_mul_distrib,Finset.prod_const, Finset.card_univ,← Real.exp_sum]
  rw [Fintype.prod_sum_type,Fintype.sum_sum_type]; conv_rhs=>
    simp only [(terrace_face S h _ _ _).1,(terrace_face S h _ _ _).2,Fintype.prod_prod_type,Fintype.sum_prod_type,Fintype.prod_option,Fintype.sum_option,(terrace_station S h _ _ _).1,(terrace_station S h _ _ _).2,Finset.prod_const_one,one_mul,zero_add]
  -- compare sums/prods after split, Edge abbrev.
  have he(x:Site c)(v:Axis):= terrace_bond S h i (x,v) w
  simp_rw [(fun x v=> (he x v).1),(fun x v=>(he x v).2),Finset.prod_mul_distrib,mul_add,Real.exp_add]
  change ((∏ _,_)*(∏ _:Site c×Axis,_))* (_*Real.exp (∑ _:Site c×Axis,_))*_= _
  conv_lhs=> simp only [Fintype.prod_prod_type,Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum, ← mul_assoc (-β) S.kernel.penalty]; ring -- lhs exp uses -β*κ
end YM.AveragedStep
