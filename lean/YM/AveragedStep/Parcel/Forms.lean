import YM.AveragedStep.Slice.Rows
import YM.RG.Measurable
/-! # Finite stem of an elementary factor (top transfer). Not F756's HEAD
truncation. This list at fixed L includes *all* elementary factors in our
algorithm.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Lattice Wilson RG RG.Patch Filter Function MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable (P:Patch)
/-- common finite cover for reading one of the elementary factors,
preparing before varying (in particular need to bind the tags before using
their smooth region simplification).
-/
def walks := Finset.univ.biUnion fun x:P.Points=> Finset.univ.biUnion fun y:P.Points=>
      Finset.univ.biUnion fun l:Lattice.Order=> (visits x.val (route x.val y.val l)).toFinset
def arrival :Finset Cover:= P.sites ∪ (walks P) ∪ P.sites.biUnion (fun x=> Finset.univ.image fun i:Axis=> x+step i)
def spur (i:Axis):Walk:=List.replicate P.L.val (posDir i)
def hub (i:Axis):Cover:=P.L.val • step i
def flights:Finset Cover:= arrival P ∪ Finset.univ.biUnion (fun i:Axis=> (arrival P).image (·+hub P i)
       ∪ P.sites.biUnion fun x=> (visits x (spur P i)).toFinset)
def circular : Finset Cover:= Finset.univ.biUnion fun p:PlaqAxes=> (visits (0:Cover) (square p.val.1 p.val.2)).toFinset

def domain : Finset Cover:=flights P ∪ circular ∪ P.sites
abbrev Grounding:= {x:Edge Cover // x.1∈domain P}
/-- one optional coarse bond (all t local frames only need one). -/
abbrev Interior:=Option (Grounding P)
abbrev Values (G:Gauge):= Interior P→G.El
variable {G:Gauge}
def limitTo (v:CoverConfig G)(y:G.El):Values P G:= fun i=>
  Option.casesOn i y (fun i=>v i.val)
def pretend (w:Values P G):CoverConfig G:=fun i=>if h:i.1∈domain P then w (some ⟨i,h⟩) else 1
lemma pretend_agrees (v:CoverConfig G)(y:G.El):∀ i:Edge Cover,i.1∈domain P→pretend P (limitTo P v y) i=v i:=by intro i hi; simp [pretend,hi,limitTo]

private lemma travel_agree (x: Cover)(w:Walk){U V:CoverConfig G}
    (h:∀ i:Edge Cover,i.1∈(visits x w).toFinset→U i=V i):travel U x w=travel V x w:=
 travel_local _ _ U V fun i hi _=> h i (List.mem_toFinset.mpr hi)
private lemma frames_agree (K:KernelChoices)(h:P.Branches K G){U V:CoverConfig G}
    (he : ∀ i:Edge Cover,i.1∈ arrival P → U i=V i)(r:P.FrameTag):
    P.frame K U r=P.frame K V r ∧ P.frameMass K U r=P.frameMass K V r:=by
 classical
 have hr(x y:P.Points)(l:Lattice.Order):travel U x.val (route x.val y.val l)=travel V x.val (route x.val y.val l):=travel_agree _ _ fun i hi=> he i <|
    Finset.mem_union_left _ <| Finset.mem_union_right _ <| Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨y,Finset.mem_univ _,Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,hi⟩⟩⟩
 have hv(t:P.Frame G):P.via t U =P.via t V:=by unfold via; simp_rw [hr]
 have hu: P.axial U=P.axial V:=by unfold axial; simp_rw [hr]
 have ho:P.score U=P.score V:=by unfold score; simp_rw [hv]
 have hMin:P.usesMin K U ↔ P.usesMin K V:=by simp only [usesMin,hu,hv]
 by_cases hx:P.usesMin K V
 · simp_rw [Patch.frame,frameMass,if_pos hx,if_pos (hMin.mpr hx),and_true]
   apply (h.frame_unique V hx).unique _ (P.min_exists _).choose_spec
   simpa only [minimizing,← ho] using! (P.min_exists U).choose_spec
 have hp : ¬P.usesMin K U:= mt hMin.mp hx
 have hh(t):P.axialCost U t=P.axialCost V t:=by
   unfold axialCost; rw [hu]; refine Finset.sum_congr rfl fun x _=>Finset.sum_congr rfl fun i _=>?_
   rw [he (x.val,i) (Finset.mem_union_left _ (Finset.mem_union_left _ x.prop))]
 have hz:P.facesum U=P.facesum V:=by
   unfold facesum; refine Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun p _=>?_
   split_ifs with h
   · unfold faceValue; apply congr_arg G.chord (travel_agree _ _ ?_)
     intro i hi; exact he i (Finset.mem_union_left _ <| Finset.mem_union_left _ <| h _ (List.mem_toFinset.mp hi))
   rfl
 simp only [Patch.frame,frameMass,hu,hx,hp,↓reduceIte,eligible,hh,hz,and_self]
private lemma connector_agree (K:KernelChoices)(h:P.Branches K G){U V:CoverConfig G}
    (he:∀ i:Edge Cover,i.1∈flights P → U i=V i)(l r:P.FrameTag)(i:Axis):
    Loops.coverY P K l r i U= Loops.coverY P K l r i V:=by
 have hv:∀ x∈arrival P,∀ a:Axis, U (x,a)=V (x,a) :=fun _ hx a=> he _ (Finset.mem_union_left _ hx)
 have hi {x: Cover}(hh:x∈(arrival P).image (· + hub P i) ∪ P.sites.biUnion fun x=> (visits x (spur P i)).toFinset) :x∈flights P:= Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hh⟩)
 have hL: P.frame K U l=P.frame K V l :=(frames_agree _ K h (by intro ⟨x,a⟩ hx; exact hv x hx a) l).1
 have hR:P.frame K (translate (hub P i) U) r=P.frame K (translate (hub P i) V) r:= (frames_agree _ K h (by intro ⟨x,a⟩ hx; exact he _ (hi (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)))) r).1
 unfold hub at hR; unfold Loops.coverY; rw [hL,hR]; funext z
 suffices T:travel U z.val (spur P i)=travel V z.val (spur P i) by unfold spur at T; rw [T]
 exact travel_agree _ _ fun e he' => he e (hi (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨z.val,z.prop,he'⟩)))

abbrev Mold := PlaqAxes ⊕ Option Axis
abbrev Leash:=P.FrameTag × P.FrameTag × P.Points
def temperatures (K:KernelChoices)(a:Mold)(l:Leash P)(U:CoverConfig G)(V:G.El): ℝ:=
    a.elim (fun p=>G.price (faceValue U ((0:Cover),p))) (fun z=>Option.casesOn z 0 (fun i=> K.penalty*G.price (V*(Loops.coverQ P K l.1 l.2.1 l.2.2 i U)⁻¹)))
def bands (K:KernelChoices)(a:Mold)(l:Leash P)(U:CoverConfig G)(_ : G.El):ℝ:=
    a.elim (fun _=> 1) (fun z=>Option.casesOn z (P.frameMass K U l.1) (fun i=> P.predictorMass K (Loops.coverY P K l.1 l.2.1 i U) l.2.2))
lemma prices_agree (K:KernelChoices)(h:P.Branches K G)(a:Mold)(l:Leash P)(U:CoverConfig G)(V:G.El):
    let X:=pretend P (limitTo P U V)
    temperatures P K a l X V=temperatures P K a l U V∧bands P K a l X V=bands P K a l U V:=by
 intro X
 have hX(i:Edge Cover)(he:i.1∈domain P): X i=U i:=pretend_agrees P U V i he
 rcases a with p|a
 · change G.price (faceValue X ((0:Cover),p)) = G.price (faceValue U ((0:Cover),p))∧1=(1:ℝ); refine ⟨congr_arg G.price (travel_agree _ _ ?_),rfl⟩
   intro i hh; exact hX i (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,Finset.mem_univ _,hh⟩)))
 cases a with
 | none=>
   change 0=(0:ℝ)∧P.frameMass K X l.1=P.frameMass K U l.1
   exact ⟨rfl,(frames_agree P K h (U:=X) (V:=U) (fun i hi=>hX i (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hi)))) l.1).2⟩
 | some i=>
   have hx:Loops.coverY P K l.1 l.2.1 i X=Loops.coverY P K l.1 l.2.1 i U:=connector_agree P K h (U:=X) (V:=U) (fun j hj=>hX j (Finset.mem_union_left _ (Finset.mem_union_left _ hj))) _ _ _
   change K.penalty*G.price (V*(P.predict K _ _)⁻¹)=_∧P.predictorMass K _ _=_
   rw [hx]; exact ⟨rfl,rfl⟩
end YM.AveragedStep
