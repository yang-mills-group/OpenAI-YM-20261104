import YM.MergeProof.North.Harvest
/-! Name equivalences permit transport of the penultimate `Served` to the
identifier type of tile copies, where the subsequent lemma from the accepted proof
(Merman.bequeathed) expects to consume it. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Bouquet.Relabel
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V I W : Type}[Fintype V][DecidableEq V][Fintype W][DecidableEq W]{G:Gauge}{n:Side}
local notation "Ξ" => Ribbon.Bud V
local notation "Ω" => Ribbon.Bud W
variable (e : V≃W)
def mode : (Ribbon.Bud V).Mode≃(Ribbon.Bud W).Mode where
    toFun p:=⟨p.val.image e,mem_univ _⟩
    invFun p:=⟨p.val.image e.symm,mem_univ _⟩
    left_inv p:=Subtype.ext (by simp [image_image])
    right_inv p:=Subtype.ext (by simp [image_image])
def walk (e : V ≃ W) : Poly Ξ →L[ℂ] Poly Ω:= LinearMap.toContinuousLinearMap ({
    toFun:=fun p=>Poly.inject fun j=>p.part ((mode e).symm j)
    map_add' := fun _ _=>by ext1; rfl
    map_smul' := fun _ _=>by ext1; rfl} : Poly Ξ→ₗ[ℂ]Poly Ω)
lemma part (p:Poly Ξ)(i:(Ribbon.Bud V).Mode):(walk e p).part (mode e i)=p.part i:=by change p.part ((mode e).symm ((mode e) i))=_; rw [Equiv.symm_apply_apply]
lemma send (p:(Ribbon.Bud V).Mode)(b:ℂ): walk e (Poly.send p b)=Poly.send (mode e p) b:=by
    ext q; obtain ⟨q,rfl⟩:=(mode e).surjective q; rw [part,Poly.part_send,Poly.part_send]; simp only [Equiv.apply_eq_iff_eq]
lemma quiet : mode e (Ξ).quiet = (Ω).quiet:=Subtype.ext (by change image _ ∅=∅; rw [image_empty])
lemma single (i:V) : mode e ((Ξ).fire i)=((Ω).fire (e i)):=Subtype.ext (image_singleton ..)
lemma mul (a b:Poly Ξ): walk e (a*b)=walk e a*walk e b:=by
    ext p; obtain ⟨p,rfl⟩:= (mode e).surjective p; rw [part,Poly.part_mul,Poly.part_mul,← Equiv.sum_comp (mode e)]; refine sum_congr rfl fun i _=> ?_; rw [← Equiv.sum_comp (mode e)]; refine sum_congr rfl fun j _=> ?_
    have hv : Poly.merges (mode e i) (mode e j) (mode e p) ↔ Poly.merges i j p:=by
      change Disjoint (i.val.image e) (j.val.image e) ∧ i.val.image e∪j.val.image e=p.val.image e ↔ _; rw [← image_union, Finset.disjoint_image e.injective]; exact and_congr Iff.rfl ((Finset.image_injective e.injective).eq_iff)
    simp only [hv,part]
@[simp] lemma one : walk e 1=1:=by
    ext p; obtain ⟨p,rfl⟩:= (mode e).surjective p; rw [part,Poly.one_part,Poly.one_part, ← quiet e]; simp only [Equiv.apply_eq_iff_eq]
lemma pow (p:Poly Ξ)(i:ℕ) : walk e (p^i)=(walk e p)^i:=by
    induction i with
    | zero=> simp
    | succ i h=> rw [pow_succ,pow_succ,mul,h]
lemma pass (p:Poly Ξ): walk e (Poly.pass p)=Poly.pass (walk e p):=by unfold Poly.pass; rw [Fintype.card_congr e,map_sum]; simp [pow]
lemma mach (u : V→ℂ) : walk e (Mach Ξ u)= Mach Ω (u ∘ e.symm):=by unfold Mach; rw [map_sum,← Equiv.sum_comp e]; simp [send,single]
lemma restore' (H:Support n→ Config G n→ Poly Ξ )  (K:Box n→ Config G n→ Poly Ξ ) (R:Rep G n)(f:V→ Config G n→ℂ)(ω:V→Res G n)(U:Config G n):
    walk e (restore R f ω H K U)=restore R (f ∘ e.symm) (ω ∘ e.symm) (fun i=> walk e ∘ H i) (fun i=>walk e ∘ K i) U:=by
    unfold restore; rw [map_smul,mul,pass,map_add,map_sum,mach]; refine congr_arg _ (congr_arg₂ (·*·) rfl ?_); unfold field; rw [map_sum]; refine sum_congr rfl fun i _=> ?_; unfold grid; split
    · have hp (J:Box n→Poly Ξ):∀ i : Finset (Box n), walk e (∏ j∈i,J j)=∏ j∈i,walk e (J j):=by
         intro i; induction i using Finset.induction with
         | empty => simp
         | insert j s he ih=> rw [prod_insert he,prod_insert he,mul,ih]
      rw [hp]; refine prod_congr rfl fun i _=> ?_; rw [map_add,map_add,mach]; unfold bar; have hc (b:ℂ) : walk e (Poly.bead (Ξ) b)=Poly.bead (Ω) b:=by change walk e (Poly.send (Ξ).quiet b)= _; rw [send,quiet]; rfl
      rw [hc]; rfl
    exact map_zero _
lemma toll (i:(Ribbon.Bud V).Mode)(w:V→ℝ):Poly.toll (w ∘ e.symm) (mode e i)= Poly.toll w i:=by unfold Poly.toll; change (∏ j∈i.val.image e,(w∘e.symm) j)=_; rw [prod_image e.injective.injOn];simp
private lemma towed {f:I→Support n}{w:V→ℝ}{b:ℕ}{α C:ℝ}{F:I→ Config G n→Poly Ξ}(h:Towed w f F b α C): Towed (w ∘ e.symm) f (fun i=> walk e ∘ F i) b α C:=by
    obtain ⟨v,hv,hV,h⟩:=h; refine ⟨v,hv,hV,fun i=> ?_⟩; obtain ⟨L,hL,hQ,h⟩:=h i; refine ⟨L ∘ (mode e).symm, fun j=> hL _,fun U j=>?_, ?_⟩
    · obtain ⟨j,rfl⟩:= (mode e).surjective j; simpa [part] using hQ U j
    refine le_trans (le_of_eq ?_) h; unfold GridApprox.Nil.wordsPrice; rw [← Equiv.sum_comp (mode e)]; simp only [toll,comp_apply,Equiv.symm_apply_apply]
-- transport Carton components
private lemma rises' {x:Poly Ξ}(h:rises x): rises (walk e x):=by
    intro i H; obtain ⟨i,rfl⟩:= (mode e).surjective i; rw [part] at H; change 2 ≤ (i.val.image e).card; rw [card_image_of_injective _ e.injective]; exact h i H
private lemma borned {o:V→Site n}{x: Support n}{f:Config G n→Poly Ξ}{t:ℝ}(h:Borne o x f t): Borne (o ∘ e.symm) x (walk e ∘ f) t:=by
    refine ⟨fun U W hU hW=> congr_arg (walk e) (h.home U W hU hW),fun i U=>congr_arg (walk e) (h.turns i U),fun i=>?_,fun U i hi=>?_⟩
    · obtain ⟨i,rfl⟩:= (mode e).surjective i; simpa only [Function.comp_apply,part] using (h.me i)
    obtain ⟨i,rfl⟩:= (mode e).surjective i; rw [Function.comp_apply,part]; apply h.scope U i; intro hp; apply hi; intro j hj; obtain ⟨j,hj',rfl⟩:= mem_image.mp hj; change o (e.symm (e j))∈ x; rw [Equiv.symm_apply_apply]; exact hp hj'
lemma moved {R:Rep G n}{f: V→ Config G n→ℂ}{ω: V→ Res G n}{Y:Config G n→Poly Ξ}{o:V→Site n}{w:V→ℝ}{b t:ℝ}(h:Served R f ω Y o w b t): Served R (f ∘ e.symm) (ω ∘ e.symm) (walk e ∘ Y) (o ∘ e.symm) (w ∘ e.symm) b t:=by
    obtain ⟨H,K,hA,hB,hC,rfl⟩:=h; refine ⟨_,_,⟨fun i=>⟨?_,fun _=>rises' e ((hA.exp i).2 _)⟩,fun i=>⟨?_,fun _=>rises' e ((hA.flag i).2 _)⟩ ⟩,towed e hB,towed e hC,funext (fun U=>restore' e H K R f ω U)⟩
    · refine ⟨borned e (hA.exp i|>.1.toBorne),fun U h=> (hA.exp i).1.permits U (fun he=> h ?_),fun U=> ?_⟩
      · change walk e (H i U)=_; rw [he,map_zero]
      rw [← quiet e,part]; exact (hA.exp i).1.sil U
    refine ⟨borned e (hA.flag i|>.1.toBorne),fun U h=> (hA.flag i).1.permits U (fun he=> h ?_)⟩; change walk e (K i U)=_; rw [he,map_zero]
end YM.MergeProof.Bouquet.Relabel
