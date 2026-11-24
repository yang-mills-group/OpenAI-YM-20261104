import YM.Qlocal.Payload

/-! Exact tally identities (not just protecting the written tickets). No support/flag/inventory
   cost using a regulator volume. Payload launch under **one** set of tested histories,
   conditional normalization only AFTER reliance on E/K estimates. Use on any positive price
   vector `c` measuring nonquiet labels (quiet entry required positive here harmless).
   No marking-degree/`F.rank` restriction. Bind common Caption span in other theorem.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Payload
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open Next.Foundations PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators
open Merge Switch UniformPays Publishing Emissions MergeProof Menu Accent Lotus
variable {Ω ι J V M : Type} [DecidableEq V] {R:Census V} {G:Gauge}{n:Side}{P: RG.Rep G n}
    {X:Support n}{o:V→Site n}{s:V→Support n}
    {u w:V→ℝ}{c:R.Mode→ℝ}{k k' : ℕ}{a b d δ C A B θ:ℝ}
-- expose Foot instance name
open scoped YM.Qlocal.Payload -- below fix

abbrev send (q:R.Mode) : ℂ→L[ℂ] Poly R:= {
  toFun := Poly.send q, map_add':= send_add q, map_smul':=fun _ _=> (sent ..).symm, cont:=Bands.sends q }

lemma ghost {f:ι→ℂ} {q:ι→R.Mode} (hp:Summable f) : Summable (fun i=> Poly.price (fun _=>1) (Poly.send (q i) (f i))) ∧ Summable (fun i=> Poly.send (q i) (f i)) := by
 have hv : Summable (fun i=> Poly.price (fun _=>1) (Poly.send (q i) (f i))):= hp.norm.congr fun i=>by rw [Poly.solo]; simp [Poly.toll]
 exact ⟨hv,(Poly.budgeted (fun v:V=>zero_lt_one) hv (fun i=>le_rfl)).1⟩
lemma shield {k:ι→J}{q:J→R.Mode}{f:ι→ℂ}(H:Summable f)(x:J) :
    Poly.send (q x) (cram k f x)=cram k (fun i=> Poly.send (q (k i)) (f i)) x:=by
 unfold cram; change (send _) _ = _; rw [ContinuousLinearMap.map_tsum _ (show Summable fun i:{i// k i=x}=>f i.val from H.comp_injective Subtype.val_injective)]; exact tsum_congr fun i=> by dsimp only; rw [i.prop]; rfl
lemma reported {k:ι→J}{q:J→R.Mode}{f:ι→ℂ}[Fintype J](H:Summable f):
    ∑ x, Poly.send (q x) (cram k f x)=∑' i, Poly.send (q (k i)) (f i):=by
 simp_rw [shield H]; exact (tsum_fintype ..|>.symm.trans (border k (p:=fun i=>Poly.send (q (k i)) (f i)) (ghost H).2|>.tsum_eq))

variable {dcl : Set (ℕ ×ℕ)} {Y:Taste Ω o P R} (hd : RetainsDeclared dcl Y s)
    (H:Peak P o Y c a A B) (ht:a=P.p.supportExponent)(hΩ:Ω)(hz:∀ i,0<c i) (Vw:Config G n)
set_option quotPrecheck false
local notation "TZ" => Town R s
local notation "KZ" => City R s
local notation "TK"=> valley hd H hΩ
local notation "TA"=> Y.menu

def citybox (i:KZ): Box n:= (i.val.1.support,i.val.1.inventory)
private def logExpense (x:Ω)(i:Town R s):= Poly.send i.val.2.val (snow hd H hΩ x i Vw)
private def flagExpense (x:Ω)(i:City R s): Poly R:=Poly.send i.val.2.val (stars hd H hΩ x i Vw)
local notation "Lb"=> logExpense hd H hΩ Vw
local notation "Lf"=> flagExpense hd H hΩ Vw
include H hd ht hz
lemma log_measured [Fintype V] (x:Ω): (Y.menu.terms x).extra Vw= ∑ i: Town R s, Poly.send i.val.2.val (snow hd H hΩ x i Vw):= by
 obtain ⟨f,hf,hF,hV,hT⟩:= light_funds hd H ht hΩ hz
 let g(i):= clipped Y x i Vw; have he:Summable g:=hf.of_norm_bounded (fun i=>hV x i Vw)
 unfold Overlay.Bands.extra; rw [Finset.sum_eq_zero (show ∀ i∈(univ:Finset V), _ from fun i _=>?_ ), zero_add]; swap; · change Poly.send _ (Y.menu.global x i)=_; rw [H.units,Poly.send_zero]
 exact (reported (J:=TZ) (k:=town hd H hΩ) (q:=fun i=>i.val.2.val) he).symm

variable (x:Ω)
def flagged (x:Ω)(j:ℕ ×ℕ):Poly R:= (Y.menu.terms x).tagged j.1 j.2 Vw
local notation "Sz"=> (fun i=> barcode P.activities (i:ℕ))
omit H hd ht hz
-- bundle one grouping within support D & another.Cart identity
lemma numbered {f:ι→Poly R}(hp:Summable f)(g:ι→J)(q:J→M)[Fintype J][DecidableEq M] (x : M) :
    cram (q ∘ g) f x = ∑ j:J, if q j=x then cram g f j else 0:=by
 let p:= {i:ι| q (g i)=x}; let y:=p.indicator f; have hy:Summable y:=hp.indicator p; have hv: cram (q ∘ g) f x=∑' i,y i:=by rw [MergeProof.expand_eq]; exact tsum_congr fun i=>by dsimp only [Function.comp_apply]; by_cases h:q (g i)=x; rw [if_pos h]; exact (Set.indicator_of_mem (show i∈p from h) _).symm; rw [if_neg h]; exact (Set.indicator_of_notMem (show i∉p from h) _).symm
 rw [hv,← (border g hy).tsum_eq, tsum_fintype]
 refine sum_congr rfl fun i _=> ?_; change cram g y i= _; by_cases h:q i=x; swap
 · rw [if_neg h]; apply (tsum_congr ?_).trans tsum_zero; intro j; exact Set.indicator_of_notMem (show j.val∉p from (by change ¬q (g j.val)= x; rw [j.prop]; exact h)) _
 rw [if_pos h]; exact tsum_congr fun j=>Set.indicator_of_mem (show j.val∈p from (by change q (g j.val)=x; rw [j.prop,h])) _
lemma crane {f:ι→Poly R}{g:ι→ℕ} [DecidableEq J] (q:ℕ→J)(j:J)(hp:Summable f) :
    cram (q ∘ g) f j = cram q (cram g f) j:=by -- no finiteness
 let p:= {i:ι| q (g i)=j}; let y:=p.indicator f; have hy:Summable y:=hp.indicator p;
 have hv: cram (q ∘ g) f j=∑' i,y i:=by rw [MergeProof.expand_eq]; exact tsum_congr fun i=>by dsimp only [Function.comp_apply]; by_cases h:q (g i)=j; rw [if_pos h]; exact (Set.indicator_of_mem (show i∈p from h) _).symm; rw [if_neg h]; exact (Set.indicator_of_notMem (show i∉p from h) _).symm
 rw [hv,← (border g hy).tsum_eq,MergeProof.expand_eq]; refine tsum_congr (fun i=>?_); change cram g y i= _; by_cases h:q i=j; swap
 · rw [if_neg h]; apply (tsum_congr ?_).trans tsum_zero; intro k; exact Set.indicator_of_notMem (show k.val∉p from (by change ¬q (g k.val)= j; rw [k.prop]; exact h)) _
 rw [if_pos h]; exact tsum_congr fun k=>Set.indicator_of_mem (show k.val∈p from (by change q (g k.val)=j; rw [k.prop,h])) _
lemma declared_cram (j:Box n)(F:ℕ ×ℕ→Poly R) (h:∀ i,i∉dcl→ F i=0):
     cram (fun i:dcl=>barcode P.activities i.val.1) (F ∘ Subtype.val) j=
       cram (Sz ∘ Prod.fst) F j:=by
 rw [MergeProof.expand_eq,MergeProof.expand_eq]; let p i:= if (Sz ∘ Prod.fst) i=j then F i else 0; apply (show (∑' i:dcl,p i.val)= _ from tsum_subtype_eq_of_support_subset ?_); intro i hi; by_contra hp; exact hi (show p i=0 from by unfold p; split; exact h i hp;rfl)
lemma cram_fst{ι κ:Type} (F:ι × κ→Poly R)(x:ι): cram Prod.fst F x=∑' j:κ,F (x,j):= by
   let e : κ ≃ {p:ι × κ// p.1=x}:= {
      toFun:=fun j=>⟨(x,j),rfl⟩, invFun:=fun p=>p.val.2
      left_inv:=fun _=>rfl
      right_inv:=fun p=>Subtype.ext (Prod.ext p.prop.symm rfl)}
   exact (e.tsum_eq (fun p=> F p.val)).symm

include hd
lemma flagged_padding (i:ℕ ×ℕ)(he:i∉dcl): flagged (Y:=Y) Vw x i=0:=by
 unfold flagged Overlay.Bands.tagged; change Poly.send _ (Y.menu.force x _ _ _)=0; rw [hd.padding i.1 i.2 he,Pi.zero_apply,Poly.send_zero]

include hΩ ht H hz
local notation "Lf"=> flagExpense hd H hΩ Vw
lemma flag_measured (i : Box n):
    cram (fun i:ℕ ×ℕ=>barcode P.activities i.1) (flagged (Y:=Y) Vw x) i=
        ∑ j: City R s, if citybox j=i then Poly.send j.val.2.val (stars hd H hΩ x j Vw) else 0:=by
 obtain ⟨f,hf,hF,hT,H⟩:= dark_funds H ht hz
 let a i:=Y.menu.force x (i:dcl).val.1 i.val.2 Vw; have he:Summable a:= (hf.comp_injective (i:=Subtype.val (p:=dcl)) Subtype.val_injective).of_norm_bounded (fun i=> hT x i.val Vw)
 rw [show (fun i:ℕ ×ℕ=>barcode P.activities i.1)= barcode P.activities ∘ Prod.fst from rfl,← declared_cram _ _ (flagged_padding hd Vw x)]
 have h(i) : (flagged (Y:=Y) Vw x ∘ Subtype.val (p:= dcl)) i=Poly.send (TK i|>.val.2.val) (a i):=rfl
 change cram (citybox ∘ TK) (fun i'=>Poly.send (TK i'|>.val.2.val) (a i')) i= _; rw [numbered (ghost he).2 (TK)]; apply sum_congr rfl; intro i ht; split; exact (shield he (k:=TK) (q:=fun i=>i.val.2.val) i).symm; rfl

-- strip vacuum once at each slot; gathering identity.
variable (hP:P.activities.Valid P.p b d)
include hP
omit hd hΩ in
lemma pocket (w:V→ℝ)(hw:∀ i,0<w i) : Summable (fun i=>Poly.price w ((Y.menu.terms x).each i Vw)) ∧
  ∀ i:Box n, cram Sz (fun i=>(Y.menu.terms x).each i Vw) i=bar P.activities R Vw i+cram (fun i:ℕ ×ℕ=>barcode P.activities i.fst) (flagged (Y:=Y) Vw x) i := by
 obtain ⟨f,hf,hF,hB,hS⟩:= dark_funds H ht hz; let g(i):=P.activities.K i Vw; have hg:Summable g:= mass_crest _ hP Vw;
 let G' i:=Poly.send R.quiet (g i); have hG: Summable (fun i=>Poly.price w (G' i)):= hg.norm.congr (fun i=>by simp only [G',Poly.solo,Poly.quiet_toll,one_mul,Complex.norm_real]);
 let μ:= flagged (Y:=Y) Vw x; let M(i):=∑' j:ℕ,μ (i,j); let T := fun (i:ℕ ×ℕ)=> Y.menu.force x i.1 i.2 Vw; have hb:Summable T:= hf.of_norm_bounded fun i => hB x i Vw; let v i :=Poly.price w (μ i)
 obtain ⟨t₀,hx',hy⟩:= Finset.exists_max_image univ (Poly.toll w (R:=R)) ⟨R.quiet, mem_univ _⟩; let v':= Poly.toll w t₀
 have hv (i:ℕ×ℕ): 0 ≤ v i:= Poly.nonnegative hw _; have hx : Summable v:= (hf.mul_left v').of_nonneg_of_le hv (fun i=>?_) ; rotate_left -- beware have ordering
 · unfold v μ flagged Overlay.Bands.tagged; rw [Poly.solo]; exact mul_le_mul (hy _ (mem_univ _)) (hB x i Vw) (norm_nonneg _) (Poly.worth hw _|>.le)
 refine ⟨?_,fun i=>?_⟩
 · let m(i):=∑' j,v (i,j); obtain ⟨hp,hk⟩:= (summable_prod_of_nonneg hv).1 hx; let g i:= (Y.menu.terms x).each i Vw
   exact (hG.add hk).of_nonneg_of_le (fun i=>Poly.nonnegative hw _) (fun i=>(Poly.addition hw _ _).trans (add_le_add le_rfl ((Poly.budgeted hw (hp i) (fun j=>le_rfl)).2)))
 have hP':Summable μ:= (Poly.budgeted hw hx (fun i=>le_rfl)).1; have hM:cram Prod.fst μ=M:= funext fun x=> cram_fst (F:=μ) x; have hm:Summable M:= hM ▸ (border Prod.fst hP').summable
 rw [show (fun i:ℕ ×ℕ=>barcode P.activities i.fst)= Sz ∘ Prod.fst from rfl, crane (g:=Prod.fst) _ i hP']; unfold Overlay.Bands.each; change cram Sz (fun i=>G' i+M i) i= bar _ _ _ _ + _; rw [show cram _ _ _= _ from (?_:cram Sz (fun i=>G' i+M i) i = cram Sz G' i + cram Sz M i)]; rw [hM]; congr 1; apply Marker.Poly.ext; intro q; unfold cram; rw [Poly.share (f:=fun k:{k//Sz k=i}=>G' k.val) ((Poly.budgeted hw hG (fun i=>le_rfl)|>.1).comp_injective Subtype.val_injective)]; by_cases h:q=R.quiet <;> simp [G',g, h,bar,profile,Poly.bead,cram] -- coe simp
 unfold cram; exact Summable.tsum_add ((Poly.budgeted hw hG (fun i=>le_rfl)|>.1).comp_injective Subtype.val_injective) (hm.comp_injective Subtype.val_injective)



end YM.Qlocal.Payload
