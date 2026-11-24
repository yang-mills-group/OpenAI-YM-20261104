import YM.SignedWilsonExpansion.F9.Glimpse
import YM.SignedWilsonExpansion.F9.Canvas
import YM.SignedWilsonExpansion.F9.Stair
/-!
# Rank palate at the epoch top

For each real pure grade label form its **true** image under top stencil
projection & add the price of an equation pillar. Locally symmetric basis
maps via explicit orbit averaging come next. Included at own h, not any
claim that higher-horizon arithmetic or comparison stencils descend!
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge Matrix
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost FVA2
open Pill Cloth
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ENNReal
variable {G:Gauge}{H:Hol G}{h i j k m r d n e:ℕ}{F:Frame G h}{x: Label G h}
section projection
open Maxwell
abbrev Lamp (G:Gauge)(h:ℕ):= shellSector G h
def bulb (G:Gauge)(h:ℕ): Label G h →ₗ[ℂ] Lamp G h:= (observable G h).rangeRestrict
def projector (G:Gauge)(h:ℕ): Module.End ℂ (Label G h):= XSpace.On.sectionMap h ∘ₗ bulb G h
lemma bulb_recovers (G:Gauge)(h:ℕ)(x:Lamp G h): bulb G h (XSpace.On.sectionMap h x)= x:= Subtype.ext (XSpace.On.recovers _)
lemma projection0 (x:Label G h): bulb G h (projector G h x)=bulb G h x:= bulb_recovers ..
lemma eraseV (x:Label G h): x-projector G h x∈ equationIdeal G h:= by change _-_ ∈ _; rw [equationIdeal, LinearMap.mem_ker,map_sub, sub_eq_zero]; exact (congr_arg Subtype.val (projection0 x)).symm
lemma fixed_color (x:Label G h)(v:realBar x=x): realBar (projector G h x)=projector G h x:=by
    apply Eq.symm; apply XSpace.On.section_real; exact Press.lower_real x.val (congr_arg Subtype.val v)
lemma channel (p:x∈Grade (n,r)) : MvPolynomial.IsWeightedHomogeneous Maxwell.Free.bwt ((bulb G h x).val) (n,r):=
    Press.re_grade x.val ((pure_grade ..).mp p)
lemma projector_grade (p:x∈Grade (n,r)): projector G h x∈Grade (n,r):= XSpace.On.section_grade _ (channel p)
-- certify visible coefficient consumes unit as itself
lemma cap_beam (p:x∈Grade (n,0)): projector G h x=x:=by
    obtain ⟨c,rfl⟩:=Labels.scalar_grade _ p; rw [map_smul]; congr 1; exact Subtype.ext (show XSpace.On.lifting (Maxwell.reduceEq (1:_))=(1:Labels.Pol G) from Eq.trans (congr_arg _ (map_one _)) (map_one _)) -- fix type
end projection
section paper
variable (A:XSpace.Survey G H h) (S:Rays G h H)
local notation "T" => (Fin (h+1))
def pigment (p:x∈Grade (h,r))(i:T)(j:Fin r) := curlP A _ (gradePart_mem (i.val,j.val) (Press.diff A x)) -- p unused need Lean include binder explicit
lemma rebate (p:x∈Grade (h,r))(e:r≤h): A.insertW (-1) x-x= ∑ i:T, ∑ j:Fin r, gradePart (i.val,j.val) (Press.diff A x):=by
    let V:= A.insertW (-1) x-x; let f i j:= gradePart (i,j) V; change V= ∑ i:T, ∑ j:Fin r,f i.val j.val; simp_rw [Fin.sum_univ_eq_sum_range]; rw [Fin.sum_univ_eq_sum_range (fun i=>∑ j∈Finset.range r,f i j)]; refine (decompose V|>.symm).trans (Finset.sum_congr rfl (fun i _=> ?_)); apply Eq.symm; exact Finset.sum_subset (Finset.range_mono (by omega)) (fun j _ hj=> Press.upper_empty A p _ j (by simpa using hj))
lemma color_pigment (p:realBar x=x)(y z:ℕ) : realBar (gradePart (y,z) (Press.diff A x))= gradePart (y,z) (Press.diff A x):=by
    rw [←gradePart_bar,Press.diff,map_sub,← A.wick_real,p]
-- Badge at weight h.
def permitT (p:x∈Grade (h,r)) : Cloth G r:= overC (k:=r) (curlP A x p) le_rfl 0+ ∑ i:T,∑ j:Fin r, overC (pigment A p i j) j.isLt.le 0
lemma paysP {v:realBar x=x}(p:x∈Grade (h,r))(i:TagIx F r): row F ((photo (permitT A p)).2 0 r) i= if wT F i=h then ((F.coords x) i).re else 0 :=by
    let P(a:T)(j:Fin r):= (overC (pigment A p a j) j.isLt.le 0 : Cloth G r); let V:T→ Era G ℝ:=fun i=>∑ j:Fin r,(pigment A p i j).letter
    have hx (a:T)(j:Fin r) : photo (P a j)=(pigment A p a j).letter:= overD ..
    have hb : (∑ i:T,∑ j:Fin r,P i j).photo=∑ i:T,V i := by unfold photo V; simp_rw [map_sum]; exact Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=> hx i j
    have he (i:T)(j:Fin r) : ((pigment A p i j).letter.2 0 r)=0:= (pigment A p i j).solid.coverN _ _ (by change j.val+0<_; omega)
    have hh (i:T): (V i).2 0 r=0:=by unfold V; simp only [Prod.snd_sum,Finset.sum_apply,he,Finset.sum_const_zero]; -- all
    rw [permitT,plus_map,axPlus (receipt _) (receipt _), overD, primary_curl _ _ p v]; change _+ row F ((photo (∑ a:T, ∑ j:Fin r,P a j)).2 0 r) i= _; rw [hb]; simp only [Prod.snd_sum, Finset.sum_apply, hh,Finset.sum_const_zero,row_nil,add_zero]
-- positive rank Ward
abbrev hedge (p:x∈ Grade (h,r+1)): Cloth G (r+1):= overC (k:=r+1) (holder S _ (tensor_eqv p)) le_rfl 0 - overC (sink S _ (tensor_eqv p)) (by change r-1≤ r+1; omega) (shadeShift r)
lemma hedge_budget (p:x∈Grade (h,r+1)): photo (hedge S p)=award S _ (tensor_eqv p):=by unfold photo hedge; rw [map_sub]; change photo _ -photo _= _; rw [overD,sees_over]; rfl
def pricedT (r:ℕ)(x:Label G h): (p:x∈Grade (h,r))→ Cloth G r:= match r with
    | 0=> fun p=> permitT A p
    | r+1=> fun p=> permitT A (projector_grade p)+hedge S (Submodule.sub_mem _ p (projector_grade p))
lemma payingP (r:ℕ)(p:x∈Grade (h,r))(u:realBar x=x)(i:TagIx F r): row F ((photo (pricedT A S r x p)).2 0 r) i= if wT F i=h then ((F.coords x) i).re else 0:=by
    cases r; · exact paysP A p i (v:=u)
    rename_i r
    let V:= projector G h x; let P:=permitT A (projector_grade p); have ht: realBar V=V:= fixed_color _ u
    unfold pricedT; rw [plus_map,axPlus (receipt _) (receipt _),paysP A _ _ (v:=ht),hedge_budget,primary_award S _ (by rw [map_sub,ht,u]) (Submodule.sub_mem _ p (projector_grade p)) (eraseV _) _ (F.bound i.val)]
    split_ifs; · simp only [map_sub, Pi.sub_apply, Complex.sub_re]; abel
    simp
end paper
section ballot
variable {L:Frames G}{A:∀ h, XSpace.Survey G H h}{R:∀ h, Rays G h H}

def blade (i:F.Index) (h':wt F i=h): (F.basis i)∈Grade (h,wr F i):=by rw [← show F.grades i=(h,wr F i) from Prod.ext h' rfl]; exact F.pure i
-- keeps rank within W.
def elder (A:∀ h, XSpace.Survey G H h)(R:∀ h, Rays G h H)(L:Frames G)(i:(L.level h).Index): Cloth G (wr (L.level h) i):=by
    let d:= wt (L.level h) i; have he:= (L.level h).bound i; let x:=downL L he i (le_refl d); have ht:= down_grade L he i (le_refl d); have hw: (L.level d).basis x ∈ Grade (d,wr (L.level h) i):= by rw [← show _ =(d,wr (L.level h) i) from (show (L.level d).grades x= _ from ht)]; exact (L.level d).pure x
    exact pricedT (A d) (R d) _ _ hw
lemma rung (i j:TagIx (L.level h) r)(p:wT (L.level h) i≤ wT (L.level h) j): row (L.level h) ((photo (elder A R L j.val)).2 0 r) i= if i=j then 1 else 0:=by
    let x:=i.val; let y:=j.val; let d:= wt (L.level h) y; let hw:= (L.level h).bound y
    let q:=downT L hw j (le_refl d); let v:=downT L hw i p; let T:=(L.level d); let F:=(L.level h); set P':=elder A R L j.val
    have hy : T.basis q.val ∈ Grade (d,wr F j.val):= by rw [← show T.grades q.val=(d,wr F j.val) from down_grade L hw y (le_refl d)]; exact T.pure q.val
    have hζ : wr F j.val=r:= j.property
    have hz:P'=pricedT (A d) (R d) _ _ hy:=rfl
    have he := row_handed H L (receipt P') (e:=0) v hw
    rw [up_downT] at he
    have hp : ∀ l:ℕ, l=wr F j.val → ∀ v':TagIx T l,∀ H': T.basis q.val ∈ Grade (d,l), row T ((photo (pricedT (A d) (R d) _ _ H')).2 0 r) v= row T ((photo P').2 0 r) v := by
       intro l e' _ H'; subst l; rw [hz]
    have ht:T.basis q.val∈ Grade (d,r):= Eq.mp (congr_arg (fun r:ℕ=> T.basis q.val∈Grade (d,r)) hζ) hy
    rw [←he, ← hp r hζ.symm v ht,payingP _ _ _ _ (T.realForm q.val) v,Frame.coords_basis]; by_cases H:i=j
    · have HH:v=q:= upT_faith L _ _ _ ((up_downT L hw i p).trans (H.trans (up_downT L hw j (le_refl d)).symm))
      rw [HH,Pi.single_eq_same,if_pos H,if_pos (show wT T q=d from congr_arg Prod.fst (down_grade L hw y (le_refl d)))]; rfl
    have HH:v.val≠q.val:=fun h=> H ((up_downT L hw i p).symm.trans ((congr_arg (upT L hw) (Subtype.ext h)).trans (up_downT ..)))
    rw [if_neg H, Pi.single_eq_of_ne HH]; split_ifs <;> rfl
end ballot
end YM.WilsonCoeffUV.Mer.Xa
