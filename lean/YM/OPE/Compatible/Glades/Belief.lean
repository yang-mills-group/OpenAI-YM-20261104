import YM.OPE.Compatible.Glades.Loop
/-!
# Tree finishes. Product bill on the surviving Marked column

Use directly also after one signed resolution inside: no more root
expectation contractions across unrelated sibling seams are needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.CutOrder
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi Finset
open scoped Topology Classical
variable {X V:Type}[PartialOrder X][OrderBot X][Fintype X]
    (D:Origin X) {U Q:Finset X}{m j:X→ℕ}
open YM.OPE.Allot Series Lights
variable {G:Gauge}{C:Family G} (A:Allot C){P: Ensemble V}{l:ℕ→ℕ}
variable {N p b n:ℕ} {E:Track C.path V p}{o:X→Track C.path V p}
variable (h:CutOrder C P D U m j N p E o b l)(S:Series Q m)(hU:Q⊆U)
variable [Fintype V][DecidableEq V]
-- single by carrying finite set addresses
variable (f: V×(brim D Q)→ Config G (C.side N p)→ℂ)
variable (ht: ∀ x∈brim D Q,n ≤ roof U m N x) (hn:n ≤ N) (hp:whenHigh Q m < n)(hF: Integrable (birth (Names V ↥(brim D Q)) (C.path.rep N p N) f) (prior G _))
variable (L : Lights A P N p (fun x:brim D Q=>finishAt D m x.val) n b E (fun x=>o x.val))
def parcel {I:Type}[Fintype I](f:V×I→ Config G (C.side N p)→ℂ)(v:V)(y:Config G (C.side N p)) := ∏ i,f (v,i) y
-- also addresses any β Branch component
structure Head (x:Finset X) (A:Allot C)(P:Ensemble V)(j N p b:ℕ)(E o:Track C.path V p)(f:V→ Config G (C.side N p)→ℂ)(a:ℝ) (hN:j ≤ N) : Prop where
    ready : ∃ L:Lights A P N p (fun _:x=> j) j b E (fun _:x=>o), L.LitUp (full V _) (gust C.path N p N (birth (Names V ↥x) (C.path.rep N p N) (fun i=>f i.1)) j hN) ∧ a ≤ ∏ i,L.bottom i ∧ ∀ i:x,Blade (C.path.rep N p j) ((L.tips i).home P.v) ((L.tips i).oil P.v) (profile (C.path.rep N p j).activities ((L.tips i).gas P.v)) 0 (4*(1/L.asks i))
-- generic recut label
section
variable {K T:Finset X} {x₀:X} {j':ℕ}{a:ℝ}
variable {A}
private lemma bridge {Q:Lights A P N p (fun u:K=>finishAt D m u.val) n b E (fun x=>o x.val)} (f: V×K→ Config G (C.side N p)→ℂ){hn}
   (ht: LitUp Q (full V _) (gust C.path N p N (birth (Names V ↥K) (C.path.rep N p N) f) n hn)) (hv:K=T)(hz:a ≤ ∏ i,Q.bottom i)(hp:Integrable (birth (Names V ↥K) (C.path.rep N p N) f) (prior G _)):
   ∃ g:V×T→ Config G (C.side N p)→ℂ,parcel (C:=C) (N:=N) (p:=p) g= parcel (C:=C) f ∧ Integrable (birth (Names V ↥T) (C.path.rep N p N) g) (prior G _) ∧ ∃ L:Lights A P N p (fun u:T=>finishAt D m u.val) n b E (fun x=>o x.val),
     LitUp L (full V _) (gust C.path N p N (birth (Names V ↥T) (C.path.rep N p N) g) n hn) ∧ a ≤ ∏ i,L.bottom i:=by
    subst T; exact ⟨f,rfl,hp,Q,ht,hz⟩
private lemma lastpost {Q:Lights A P N p (fun u:K=>finishAt D m u.val) n b E (fun x=>o x.val)} (f: V×K→ Config G (C.side N p)→ℂ){hn : n ≤ N}
   (ht: LitUp Q (full V _) (gust C.path N p N (birth (Names V ↥K) (C.path.rep N p N) f) n hn)) (hv:K={⊥})(he:m ⊥=n)(hz:a ≤ ∏ i,Q.bottom i)
   (hQ:∀ i:K,Blade (C.path.rep N p n) ((Q.tips i).home P.v) ((Q.tips i).oil P.v) (profile (C.path.rep N p n).activities ((Q.tips i).gas P.v)) 0 (4*(1/Q.asks i))) : Head ({⊥}:Finset X) A P (m ⊥) N p b E (o ⊥) (parcel (C:=C) (N:=N) (p:=p) f) a (he ▸ hn):=by
   subst K n; let x:Finset X:={⊥}; haveI hu : Subsingleton ↥x := by dsimp [x]; infer_instance -- x type ascription
   have hF : f=fun t=>parcel (C:=C) (N:=N) (p:=p) f t.1:=by
      funext ⟨v,i⟩; symm; funext U; unfold parcel; apply Finset.prod_eq_single i; intro b _ he; exact False.elim (he (hu.allEq _ _)); intro he; exact False.elim (he (mem_univ _)) --
   have hq: (fun u:({⊥}:Finset X)=>finishAt D m u.val)=(fun _=>m ⊥):=funext fun u=> by rw [show u.val=⊥ from Finset.mem_singleton.mp u.2,deck]
   have hx:(fun u:({⊥}:Finset X) => o u.val)=(fun _=>o ⊥):= funext fun u=> congr_arg o (Finset.mem_singleton.mp u.2)
   suffices h : ∃ L:Lights A P N p (fun u:({⊥}:Finset X)=>finishAt D m u.val) (m ⊥) b E (fun x=>o x.val), L.LitUp (full V _) (gust C.path N p N (birth (Names V ↥({⊥}:Finset X)) (C.path.rep N p N) (fun i=>parcel (C:=C) (N:=N) (p:=p) f i.1)) (m ⊥) hn) ∧ a ≤ ∏ i,L.bottom i∧ ∀ i,Blade (C.path.rep N p (m ⊥)) ((L.tips i).home P.v) ((L.tips i).oil P.v) (profile (C.path.rep N p (m ⊥)).activities ((L.tips i).gas P.v)) 0 (4*(1/L.asks i)) by rw [hq,hx] at h; exact ⟨h⟩
   exact ⟨Q, hF ▸ ht,hz,hQ⟩
end
variable {a:ℝ} (hz:Expenses C D U m j l b a)(hr:G.Simple)(hC:C.Makes) (hA:∀ i,m ⊥ ≤ i→ places X≤ A.r i)
include hU S h ht hp hF hz hr hC hA
lemma windfall (hY: LitUp L (full V _) (gust C.path N p N (birth (Names V ↥(brim D Q)) (C.path.rep N p N) f) n hn)) : Head ({⊥}:Finset X) A P (m ⊥) N p b E (o ⊥) (parcel (C:=C) (N:=N) (p:=p) f) (a^(Q.card*(places X+places X))*∏ i,L.bottom i) (((high D S S.base.base).trans hp.le).trans hn):=by
   -- sub-recursive roll
   have hz₀:∀ {Q:Finset X}(s:Series Q m)(n:ℕ),whenHigh Q m < n → m ⊥ < n:=fun s n hv=> lt_of_le_of_lt (high D s s.base.base) hv
   induction Q using Finset.strongInductionOn generalizing n
   rename_i Q ih
   let J:= crease D S; let x:= whenHigh Q m
   let f':=relayTo D (C:=C) (N:=N) (p:=p) S f; let r:= parcel (C:=C) (N:=N) (p:=p) f
   have he:parcel (C:=C) (N:=N) (p:=p) f'=r:=funext fun i=> funext fun k=> (all_prod (attaches D S) (fun x=> f (i,x) k)).symm
   obtain ⟨hx,X',hM,hB,hp'⟩:= roll D A h S hU f ht hn hp hF L hr hC hA hY hz
   let χ:= places X + places X; have hy : 0 ≤ ∏ i,L.bottom i:= Finset.prod_nonneg fun i _=>(L.bottom_pos _).le
   by_cases hw:(bed Q m).Nonempty
   · let P':= bed Q m; have hyK:after D Q m=brim D P':= if_pos hw
     have hh x' (hp':x'∈brim D P'): x ≤ roof U m N x':= kids_at D S hU (fun i hi=> hp.le.trans (ht i hi)) ⟨x',hyK.symm ▸ hp'⟩
     obtain ⟨g,hg,hI,Q',hJ,hW⟩:= bridge D f' hM hyK hp' hx
     obtain ⟨Vt,hVt,hP,hX⟩:= (ih P' (S.dropped) (frame S hw) (S.dropped.subset.trans hU) g hh (hp.le.trans hn) (low_bed D S hw) hI Q' hJ).ready -- args inspect
     have hfg:=hg.trans he; change Head _ _ _ _ _ _ _ _ _ r _ _; rw [← hfg]; refine ⟨Vt,hVt,?_,hX⟩
     refine le_trans ?_ hP; have hb':P'.card+1 ≤ Q.card:= Finset.card_lt_card S.dropped
     calc
       a^(Q.card*χ)*(∏ i,L.bottom i) ≤ a^((P'.card+1)*χ)* (∏ i,L.bottom i):=mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hz.good.le hz.small (Nat.mul_le_mul_right χ hb')) hy
       _=a^(P'.card*χ) * (a^χ * (∏ i,L.bottom i)):=by rw [add_mul, one_mul,pow_add,mul_assoc]
       _ ≤ _:= mul_le_mul_of_nonneg_left hW (pow_nonneg hz.good.le _)
   have hK:after D Q m={⊥}:=if_neg hw
   have hL:a^(Q.card*χ) ≤ a^χ:= pow_le_pow_of_le_one hz.good.le hz.small (by nth_rw 1 [← one_mul χ]; exact Nat.mul_le_mul_right χ (card_pos.mpr (begun D S)))
   have hq':m ⊥=x:= (bed_empty D S hw).symm; apply he ▸ lastpost D f' hM hK hq' (le_trans (mul_le_mul_of_nonneg_right hL hy) hp') -- r reduction
   intro x'; refine hB x' ((cred D S x').not.mpr ?_); rcases x' with ⟨x',hh⟩; obtain rfl:x'=⊥:= mem_singleton.mp (hK ▸ hh : x' ∈ ({⊥}:Finset X)); exact not_not_intro S.base.base
end YM.OPE.Arboreal.CutOrder
