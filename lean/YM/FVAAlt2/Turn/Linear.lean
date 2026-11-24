import YM.FVAAlt2.Turn.Sat
/-! Linearity of continuum and high caller; reorder natural cross-construct AMS `comet`.
 Profile.Rates at scalar/log. Do keep `Pact` instead of inserting new functions everywhere. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.FVA.Town
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color Book _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve High Detect Domain Tone Tone.Frame Momentum Outlook Motif Literal Mach
open _root_.YM.MS.Wind _root_.YM.MS.City Native Native.Wilsonian
open Motions
open scoped Topology BigOperators ContDiff Interval Pointwise
set_option linter.unusedSectionVars false
variable {G:Gauge}{I:Type}{i:ℂ}{b:Bool} {m n k:ℕ}{h x:ℝ} {d t r u:ℤ}
variable {φ ψ:Reading G} {A C: Dec G}{P:Recount G}
open High.Knobs
lemma morning_c {X Y:Recount G}(hx:Fixed X Y b d m)(c:ℂ) : Fixed (c • X) (c • Y) b d m:=fun i hi k hk E _ _ w he ht=> Light.scalar ( hx i hi k hk E w he ht ) c
lemma morning {X Y:I→ Recount G}(s:Finset I)(hv:∀ i∈s, Fixed (X i) (Y i) b d m): Fixed (∑ i∈s,X i) (∑ i∈s,Y i) b d m:=by
 classical
 induction s using Finset.induction_on with
 | empty=> simp_rw [Finset.sum_empty]; exact fun _ _ _ _=> zero_ext (fun _ _ _ _=> rfl) (fun _ _ _ _=>rfl)
 | insert i s hi ih=>
     simp_rw [Finset.sum_insert hi]; intro j hj k hk E _ _ w he hh; exact Light.add (hv i (by simp) j hj k hk E w he hh) (ih (fun j hj=> hv j (Finset.mem_insert_of_mem hj)) j hj k hk E w he hh)
def pressX (s:Signed)(F: Recount G): Recount G:= fun i=> (turnW G s) ∘ F i
lemma morningX (s:Signed){X Y:Recount G}(hx: Fixed X Y false d 0) : Fixed (pressX s X) (pressX s Y) false d 0:=fun i hi j hk=> tri_m s (hx i hi j hk)
variable {X: T (Flats G)} {V:Pearl.Flats G}
lemma mstar (h:ClockD false t r V)(he:star i=i): ClockD false t r (i • V):= fun j=> (h j).smul he
lemma sing2 {F H J:T (Flats G)} {A B C X:T (Coat G)}(ha:comet k t J A F C)(hb:comet k t J B H X): comet k t J (A+B) (F+H) (C+X):= by
 intro n; obtain ⟨ ⟨r, hA,V,hG⟩,ha₀⟩:= ha n; obtain ⟨ ⟨s,hB,W,hH⟩,hb₀⟩:= hb n; refine ⟨ ⟨r ⊔ s,?_, Cap0.heap.plus ( clockTrans V le_sup_left ) ( clockTrans W le_sup_right ), Cap0.add (hG.collects le_sup_left) (hH.collects le_sup_right)⟩,False.elim ⟩
 simp only [platform,Pi.add_apply,map_add, Finset.sum_add_distrib]; rw [add_add_add_comm]; exact hA.plus hB
lemma singc {F J:T ( Flats G )} {A B:T (Coat G)}(ha:comet k t J A F B)(hi:star i=i): comet k t J (i • A) (i • F) (i • B) := by
   intro n; obtain ⟨⟨u,hf,h,x⟩,H⟩:=ha n; refine ⟨⟨_,?_, mstar h hi,x.smul hi⟩,False.elim⟩; simp only [platform,Pi.smul_apply,map_smul,← smul_add,← Finset.smul_sum]; exact hf.scale _
lemma sings_zero (F:T (Flats G)): comet k t F 0 0 0:= fun i=> (show sings false t k 0 False (platform F i 0) 0 0 from (by unfold platform; simp only [Pi.zero_apply,map_zero, Finset.sum_const_zero]; exact zero_sing _)) -- step0 yields exactly
lemma SumM {A Y:I→ T ( Coat G )} {F:I→ T ( Flats G )} (J:Finset I)(h:∀ i∈J,comet k t X (A i) (F i) (Y i)): comet k t X (∑ i∈J,A i) (∑ i∈J,F i) (∑ i∈J,Y i):= by
 classical
 induction J using Finset.induction_on with| empty=> simpa using sings_zero X (k:=k) (t:=t)| insert i s hi ih=> rw [Finset.sum_insert hi,Finset.sum_insert hi,Finset.sum_insert hi]; exact sing2 (h i (by simp)) (ih fun i hi=> h i (Finset.mem_insert_of_mem hi))
lemma Zsame (U V:Flats G)(hh:Pact U V)(hs:Stay k U)(he:Stay k V): hereZ k U h x= hereZ k V h x:=by apply Lift.unique _ (live0 he); exact Lift.congr (live0 hs) ( Train.prom hh _ _ _ ) -- notation
lemma straight {X:I→Flats G}(s:Finset I) (ht:∀ i∈s, Stay k (X i)): hereZ k (∑ i∈s,X i) x h=∑ i∈s,hereZ k (X i) x h:= by
    classical
    have hu : Lift (Parade (∑ i∈s,X i) k h x) (∑ i∈s,hereZ k (X i) x h):= by rw [page_sum]; exact Pick.fin (n:=0) _ (fun i hi=>show Lift _ _ from live0 (ht i hi)) -- Pick
    exact Lift.unique (Rub ⟨ _,hu ⟩ 0) hu
lemma straight_c {F:Flats G}(hf:Stay k F)(c:ℂ): hereZ k (c • F) x h=c • hereZ k F x h:= by
    apply Lift.unique (live0 (Stay_scale hf c)); rw [ page_smul ]; exact Lift.static (live0 hf ) c
lemma archive_c (X:T ( Flats G )) (hv:∀ i,Stay k (X i))(c:ℂ): Archive k (c • X)=c • Archive k X:= by funext n i; unfold Archive four; simp only [Pi.smul_apply]; rcases i with ⟨a,b⟩; dsimp only; rw [straight_c (hv _)]; rfl -- lint
lemma archive_sum {X:I→ T (Flats G)} (s:Finset I) (ht:∀ i∈s,∀ j, Stay k ( X i j )): Archive k (∑ i∈s,X i)=∑ i∈s, Archive k (X i):= by
 funext n y; obtain ⟨a,b⟩:=y; unfold Archive four; rw [Finset.sum_apply]; dsimp only; rw [straight (X:=fun i=>X i n) s (fun i hi=> ht i hi _), Finset.sum_apply,Finset.sum_apply,Finset.sum_apply]
lemma archive_eq {X Y:T (Flats G)} (h:∀ i,Pact (X i) (Y i))(hv:∀ i, Stay k (X i))(he:∀ i,Stay k (Y i)): Archive k X=Archive k Y:= by funext n y; rcases y with ⟨a,b⟩; unfold Archive four; dsimp only; rw [Zsame _ _ (h n) (hv n) (he n)]
end YM.MS.FVA.Town
