import YM.OPE.Compatible.Bowman.Round
/-!
# Financial uplift and startup chain. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Work.F05 Flume Flume.Script Frequency
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J Y Z:Type}{G:Gauge}{N:Side}{p q:Clip}{R T:PathData G}{P:Patch}{K:KernelChoices}{V:ChartRatio G}{i j t r n m:ℕ}{s s' u b U e d:ℝ}{B:Sponsor G} {H:Seasons B}
namespace Alps
open Page Planned.PrimaryIntegral295.Carrier
variable (A:Alps B H i b)
abbrev word (j:ℕ):= inkV A.live A.clip j
abbrev liftZ (j:ℕ):= leafV A.live j
lemma fullK (n:ℕ): stint A.word n (fun _=>mainTerm A.clip A.live) := ⟨fun n=>(chartK A.live A.clip n A.pays).1, fun i k _=> (inkSongs A.live A.clip i k 0 A.pays).2.2, fun _ v p=>mainTerm_gauge A.pays p v, fun i m=> (inkSongs A.live A.clip 1 i m A.pays).2.1, fun i=> (inkSongs A.live A.clip 1 i 0 A.pays).1⟩
lemma fullL (n:ℕ):stint A.liftZ n (fun _=> Precision.loop A.live):= ⟨fun i=>(tubesY A.live A.clip i A.pays).1, fun i k _=> (leafSongs A.live A.clip i k 0 A.pays).2.2, fun _ v p=>loop_gauge A.pays p v,fun i m=>(leafSongs A.live A.clip 1 i m A.pays).2.1,fun i=> (leafSongs A.live A.clip 1 i 0 A.pays).1⟩
lemma stint_cut (p q:(r:ℕ)→Script (Shade G) r)(R T:∀ n:Side,Config G n→ℝ)(h:stint p r R)(hv:stint q r T) : stint (p-q) r (R-T):=by
    have hr(n):folk (q n):= hv.here n
    refine ⟨fun i=> (h.plot i).sub (hv.plot i),?_,fun i g u=>congr_arg₂ (fun x y=>x-y : ℝ→ℝ→ℝ) (h.stand i g u) (hv.stand i g u),fun n=>folkD (h.here _) (hr _),?_⟩
    · intro i k hk v
      have hp: Summable (p k):= folk_whole (h.here k); have he: Summable (q k):= folk_whole (hr k)
      change library i (p k-q k) (spool G i∘v)= iteratedFDeriv ℝ k (R i ∘ represent-T i∘ represent) 0 v; rw [show p k - q k=p k+(-1:ℝ)•q k by simp [sub_eq_add_neg],libAdd _ ((-1:ℝ) • q k) hp (he.const_smul (-1:ℝ)), libScale,iteratedFDeriv_sub_apply ((h.plot i).of_le le_top) ((hv.plot i).of_le le_top), _root_.sub_apply]; erw [h.wink i k hk v,hv.wink i k hk v]; ring
    intro i; change (p i-q i).Idem; rw [show p i-q i=p i+(-1:ℝ)•q i from by simp [sub_eq_add_neg]]; exact idemAdd _ _ (h.sym i) (idemScale _ _ (hv.sym i)) (folk_whole (h.here i)) (folk_whole (folkS (hr i) _))
lemma textBudget (A:Alps B H i b)(L:Alps B H i U)(hp:(A.root - L.root).strip s u)(h:i≥4)(hh:0<s)(ht:0≤ u)(m:ℕ): soot m (A.word 2-L.word 2) ((Fintype.card (Ink (Shade G) 2):ℝ)*(widthCost s m*u)) := by
    let P:=A.word 2 - L.word 2; let Q:=A.root-L.root; have he:= (stint_cut _ _ _ _ (A.fullK 2) (L.fullK 2)).sym 2; refine layered _ (fun j:Ink (Shade G) 2=> ?_); change Sack (poise m) (sliceP P j) _; rw [show sliceP P j=upland (Script.crop P j) from funext (fun x=>pin_slots P j x he.1)]
    apply upland_bill; let B:= Script.crop P j; have H(i:Bin 1): B i= if (j 0).2=(j 1).2 then Q (coord (j 0).1) (coord (j 1).1) (lemmaCov i) else 0:=by
        let z:= wreath 1 (0,i); let p:=syn z j; have hg:p.primary=0:=header ..; have hv : (p 1).1=lemmaCov i:=by change stepOut z _= _; erw [flowPart 0 i (0:Fin 1),zero_add]; rfl
        change A.word 2 p-L.word 2 p=_; unfold word; rw [A.textReal h p hg, L.textReal h p hg,hv,show (p 0).2=j 0 from rfl, show (p 1).2=j 1 from rfl]; split_ifs <;> first|rfl|simp
    by_cases h:(j 0).2=(j 1).2; swap
    · have hd :Script.crop P j=0:= by ext x; change B x=0;rw [H,if_neg h]
      rw [hd]; exact Sack.zero (mul_nonneg (zero_le_one.trans (widthCost_ge hh m)) ht) _
    let Z:= Q (coord (j 0).1) (coord (j 1).1); have hv: Sack (poise m) Z (widthCost s m*u):=by
       have hg:= width_income hh (hp (coord (j 0).1) (coord (j 1).1)) m; unfold Sack; simp_rw [liftCostSame, mul_comm (liftCost ..)]; exact hg
    rw [show Script.crop P j= Z ∘ lemmaCov from funext fun i=> (H i).trans (if_pos h),show poise m (I:=Flume.Keys 1)= poise m ∘ lemmaCov from ?_]; exact hv.adroit lemmaCov
    ext1 x; unfold poise notch; rw [couple_size]; simp only [Fin.sum_univ_one]; rfl
-- cost clip family
end Alps
end YM.OPE.Votive
