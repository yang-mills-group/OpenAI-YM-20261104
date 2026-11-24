import YM.OPE.Compatible.Ibis.Small
/-! # stencil estimate in all weighted seats. Offsets count. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{K: KernelChoices}{I:Type}{i j k m b d:ℕ}{n:Side}{ε v s r R A:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals Stroke
section
noncomputable def CapeX (x:Site n)(p:Page I i): Fin i→ Site n × I:=fun j=>(x+wrap n (p j).1,(p j).2)
lemma SoloX [DecidableEq I] (x:Site n)(p q:Page I i):render x q (fun j=>Pi.single (CapeX x p j) 1)= if circle p n=circle q n then 1 else 0:=by
         have ht(k j:Page I i):CapeX x k=CapeX x j↔ Script.circle k n=Script.circle j n:=by unfold CapeX Script.circle; simp_rw[funext_iff,Prod.mk.injEq,add_right_inj]
         split
         next h=> unfold render; change (∏ j,(Pi.single (CapeX x p j) (1:ℝ): Site n×I→ℝ) (CapeX x q j))=_; rw [(ht ..).mpr h]; simp only [Pi.single_eq_same,prod_const_one]
         next h=> obtain ⟨i,hi⟩:= Function.ne_iff.mp ((ht p q).not.mpr h); apply prod_eq_zero (mem_univ i); exact Pi.single_eq_of_ne hi.symm _
-- board all tags sphere receives probes.
lemma MonoCX (h:2*(b+1)<n.val): InjOn (fun x:Page (Shade G) i=>Script.circle x n) (↑(encircled G b i)):=by
       intro p hp q hq e; obtain ⟨v,hv,rfl⟩:= Finset.mem_image.mp hp; obtain ⟨w,hw,rfl⟩:= Finset.mem_image.mp hq; ext1 j; have ht:= Prod.mk.inj (congr_fun e j); refine Prod.ext ?_ (Prod.mk.inj (congr_fun e j)).2; let p:= (pealB (v j)).1; let q:= (pealB (w j)).1; have hu:wrap n p=wrap n q:= (Prod.mk.inj (congr_fun e j)).1; exact (borne h p (v j|>.1.property.1)).symm.trans ((congr_arg lift hu).trans (borne h q (w j|>.1.property.1)))
variable (x:Site n) (p:Seat k m (Shade G))
lemma TallG (h:2*(b+1)<n.val)(hp:p∈ Hoard G b k m)(i:ℕ)(a:Page (Shade G) i)(ha:a∈encircled G b i):scribe x (lilies m k _ p i) (fun j=>Pi.single (CapeX x a j) 1)=lilies m k _ p i a:=by
       unfold scribe; let P:= lilies m k _ p i; let g(j):deck (Shade G) n:=Pi.single (CapeX x a j) 1; rw [tsum_eq_single a]; swap
       · intro j hj; change P j * render _ _ _ =0; by_cases he:j∈encircled G b i
         · have hh: Script.circle a n ≠ Script.circle j n:=fun h'=> hj (MonoCX h he ha h'.symm); have hr:render x j g=0:=(SoloX x a j).trans (if_neg hh); exact mul_eq_zero_of_right _ hr
         exact mul_eq_zero_of_left (hp i j he) _
       change P a * render x a g=_; rw [show render x a g=1 from (SoloX x a a).trans (if_pos rfl),mul_one]
noncomputable abbrev GramU (G:Gauge)(b m k:ℕ):=∑ i∈range (k+1),gumBill G b i m
lemma gumSafe (h:2*(b+1)<n.val)(hp:p∈ Hoard G b k m)(hx:∀ (i:ℕ), i<d →∀ u:Fin i→ Tab (Shade G) n, ‖scribe x (lilies m k _ p i) (fun i=> Pi.single (u i) 1)‖ ≤ R)(hB:0≤R): ‖Cap (Shade G) d k m p‖ ≤ GramU G b m k * R:=by
       let H:= lilies m k (Shade G); let P:= Cap (Shade G) d k m p; let D:= GramU G b m k; have ht(i:ℕ):0≤gumBill G b i m:=by unfold gumBill; positivity
       have hR : 0≤D*R:=mul_nonneg (sum_nonneg fun i _=>ht i) hB; apply totalU; refine ⟨?_,?_⟩ -- Volume maybe And
       · exact (sproutV _ _ _).1
       intro i; by_cases hI:i≤k; swap; · rw [(sproutV _ _ _).1 i (not_le.mp hI)]; exact Sack.zero hR _
       rw[crimp]; by_cases hQ:i<d; swap; · rw[if_neg hQ]; exact Sack.zero hR _
       rw [if_pos hQ]; apply Sack.tips (A:=gumBill G b i m*R) _ (mul_le_mul_of_nonneg_right (single_le_sum (fun j _=>ht j) (mem_range.mpr (by omega))) hB); let f(j:Page (Shade G) i):= lilies m k _ p i j; let S:= encircled G b i
       refine ⟨fun i=>mul_nonneg (zero_le_one.trans (payer ..)) (norm_nonneg _),(sproutV _ _ p).2 i |>.2.1,?_⟩; rw [tsum_eq_sum (s:=S) (fun i hi=>by rw [hp _ _ hi,norm_zero,mul_zero]),show S= _ from (show S= Finset.univ.image (CageB b i (G:=G)) from rfl),sum_image Cage_inj.injOn]; let C:=(↑(1+i*(4*b):ℕ):ℝ)^m; apply (sum_le_sum (g:=fun _=> C*R) (fun j _=>?_)).trans_eq; swap
       · let X:=CageB b i j; have hz:stamp X≤ 1+i*(4*b):=by
               rw [Page.perimeter]; exact Nat.add_le_add_left ((Finset.sum_le_sum (f:=fun k:Fin i=> Laurent.size (X k).1) (fun k _=> Spindle.bounded (j k|>.1.property.1))).trans_eq (by simp)) _
         have hA: figure m X≤ C:=pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hz) _; exact mul_le_mul hA (by rw [← TallG x p h hp i X (mem_image.mpr ⟨j, mem_univ _,rfl⟩)]; apply hx i hQ) (norm_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
       rw [sum_const,card_univ,Fintype.card_fun,nsmul_eq_mul,Fintype.card_fin,Nat.cast_pow]; exact (mul_assoc ..).symm
abbrev cashRead (x:Site n)(i:ℕ)(v:Fin i→ deck I n) [Fintype I] := (ContinuousMultilinearMap.apply ℝ _ ℝ v) ∘L reading m i x ∘L moduleAt m k i I
lemma stamp_C (p:Seat k m I)[Fintype I](u:Fin j→deck I n): cashRead (k:=k) (m:=m) x j u p=scribe x (lilies m k _ p j) u:=by rw [cashRead,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,toScript]; exact (instruments _ (sootS ((sproutV ..).2 _)) ..).tsum_eq.symm
lemma price_H [Fintype I] [DecidableEq I](p:Seat k m I)(v:Fin i→ Tab I n): ‖scribe x (lilies m k _ p i) (fun i=>Pi.single (v i) 1)‖ ≤ ‖p‖:=by
       let f:=lilies m k _ p i; let u(i:Fin i):deck I n:= Pi.single (v i) 1; let g(i):=f i*render x i u; have hv:= Sack.mass ((sproutV m k p).2 i) (payer m)
       have he(p:Page I i): ‖g p‖ ≤ ‖f p‖:=by
             unfold g; rw [norm_mul]; apply mul_le_of_le_one_right (norm_nonneg _); unfold render; rw [norm_prod]; apply le_trans (Finset.prod_le_prod (g:=fun _=>(1:ℝ)) (fun _ _=>norm_nonneg _) (fun i _=>?_))
             swap; · unfold u; by_cases hv:(x+wrap n (p i).1,(p i).2)=v i
                     · rw [hv,Pi.single_eq_same,norm_one]
                     rw [Pi.single_eq_of_ne hv,norm_zero]; exact zero_le_one
             simp -- layout likely bad
       have hS:Summable (fun i=>‖g i‖):=Summable.of_nonneg_of_le (fun i=>norm_nonneg _) he hv.2.1; exact (norm_tsum_le_tsum_norm hS).trans ((hS.tsum_le_tsum he hv.2.1).trans hv.2.2)
end
end YM.OPE.Ibis
