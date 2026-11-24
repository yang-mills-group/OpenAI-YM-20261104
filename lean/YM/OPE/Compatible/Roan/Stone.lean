import YM.OPE.Compatible.Roan.Tenter
/-! # mixed-rank vertices HopeTD -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type*} {i k m:ℕ}{t C s u z ℓ v a c e r R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable (L:Host K T)
set_option quotPrecheck false
local notation "Fθ"=> L.ForestQ
variable {N:ChartRatio G}(hN:LocalRatio N)(H:StackP N r R t)
open Dew AnalyticNext.QuarticMatch Radius Radius.Articles Radius.Polish Radius.Fetch Radius.Showroom Estimate
variable (h:L.Rich s c e v u C)(he:0 <e)(hc:0≤c)(hp:0≤v)
noncomputable abbrev χ2 (N:ChartRatio G): L.DirA→ℝ:= (-jet L.PL 2)+(jet (turnt L N) 2)
noncomputable abbrev χ4 (x:L.DirA):ℝ:= -(jet L.PA 4 x)
include h hc he
lemma leafE : Tires L (Rate3 L) 3 c s∧ Tires L (χ4 L) 4 c s:=by
          obtain ⟨p,hp⟩:=h.stem; exact ⟨nTires L (Kea L L.PA hp (by norm_num) hc he), nTires L (Kea L L.PA hp (by norm_num) hc he)⟩
omit h hc he
include hN
lemma tel4 : Rate4 L N=(χ4 L)+(χ2 L N):=by
        funext x; unfold Rate4 χ4 χ2; have hx : jet (turnt L N) 2 x= jet (taxY L.ForestQ N) 2 x.2:=by
              let S:= ContinuousLinearMap.snd ℝ (Bid.Dir G L.c) (AxisChart G Fθ); unfold jet; rw [show iteratedFDeriv ℝ 2 (turnt L N) 0 _= _ from lin_rate_at (taxY L.ForestQ N) S 0 (accountV Fθ hN).1 2 (fun _=>x)]; rfl
        simp only [Pi.add_apply,Pi.neg_apply,hx]; ring
include H h he hp
lemma taper: Tires L (χ2 L N) 2 (v+4*t) s:=by
        obtain ⟨p,hp'⟩:=h.aged; exact FTires L (nTires L (Kea L _ hp' (by decide) hp he)) (Kea L _ (teeP L hN H s) (by decide) (mul_nonneg (by norm_num) H.pays.1) H.sweep.sizes.1)
end
section
open Lav
variable {X Y:Type*}[MeasurableSpace X]{u v w g:X→ℝ}{M:Measure X}[IsProbabilityMeasure M]
omit [IsProbabilityMeasure M] in lemma PuSum (T:Finset I)(f:I→X→ℝ)(h:∀ i∈T, Pu M (f i)):Pu M (∑ i∈T,f i):=by
       induction T using Finset.induction_on with
       | empty=> simp only [sum_empty]; intro i hi; exact ⟨0,le_rfl,aestronglyMeasurable_zero,by simp⟩
       | insert i T hi ih=> rw[sum_insert hi]; exact addedP (h i (mem_insert_self ..)) (ih fun j hj=>h j (mem_insert_of_mem hj))
omit [IsProbabilityMeasure M] in lemma Pτ (f:X→ℝ)(t:ℝ): a_ M (t • f)= t*a_ M f:= integral_const_mul .. -- omit
lemma PuPier (hv:Pu M u)(g:I→X→ℝ)(h:Finset I)(hp:∀ i∈h,Pu M (g i))(b:I→ℝ): κ2 M u (∑ i∈h,b i • g i)=∑ i∈h,b i *κ2 M u (g i):=by
       have ht(i:I): κ2 M u (b i • g i)=b i*κ2 M u (g i):=by unfold κ2; rw [mul_smul_comm,Pτ,Pτ]; ring -- using hf? mul_smul
       induction h using Finset.induction_on with
       | empty=> rw [sum_empty,sum_empty]; simp only [κ2,mul_zero,a_,Pi.zero_apply,integral_zero,sub_zero]
       | insert i s hi ih=>
             have he:∀ j∈s,Pu M (g j):= fun j hj=> hp j (mem_insert_of_mem hj); have hf:{p q:X→ℝ}→ Pu M p→Pu M q→ κ2 M u (p+q)=κ2 M u p+κ2 M u q:=by intro p q hP hQ; unfold κ2; rw[mul_add,Etick (timesP hv hP) (timesP hv hQ),Etick hP hQ]; ring
             rw [sum_insert hi,sum_insert hi,hf (scaleP (hp i (mem_insert_self ..)) _) (PuSum _ _ (fun i hi=> scaleP (he i hi) _)),ht,ih he] -- mem infer
lemma PuPier3 (hv:Pu M u)(hx:Pu M v)(g:I→X→ℝ)(h:Finset I)(hp:∀ i∈h,Pu M (g i))(b:I→ℝ): κ3 M u v (∑ i∈h,b i • g i)=∑ i∈h,b i*κ3 M u v (g i):=by
        rw [beak3, PuPier (timesP hv hx) g h hp b, PuPier hv g h hp b, PuPier hx g h hp b, Finset.mul_sum,sum_mul, ← sum_sub_distrib, ← sum_sub_distrib]; refine sum_congr rfl fun i _=>?_ ; rw [beak3]; ring
end
end YM.OPE.Borealis.Galea
