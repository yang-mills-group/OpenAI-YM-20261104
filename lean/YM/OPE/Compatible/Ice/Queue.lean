import YM.OPE.Compatible.Ice.Mar
/-! # Calls after choosing post-height, before periodic calendars. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{K: KernelChoices}{I:Type}{i j k m b d e Z:ℕ}{n:Side}{ε v t s r R A:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals Stroke
open Borealis Lav Borealis.Galea Quit.PriceZ Quit.Jac
variable {τ:Phase→ℕ}
section fee
-- one height by tau.Dto.
variable (G)(K:KernelChoices) (hz:4 ≤j)(F k d m:ℕ)
lemma Θfund (x:ℝ)(t s:ℝ): ∀ᶠ n:Side in Filter.comap PNat.val atTop, let b:= StrayT t x; 2*(b+1)<n.val∧∀ V:Train j,∀ p∈Hoard G b k m,‖boostS (rentV G V hz K n) (1/2) m k p-boostS (atlasF G V hz K) (1/2) m k p‖ ≤ Real.exp (s*x)*‖p‖:= ( (show Tendsto PNat.val (Filter.comap PNat.val atTop) atTop from tendsto_comap).eventually_gt_atTop _).and (Solv K hz (1/2) _ (StrayT t x) k m G (Real.exp_pos _))
lemma WhereQ (t s:ℝ) (x:ℝ): ∃ m':ℕ,∀ n:Side, m'≤ n.val → let b:=StrayT t x; 2*(b+1)<n.val ∧∀ V:Train j,∀ p∈ Hoard G b k m, ‖boostS (rentV G V hz K n) (1/2) m k p-boostS (atlasF G V hz K) (1/2) m k p‖≤ Real.exp (s*x)*‖p‖:=by
        let f:= Filter.comap PNat.val atTop; obtain ⟨s,hs,hA⟩:= (show ∃ s∈(atTop:Filter ℕ),_ from mem_comap.mp (Θfund G K hz k m x t s)); obtain ⟨b,hb⟩:= eventually_atTop.mp (show ∀ᶠ i:ℕ in atTop,i∈s from hs); exact ⟨b,fun N H=> hA (hb N.val H)⟩
variable (q:Phase)
private lemma ρu (e:ℕ)(h:s<t):∃ v:ℝ,0 < v ∧ s+ e*v ≤ t:=by
        let v:=(t-s)/(e+1:ℝ); have hv : 0 <v:=div_pos (sub_pos.mpr h) (by positivity); refine ⟨v,hv,?_⟩; have hh : (e+1:ℝ)*v=t-s:=by unfold v; field_simp
        have he:e*v ≤ (e+1:ℝ)*v:=mul_le_mul_of_nonneg_right (by linarith) hv.le; linarith
include q
lemma TriviaC (hc:s<t)(he:e ≤ Z+1): ∃ H:ℝ→ℕ,∀ (l:Filter I)(c:I→ℝ)(a:I→solar G k τ)(X:I→ Train j) (n:I→Side)(x:∀ i,Site (n i)), Tendsto c l atTop→(∀ᶠ i in l,H (c i)≤ (n i).val)→ Alive l c a→ Audible G K n l c j Z X hz (fun i=> Rink (x i) (a i) q) s→ RateLE l c (fun i=> Cap (Shade G) e (k+q.val) (τ q) (boostS (atlasF G (X i) hz K) (1/2) (τ q) (k+q.val) ((a i).val q))) t:=by
        let m:=τ q; let d:= k+q.val; obtain ⟨b,hb,H⟩:= ρu (4*d+m) hc; choose F hF using WhereQ G K hz d m b s; refine ⟨F,fun l c a X n x ht hs hA hy=>?_⟩
        obtain ⟨e',hR⟩:=exists_nat_gt (-s/b); have hh: -(e'*b)≤ s:=by have hg:= (div_lt_iff₀ hb).1 hR; linarith
        obtain ⟨s',hS,hp⟩:=hy.yod; obtain ⟨r,hK,hP⟩:= hA (m+e'); have hz' : s+(4*d+(m:ℝ))*b ≤ t:=by exact_mod_cast H
        apply RateLE.of_norm_le (ZeraX G ht K hz hS hb.le hh hz' hK (d:=e) d Z); filter_upwards [hp,hP,hs] with i hi hv hu; obtain ⟨hl,hU⟩:=hF (c i) (n i) hu; let B:=StrayT b (c i); let V:= X i; let P:= (a i).val q; apply LowQ (K:=K) (b:=B) V hz (x i) P (fun i'=> (a i).property.1 q i') (hv q) hi.1 hl (Real.exp_nonneg _) he hi.2 (hU V) -- maybe hs bind
end fee
end YM.OPE.Ibis
