import YM.OPE.Compatible.Ice.Guru
/-! # energy frame funds.Bills sum and shift. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{K: KernelChoices}{I:Type}{i j k m b d e:ℕ}{n:Side}{ε v t s r R A:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals Stroke
open Borealis Lav Borealis.Galea Quit.PriceZ Quit.Jac
variable {τ:Phase→ℕ}
section
variable {p q:I→ solar G d τ}{l:Filter I}{V w:I→ℝ}
lemma nectar (p:solar G d τ) (hp:coveredM (Goan p) b) : Tide (Goan p) d m ((b:ℝ)^m*‖p‖):=by
      let f:=Goan p; have hv:Tide f d 0 ‖p‖:= resin p.val (fun _=>Nat.zero_le _); intro i; refine ⟨(hv i).1,fun j=>?_⟩; let U:= f i j; let a:ℝ:= (b:ℝ)^m; let B:= (hv i).2 j; have hA : 0≤ a:= pow_nonneg (Nat.cast_nonneg _) _; let X:= Sack.mass B (payer 0); let g(i):= a*‖U i‖; have ht: SumBudget g (a*‖p‖):= by refine ⟨fun i=>mul_nonneg hA (norm_nonneg _), X.2.1.mul_left _,?_⟩; unfold g;rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left X.2.2 hA
      refine Work.F08.budget_minor ht (fun k=>mul_nonneg (zero_le_one.trans (payer m k)) (norm_nonneg _)) fun k=>?_; by_cases hx:U k=0; · change _ *‖U k‖ ≤ a*‖U k‖; rw [hx,norm_zero,mul_zero,mul_zero]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hp i j k hx) m) (norm_nonneg _)
lemma WaitX (hc:Tendsto V l atTop)(b:I→ℕ)(hp:∀ᶠ i in l, coveredM (Goan (p i)) (b i))(hx:RateLE l V p 0)(hv:RateLE l V (fun i=>(b i:ℝ)) 0): Alive l V p:=by
       intro m; exact ⟨fun i=>(b i:ℝ)^m*‖p i‖,((hv.pow m hc).mul hx.norm).mono (by simp),hp.mono fun _ h=> nectar _ h⟩
lemma Borex (hc:Tendsto V l atTop)(b:I→ℕ)(A:(i:I)→Song (Scoop G (b i)))(hz:∀i,ReadyP (A i) d)(H:Aware d τ)(hb:RateLE l V (fun i=>(b i:ℝ)) 0)(hx:RateLE l V (fun i=> billP d (b i) (τ 0) (A i)) 0): Alive l V (fun i=> ChiselV H (hz i)):=by
       have he(x:ℝ):= RateLE.const x hc; have hg: RateLE l V (fun i=>(PinB (b i) d:ℝ)) 0:=by unfold PinB; push_cast; apply RateLE.add (he 1) _ hc; exact ((he _|>.mul (((he _).mul ((he _).add (((he _).mul ((he _).mul ((he _).mul hb))).mono (show _ ≤ 0 from by norm_num)) hc)).mono (show _ ≤ 0 from by norm_num)))).mono (show _ ≤ 0 from by norm_num)
       exact WaitX hc (fun i=> PinB (b i) d) (Eventually.of_forall fun i=> Root_Q _ H (hz i)) (RateLE.of_norm_le (((he _).mul hx).mono (by norm_num)) (Eventually.of_forall fun _=> WarmCost H _)) hg
lemma Alive.score (h:Alive l V p)(hv:Tendsto V l atTop) : RateLE l V p 0:=by let f(j:Phase)(i:I):= ‖(p i).val j‖; apply RateLE.of_norm_le (RateLE.sum (f:=f) (S:=Finset.univ) hv fun i _=>(WTK h i).norm); filter_upwards with i; exact (pi_norm_le_iff_of_nonneg (x:=(p i).val) (Finset.sum_nonneg fun j _=>norm_nonneg ((p i).val j))).2 fun j=> Finset.single_le_sum (f:=fun j=> f j i) (fun _ _=> norm_nonneg _) (mem_univ _)
lemma Alive.plus_S (h:Alive l V p)(he:Alive l V q)(hv:Tendsto V l atTop): Alive l V (p+q):=by intro m; obtain ⟨c,hc,H⟩:=h m; obtain ⟨d,hd,H'⟩:= he m; refine ⟨fun i=>c i+d i,hc.add hd hv,?_⟩; filter_upwards [H,H'] with i hi hv; exact glowsA _ _ hi hv
lemma Alive.bend (h:Alive l V p)(hv:RateLE l V w 0): Alive l V (fun i=>w i • p i):=by intro m; obtain ⟨c,hc,H⟩:=h m; exact ⟨fun i=>‖w i‖*c i,(hv.norm.mul hc).mono (by simp),H.mono fun _ H=>glowsC _ _ H⟩
lemma Alive.negative (h:Alive l V p)(hv:Tendsto V l atTop):Alive l V (-p):=by rw [show -p=fun i=> (-1:ℝ) • p i from funext fun i=>(show -(p i)=_ from (neg_one_smul ℝ _).symm)]; exact h.bend (RateLE.const _ hv)
lemma Alive.minus (h:Alive l V p)(he:Alive l V q)(hv:Tendsto V l atTop):Alive l V (p-q):=by rw [sub_eq_add_neg]; exact h.plus_S (he.negative hv) hv
lemma Alive.γΖ (h:Alive l V p)(ht:Tendsto V l atTop)(hp:RateLE l V w 0)(H:Aware d τ): Alive l V (fun i=>vintage G H (w i) (p i)):=by
       intro m; obtain ⟨b,hb,hz⟩:= h m; have hh : RateLE l V (fun i=> w i/2) 0:=by simpa only [div_eq_mul_inv,add_zero] using hp.mul (RateLE.const ((2:ℝ)⁻¹) ht)
       exact ⟨fun i=> KevT d (w i) (b i),hb.add ((hh.norm.mul ((RateLE.const _ ht).mul hb)).mono (by norm_num)) ht,hz.mono fun _ h=> vintage_hi G H _ _ h⟩
end
end YM.OPE.Ibis
