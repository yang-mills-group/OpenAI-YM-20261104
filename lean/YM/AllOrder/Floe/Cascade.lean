import YM.AllOrder.Plateau.Indigo
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Floe
open Function Filter Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Uniform SectorMeasure PhysicalNext Repeat Fare Lapis
open AnalyticBridge VerifiedReset Collection Quotes Next.Fluctuations Next.SectorChange ConnectedActivityE6 Blaze Brush
open AbsoluteSums Org Poll
open Ker Ker.Start Haiku Haiku.Coat Fire PertExtension.Series Radial
open Laplace Laplace.SigmaP Response Ink Ink.Method Ink.Money Laurent Stationary
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open PositionX.Jet Extra.Iteration
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {G: Gauge} {c f n : Side} {k j w N : ℕ} {S:StepData c f}
variable {σ C Z D β Θ:ℝ}
section jet
-- monomial shift: in numerical implementation prefix ratioFine etc, formal operation.
variable {X Y:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
local notation "L"=>ℝ×X
lemma someM (j k:ℕ) : someJ (fun t:ℝ=> t^k) j = if k=j then 1 else 0:= by
 unfold PositionX.Jet.someJ; rw [iteratedDeriv_fun_pow_zero]; split; rename_i hi; · subst j; simp; field_simp
 simp; omega
lemma dispersal (f:ℝ→ℝ) (h:ContDiffAt ℝ ω f 0) (a:ℝ)(j k:ℕ): someJ (fun p:ℝ=>(a*p)^k*f p) j= if k≤j then a^k*someJ f (j-k) else 0:= by
 let P (x:ℝ):=x^k
 let u : ℝ→ℝ:= (fun _=>a^k) * P
 have he : (fun p:ℝ=>(a*p)^k*f p)=u*f:= by funext i; rw [mul_pow]; rfl
 have ht:ContDiffAt ℝ ω P 0:=contDiffAt_id.pow k; have hu:ContDiffAt ℝ ω u 0:= contDiffAt_const.mul ht; have hr(i:ℕ) : someJ u i=a^k*someJ P i:= ((eo_Act i ht).smul (a^k)).writes i le_rfl
 rw [he,some_mul hu h, plus_sum]
 by_cases h':k≤ j; swap; · rw [if_neg h']; refine Finset.sum_eq_zero (fun l hl=>?_); have hh:= Finset.HasAntidiagonal.mem_antidiagonal.mp hl; rw [hr,show someJ P l.1=0 from (someM ..).trans (if_neg (by omega)),mul_zero,zero_mul]
 rw [if_pos h',Finset.sum_eq_single (k,j-k),hr k,show someJ P k=1 from (someM k k).trans (if_pos rfl),mul_one]; intro l hl hm; obtain ⟨t,i⟩:= l; have hh:t+i=j:= mem_antidiagonal.mp hl; have hh': k≠t:= by rintro rfl; exact hm (by rw [show i=j-k by omega]); -- layout
 rw [hr,show someJ P t=0 from (someM t k).trans (if_neg hh'),mul_zero,zero_mul]
 exact fun H=> False.elim (H (Finset.HasAntidiagonal.mem_antidiagonal.mpr (show k+(j-k)=j by omega)))
lemma favor_exp (f:X→ℝ)(h: ContDiffAt ℝ ω f 0)(a:ℝ)(x:X)(j k:ℕ): jet (fun x:L=> x.1^k*f x.2) j (a,x)= if k≤j then a^k*jet f (j-k) x else 0:= by
 have hh : ContDiffAt ℝ ω (fun x:L=> x.1^k * f x.2) 0:= (contDiffAt_fst.pow _).mul (ContDiffAt.comp (g:=f) _ h contDiffAt_snd)
 have hF : ContDiffAt ℝ ω (fun t:ℝ=> f (t • x)) 0:=ContDiffAt.comp (g:=f) (f:=fun t:ℝ=>t • x) 0 ((zero_smul ℝ x).symm ▸ h) (contDiffAt_id.smul contDiffAt_const)
 have hz : (fun t:ℝ=> (t*a)^k*f (t• x))=(fun t:ℝ=>(a*t)^k*f (t• x)):=funext fun i=> by rw [mul_comm i]
 rw [← jet_entry (hh.of_le le_top),← jet_entry (h.of_le le_top)]; change someJ (fun t:ℝ=> (t*a)^k*f (t• x)) j= _; rw [hz]; exact dispersal _ hF a j k
-- Ribbon doesn't use propagations beyond j if rank.matched
lemma favor_pocket (f:X→ℝ)(h: ContDiffAt ℝ ω f 0)(d r k j : ℕ)(hf:∀ p<r, iteratedFDeriv ℝ p f 0=0) (a:ℝ)(x:X)(hk:d=k+r)(hl:j<d): jet (fun x:L=> x.1^k*f x.2) j (a,x)=0:= by
 rw [favor_exp f h]; split; · rw [jet, hf _ (by omega)]; simp
 rfl
end jet
end YM.AllOrder.Floe
