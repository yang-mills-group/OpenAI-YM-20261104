import YM.OPE.Compatible.Munch.Tips
/-! # purchase properties of region data all slices. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Borealis.Galea
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{I:Type}{i j k m:ℕ}{ε v t c C R:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown
variable {K:Sponsor G}{T:Seasons K}
section
variable {L:Host K T}(x:Site L.f)
local notation "Xθ"=> Bid.Dir G L.c
variable (A: Law (Bid.Dir G L.c))(μ:Measure (Bid.Dir G L.c))[μ.IsAddHaarMeasure]
set_option quotPrecheck false
local notation "YΦ"=> quart A μ
abbrev PerSeat (C:ℝ):Prop:=∀ i: Wings G L.c, let a:=castAt (JetB G L.c) i; A.wick a a ≤ C
variable (h:PerSeat (L:=L) A C)(hx:0 ≤ C)
include h hx
abbrev crownG (G:Gauge)(m:ℕ)(c:ℝ):price:= fun i=> (κceil m * (Fintype.card G.ColorIndex:ℝ))*(Real.sqrt c* ampleP i)
omit hx in
lemma Sz_S (k:ℕ)(ht:0 ≤ t):(quart A μ).real {w:Bid.Dir G L.c| crestPrice G t < ‖Qspot L x k w‖}≤ ((κceil k:ℝ)*(Fintype.card G.ColorIndex))* (2*Real.exp (C/2)*Real.exp (-t)):=by
       let P:= Qspot L x k; let a(i):= castAt (JetB G L.c) i; let X:= (rangeG L x k) ×ˢ(Finset.univ:Finset G.ColorIndex); let f(i: Wings G L.c):= {p:Xθ|t<‖a i p‖}; have he(i: Wings G L.c): (quart A μ).real (f i) ≤2*Real.exp (C/2)*Real.exp (-t):= (defeat A μ (a i) _).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_monotone (div_le_div_of_nonneg_right (h i) (by norm_num))) (by norm_num)) (Real.exp_nonneg _))
       have hp:{w:Xθ|crestPrice G t<‖P w‖}⊆ ⋃ i∈X,f i:=by
            intro p hv; change _<‖P p‖ at hv; by_contra hh; apply (not_lt.mpr (Tip_T (X:=Body 1 L.c) (P p) ht (fun i=>?_))) hv; by_cases H: i.1 ∈ rangeG L x k
            · rw [show cash (Limn.Tip G (Body 1 L.c)) _ _= _ from Mouth x p i H]; apply le_of_not_gt (fun ht=> hh (Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨(Finset.mem_product.mpr ⟨H,Finset.mem_univ _⟩),ht⟩⟩))
            rw [show cash (Limn.Tip G (Body 1 L.c)) _ _= _ from Ear_Q x p i H, norm_zero]; exact ht
       refine (measureReal_mono hp (measure_ne_top _ _)).trans ?_; apply le_trans (measureReal_biUnion_finset_le ..) _; apply le_trans (sum_le_sum (fun j _=>he j)) _; rw [sum_const,nsmul_eq_mul, show X.card= _ from (show X.card=(rangeG L x k).card*Fintype.card G.ColorIndex from by simp [X]),Nat.cast_mul]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast Round x k) (by positivity)) (by positivity) -- Lean measure_real syntax
lemma mac (k:ℕ) : Cane (quart A μ) (Qspot L x k) (crownG G k C):=by
        let Q:= Qspot L x k; let X:= (rangeG L x k) ×ˢ(Finset.univ:Finset G.ColorIndex); let b(i:Wings G L.c):= castAt (JetB G L.c) i; let g(i:Wings G L.c)(w:Xθ):= ‖b i w‖; let V(i:ℕ):=Real.sqrt C*ampleP i; have hp:Cane YΦ (∑ i∈X,g i) (∑ _ ∈ X,V):= by refine Cane.sum _ _ _ fun i _=>?_ ; intro j hj; exact (Lal A μ (b i) (Real.sqrt_nonneg _) ((h i).trans_eq (Real.sq_sqrt hx).symm) hj).NormT
        have hx':∀ w:Xθ,‖Q w‖≤ ‖(∑ i∈X,g i) w‖:=by
             intro w; rw [Finset.sum_apply]; apply (BitGl (Q w)).trans; let P(i: Wings G L.c):= ‖b i (Q w)‖; have hg:∑ i,P i=∑ i∈X,P i:=by
                  refine Eq.symm (sum_subset (subset_univ X) (fun i _ hi=>?_)); unfold P; have ht:b i (Q w)=0:=Ear_Q x w i (fun H=>hi (Finset.mem_product.mpr ⟨H,Finset.mem_univ _⟩)); rw [ht,norm_zero]
             refine (hg.trans (sum_congr rfl fun j hj=>congr_arg norm (Mouth x w j (Finset.mem_product.mp hj).1))).trans_le (Real.le_norm_self (∑ i∈X,g i w)) -- names
        apply (of_K hp Q.continuous.aestronglyMeasurable hx').grow; intro i hi; have hh:0≤ V i:= mul_nonneg (Real.sqrt_nonneg _) (le_trans zero_le_one (le_max_left ..)); rw [Finset.sum_apply,sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ hh; rw [show X.card=(rangeG L x k).card*Fintype.card G.ColorIndex from by simp [X],Nat.cast_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast Round x k) (by positivity)
end
end YM.OPE.Borealis.Galea
