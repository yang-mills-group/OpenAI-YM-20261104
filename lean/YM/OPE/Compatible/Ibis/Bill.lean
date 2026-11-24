import YM.OPE.Compatible.Ibis.Beacon
import YM.OPE.Compatible.Roost.Fan
/-! # full census rotor. any d. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Ibis
open Function Filter Set MeasureTheory Lattice Laurent RG Wilson Flume Flume.Page Flume.Script Gauge
open Pill Jargon Matrix Bloch FreeResolvent Precision Exterior Source Next.Rank Next.Rank.Spindle Silt Silt.Float Silt.Phere Next.Free Frequency Beamer
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open PertExtension Series Libra Stranded Libra.Shell Libra.Flock Cascade Cascade.Paver ScriptJ GaussianScore Radial Tensor Cloud Terp MSbar.Tree MSbar.Tree.Resolvent Streamer
attribute [local instance] Gauge.frobInner
variable {G:Gauge}{K: KernelChoices}{I:Type}{i j k m b d t:ℕ}{n:Side}{ε v s r R A:ℝ}
open Finset Metric
open Score Drift Cascade.Rill Glass Coin Pilot Shell Char Planned.PrimaryIntegral295.Carrier Flume.Virgin PhysicalNext.Repeat.Aroma Tree Woody Limn Zeph Spells Raucous Raucous.Host Votive Stationary Cinders Crown Push Push.AbsoluteSums.Animals Stroke
open Borealis Lav Borealis.Galea
section
variable (V:Train i)(h:4 ≤ i)(d:ℕ)
noncomputable abbrev censusE (G:Gauge)(K:KernelChoices)(h:4 ≤ i)(d:ℕ):price:=J1+(Fintype.card (Shade G):ℝ) • hikeP (J1+Θspin K h) d
lemma Eu_I : Borealis.Galea.Cane (quart (Vessel K V G n h) (Chart.tangent G (Body 1 n))) (fun x=> (1+‖spool G n x‖)^d) (((n.val:ℝ)^4) • censusE G K h d):=by
        let μ:= quart (Vessel K V G n h) (Chart.tangent G (Body 1 n)); have hP:IsProbabilityMeasure μ:=inferInstanceAs (IsProbabilityMeasure (quart (Vessel K V G n h) (Chart.tangent G (Body 1 n)))); let F:= fun (x:Bid.Dir G n)=> ‖spool G n x‖; let A:=Tab (Shade G) n; let g(i:A)(x):=(1+‖(spool G n x) i‖)^d; let b(i:A):=hikeP (J1+Θspin K h) d
        have hx:Borealis.Galea.Cane μ (∑ i,g i) (∑ i,b i):=by refine Borealis.Galea.Cane.sum univ _ _ fun i _=>?_; exact powerQ ((Borealis.Galea.Cane.constant (μ:=μ) (1:ℝ) (by norm_num: ‖(1:ℝ)‖ ≤ 1)).add ((spokeV V h i).normVal)) d
        let X := (Borealis.Galea.Cane.constant (μ:=μ) (1:ℝ) (by norm_num:‖(1:ℝ)‖≤1)).add hx; apply (of_K X ((continuous_const.add (spool G n).continuous.norm).pow d|>.aestronglyMeasurable) ?_).grow ?_
        · intro x; change ‖(1+‖spool G n x‖)^d‖≤ _; rw [Real.norm_of_nonneg (show 0≤ (1+‖spool G n x‖)^d from by positivity)]; refine le_trans ?_ (Real.le_norm_self _); simp only [Pi.add_apply,Finset.sum_apply]; cases isEmpty_or_nonempty (Tab (Shade G) n) with
          | inl hv=> change _ ≤ 1+∑ _, _; rw [Finset.univ_eq_empty (α:=A),sum_empty,show spool G n x=0 from Subsingleton.elim ..,norm_zero]; simp only [add_zero,one_pow,le_refl]
          | inr hf=>
              obtain ⟨i,H,hT⟩:= exists_max_image Finset.univ (fun i:A=> ‖(spool G n x) i‖) univ_nonempty; have hp':‖spool G n x‖≤ ‖(spool G n x) i‖:= (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j=>hT _ (mem_univ _);
              apply le_trans _ (le_add_of_nonneg_left (by norm_num: (0:ℝ)≤ 1)); apply le_trans _ (single_le_sum (f:=fun j:A=>g j x) (fun j _=> by unfold g; positivity) (mem_univ i)); exact pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hp') _
        intro i' hi; rw [Pi.add_apply,Finset.sum_apply,show ∑ i:A,b i i'= Fintype.card (Site n)*(Fintype.card (Shade G):ℝ)*(hikeP (J1+Θspin K h) d i') from ?_,site_card,Nat.cast_pow]; unfold censusE; rw [Pi.smul_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul,mul_add]; apply add_le_add (b:=(_ * _)) (by change (1:ℝ)≤(n.val:ℝ)^4*1; rw [mul_one]; exact one_le_pow₀ (by exact_mod_cast n.pos)) (le_of_eq (mul_assoc ..)); unfold b A Tab; simp
-- paid.TracePay output line error Spectre. buy Price5.
variable {Q:Sponsor G}{T:Seasons Q}{P:Patch}{L: KernelChoices}{U:Boxes G P L}{m':ℕ}{W:Alps Q T m' ε}{H:ChartRatio G}
lemma molds (he:Mold r R A n k): (n.val:ℝ)^k * ‖r-R‖≤ A:= he
lemma held_B (hp:LocalRatio H)(he:Paid P L U W H m 5 d r s)(hb:0≤r)(p:Muse G)(hx:Tide p d m v):
         let S:=subStud P L n; let B:=Vessel K V G n h; let O:= Chart.tangent G (Body 1 n); let η:=r*v/(n.val:ℝ); let M:= Paver.sculpt P L U W H s p d;
         ∀ l g, licensed S P.odd_side U W.clip W.live l W.sky g→∀ t:S.Choices,∀ Z:FibreRep S P.odd_side U t W g s,∀ x:Site n,∀ j:Phase, let f:= TracePay S P.odd_side U W t g H d p s x Z; Spectre B O ((skry f j)-(skry (inkM M d x) j)) k (η * censusE G K h (glideZ d) 2):=by
            intro S B O η M l g hK t Z x j f; let μ:=quart B O; have hs:0 ≤v:= Sack.coins ((hx 0).2 0); let r':=glideZ d; let n':ℝ:=n.val; have hn:0<n':=by unfold n'; exact_mod_cast n.pos
            obtain ⟨hpA,hH⟩:=he n l g hK t Z x p v hx
            let P':=skry f j-skry (inkM M d x) j
            have hz:Bond P':=by
                 let u:= inkM p d (S.ratio.embed x); have hh:ScriptJ.B f:= Fiber.predictB (F:=Z.L) hp (u ∘ ribz S P.odd_side) (fun i=> ((meridian _ _ _ _ _ hx) i).compLinear (ribz S P.odd_side).toLinearMap); exact (hh j).sub ((meridian _ _ _ _ _ hpA) j)
            apply Spectre.Ffoot ?_ (Stoam B O hz); let V'(u):=(1+‖spool G n u‖)^r'
            let a:=r*v/n'^5; have ha:0 ≤ a:= by unfold a; positivity
            have h':Fault μ 2 (a • V') (η*censusE G K h (glideZ d) 2):=by
                     have hv':= ((Borealis.Galea.Cane.scal (Eu_I V h (G:=G) (n:=n) (K:=K) r') a) 2 two_pos); refine hv'.mono le_rfl (le_of_eq ?_); rw [Pi.smul_apply, Pi.smul_apply, Real.norm_of_nonneg ha]; change a*(n'^4*_)=(r*v/n')*_; unfold a;field_simp; rfl
            refine h'.ofLe hz.smooth.continuous.aestronglyMeasurable (Eventually.of_forall fun i=>?_ )
            refine le_trans ?_ (Real.le_norm_self _); change ‖P' i‖≤ a*V' i; unfold a; rw[div_mul_eq_mul_div,le_div_iff₀ (by positivity),mul_comm]; exact hH i j -- hv
end
end YM.OPE.Ibis
