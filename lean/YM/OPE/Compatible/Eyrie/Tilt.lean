import YM.OPE.Compatible.Eyrie.Hill
import YM.Extra.SOURCE_HISTORIES.Play
/-! # Push one or many from k in genuine unnormalized form. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Eyrie
open Function Filter MeasureTheory Spec Lattice RG Wilson Source Cov Allot MergeProof Next.Extract Dash Analysis Extra.Histories Next.Rank
open Push.GridApprox Motion
open scoped Topology BigOperators Classical
variable {d k m N p M:ℕ}{o:Side}{G:Gauge}(A:History G)(h:A.Selected)
local notation "P0"=>A.S.side N p
variable (hp:k ≤ N) (hT:k<N)
variable (U V:lots G (A.S.side N p))(hu:Continuous U)(hv:Continuous V)
include hu
-- naturality and signs
lemma soot : Integrable (illum (A.β N p N) U) (prior G P0):= (lite U hu).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
omit hu in
lemma bulb {a:ℕ}(ht:k+1 ≤ a) (F:lots G (A.S.side a p)): pushTo A N p ((Nat.le_add_right k 1).trans ht) F=(A.levels.clock.op k p).push (A.β N p (k+1)) (pushTo A N p ht F):=by
        induction a,ht using Nat.le_induction with
        | base=> rw [pushTo_next A N p (le_refl k),pushTo_self,pushTo_self]
        | succ m hm ih=> rw[pushTo_next A N p ((Nat.le_add_right k 1).trans hm), pushTo_next A N p hm,ih]
lemma PuffS (d:ℕ): puff A N p d U hT.le= blast A N p k d (puff A N p d U hT):=by
        let Y:=illum (A.β N p N) U; unfold blast puff; rw [StepData.push_smul _ _ _ _ (pushTo_integrable A N p hT _ (soot A U hu)), show (A.S.a k:ℂ)= (((A.S.block k).val:ℂ))*(A.S.a (k+1):ℂ) from ?_,mul_pow,mul_smul, bulb A hT Y (N:=N)] -- rhs ordering
        rw [A.S.a_step,Complex.ofReal_div,Complex.ofReal_natCast,mul_div_cancel₀]; exact_mod_cast (A.S.block k).property.ne'
lemma Opal (d:ℕ)(b:ℂ): puff A N p d (b • U) hp=b • puff A N p d U hp:=by
        induction hp using Nat.decreasingInduction with
        | self=> simp only [puff,pushTo_self]; ext1 x; simp only [Pi.smul_apply,illum,smul_eq_mul]; ring
        | of_succ m hm ih=> rw [PuffS A hm (b • U) (hu.const_smul b),PuffS A hm U hu, ih]; unfold blast; unfold puff; rw [StepData.push_smul _ _ _ _ ((pushTo_integrable A N p hm _ (soot A U hu)).smul _), smul_comm]
lemma twig (d:ℕ)(v:Motion) : puff A N p d (dance v U) hp=dance v (puff A N p d U hp):=by
        induction hp using Nat.decreasingInduction with
        | self=> simp only [puff,pushTo_self]; ext1 x; simp only [Pi.smul_apply,illum,smul_eq_mul]; simp only [dance,Pi.smul_apply,smul_eq_mul,illum,scalar_mul,bare_pull,scalar_real]; unfold scalar;split <;> simp only [star_pow, Complex.star_def, Complex.conj_ofReal]
        | of_succ m hm ih=>
             have hp:Continuous (dance v U):=by unfold dance scalar; split; exact (hu.comp (continuous_pull ..)).star; exact hu.comp (continuous_pull ..)
             rw [PuffS A hm (dance v U) hp,PuffS A hm U hu, ih]; exact blast_dance A _ _ _ _ v (puff A N p d U hm) ((pushTo_integrable A N p hm _ (soot A U hu)).smul _)
include hv
lemma WaveF (d:ℕ): puff A N p d (U+V) hp=puff A N p d U hp+puff A N p d V hp:=by
        induction hp using Nat.decreasingInduction with
        | self=> simp only [puff,pushTo_self]; ext1 x; simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,illum]; ring
        | of_succ m hm ih=> rw [PuffS A hm _ (hu.add hv),PuffS A hm _ hu,PuffS A hm _ hv,ih]; unfold blast; unfold puff; rw [StepData.push_add (A.levels.transition_mass m _ _) _ _ ((pushTo_integrable A N p hm _ (soot A U hu)).smul _) ((pushTo_integrable A N p hm _ (soot A V hv)).smul _),smul_add]
-- currents at every actual level
end YM.OPE.Eyrie
