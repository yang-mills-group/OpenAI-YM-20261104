import YM.OPE.Compatible.Nock.Stripe
/-!
# Agreement of polynomial readings. No mixing infinite degree. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Flock
open Function Filter Lattice Laurent Tree Woody Weir MeasureTheory Exterior Bloch Cascade
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace
open RG Bid Pressure Precision FreeResolvent WithLp Next.Free Frequency
open PertExtension Series Asymptotics GaussianScore Radial Finset
variable {E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] [NormedAddCommGroup F][NormedSpace ℝ F][FiniteDimensional ℝ F]
omit [FiniteDimensional ℝ E] in lemma flat_dot (l:List (Dual' E)) :dotV l= Law.product l.get univ :=by
    induction l with
    | nil=>funext; simp [dotV, Law.product]
    | cons a t h=>
      rw [dot_cons,h]; funext x; simp only [Pi.mul_apply,Law.product]; exact (Fin.prod_univ_succ (fun i:Fin (t.length+1)=> ((a::t).get i) x)).symm
section
variable [MeasurableSpace E][BorelSpace E][MeasurableSpace F][BorelSpace F] (μ :Measure E) (ν:Measure F)
variable [μ.HasTemperateGrowth] [Measure.IsAddRightInvariant μ][NeZero μ] [ν.HasTemperateGrowth] [Measure.IsAddRightInvariant ν][NeZero ν]
variable (L:Law E)(P:Law F)(A:E→ₗ[ℝ] F)(hp:∀ k j:Dual' F,L.wick (k.comp A) (j.comp A) = P.wick k j)
include hp
lemma mapLine {ι:Type}(k:ι→ Dual' F)(s:Finset ι): P.average ν (Law.product k s) = L.average μ ((Law.product k s) ∘ A):=by
     let X(t:ι):= (k t).comp A; have hh (p:Finset ι): Law.product k p∘ A=Law.product X p:= rfl
     induction s using Finset.strongInduction with
     | _ s ih =>
       obtain rfl |⟨i,h⟩:= s.eq_empty_or_nonempty
       · rw [hh,show Law.product k ∅= 1 by funext i; simp [Law.product],show Law.product X ∅=1 by funext i;simp [Law.product],P.empty,L.empty]
       classical
       rw [hh, ← insert_erase h, slopeTest ν P k (s.erase i) i (notMem_erase _ _), slopeTest μ L X (s.erase i) i (notMem_erase _ _)]; exact sum_congr rfl fun j _=> congr_arg₂ _ ( (ih _ ((Finset.ssubset_of_subset_of_ssubset (erase_subset ..) (erase_ssubset h)))).trans (congr_arg _ (hh _))) (hp ..).symm
lemma meanFit (f: F→ℝ)(h:Bond f): P.average ν f=L.average μ (f ∘ A):=by
      apply Quilting.everything _ _ h (g:=fun f=> P.average ν f=L.average μ (f ∘ A)); constructor
      · intro l; rw [flat_dot, mapLine μ ν L P A hp]
      · intro f hf h c
        rw [show (c • f)∘ A=c • (f∘ A) from rfl,scooted,scooted];rw [h]
      intro f a hf ha hh H; rw [show (f+a) ∘ A=f ∘ A+a ∘ A from rfl,sun _ _ hf ha,sun _ _ (hf.compLinear A) (ha.compLinear A),hh,H]
end
section
variable (A:E≃ₗ[ℝ] F)(L: Law E)(R: Law F)(h:∀ x, L.P x x=R.P (A x) (A x))
include h
lemma dual_wick (k j:Dual' F): L.wick (k.comp A.toLinearMap) (j.comp A.toLinearMap) = R.wick k j := by
    have hh(x y): L.P x y=R.P (A x) (A y):=by
         have hv:=h (x+y); simp only [map_add,LinearMap.add_apply,L.turns y x,R.turns (A y) (A x),h x,h y] at hv; linarith
    let v:= k.comp A.toLinearMap
    have hv:L.P (A.symm (R.inverse k))=v:= LinearMap.ext fun i=> by rw [hh, A.apply_symm_apply,R.applies];rfl
    have hx: A (L.inverse v)= R.inverse k:=by rw [← hv,L.solves,A.apply_symm_apply]
    exact congr_arg j hx
end
end YM.OPE.Libra.Flock
