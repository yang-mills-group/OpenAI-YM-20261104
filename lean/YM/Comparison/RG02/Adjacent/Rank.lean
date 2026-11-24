import YM.Comparison.RG02.Adjacent.Parity
/-!
# Rank tensor basis consumes the Same sale formula; no chart size assumptions
 Input p in log x acquitted by its Level only. All motion/gauge charts same. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent
open Function Filter Finset MeasureTheory RG Lattice
open PertExtension.Series PertExtension.Series.Tested YM.Tensor
open Order Assembly Valence Moving Moving.Path Moving.Shift Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {G:Gauge}{c:Side}
variable {p:Display X} {m:ℕ→ℤ} {r:ℕ}
namespace Ranking
lemma impression {f:X→ℂ}(h:ContDiffAt ℝ ω f 0)(x:X): Aspiration (fun t:ℝ=> f (t•x)) (fun k=> Assembly.jet f k x) := by
   let L:ℝ→L[ℝ] X:= (ContinuousLinearMap.id ℝ _).smulRight x
   have he (k:ℕ) : motion (f ∘ L) k=Assembly.jet f k x:= by unfold motion; rw [Assembly.jet_continuous_right L (h.of_le le_top), show L 1=x from one_smul ℝ x] -- fix L reduc
   rw [← funext he]; exact ordinary (f:=f ∘ L) ((show ContDiffAt ℝ ∞ f (L 0) from L.map_zero.symm ▸ h.of_le le_top).comp _ L.contDiff.contDiffAt) -- at L 0≠def
lemma clip {f:X→ℂ}(h:ContDiffAt ℝ ω f 0)(k j:ℕ): Assembly.jet (Assembly.jet f k) j = if j=k then Assembly.jet f k else 0 := by
   have hp : ContDiff ℝ ω (Assembly.jet f k) := (levelJet h k).smooth
   funext x; have he: Aspiration (fun t:ℝ=> Assembly.jet f k (t•x)) (fun i=> if i=k then Assembly.jet f k x else 0) := by simp_rw [Clipper.weight]; exact Aspiration.single _ _
   rw [show Assembly.jet (Assembly.jet f k) j x=_ from congrFun ((impression hp.contDiffAt x).unique he) j]; split <;> rfl
lemma crop {f:X→ℂ}(h:ContDiffAt ℝ ω f 0)(k j:ℕ): iteratedFDeriv ℝ j (Assembly.jet f k) 0= if j=k then iteratedFDeriv ℝ j f 0 else 0:= by
   let L:= Assembly.jet f k; have hp:= (levelJet h k).smooth.contDiffAt (x:=0)
   have H(x:X):= congrFun (clip h k j) x
   have hc:Tensor.Sym (iteratedFDeriv ℝ j L 0):= YM.Analysis.sym_Jet (hp.of_le le_top)
   by_cases he:j=k; subst j; rw [if_pos rfl]; apply Tensor.ext_diag _ _ hc (YM.Analysis.sym_Jet (h.of_le le_top))
   · funext x; apply (smul_right_inj (show (k.factorial:ℝ)⁻¹ ≠ 0 from by positivity)).mp; change Assembly.jet (Assembly.jet f k) k x = Assembly.jet f k x; rw [clip h,if_pos rfl]
   rw [if_neg he]; apply Tensor.ext_diag _ _ hc (fun _ _=> rfl); funext x; change _=(0:ℂ); apply (smul_right_inj (show (j.factorial:ℝ)⁻¹≠0 from by positivity)).mp; change Assembly.jet L j x=_; unfold L; rw [clip h k j, if_neg he]; simp

variable (K:UnitCost)(d:ℤ){r:ℕ} (h:Charge r m p)
include h
lemma pay (k i:ℕ): iteratedFDeriv ℝ k (born p K d r i) 0= ∑ j∈range (r+1), motion (money K d j k) i • iteratedFDeriv ℝ k (p j) 0 := by
   let u (j n:ℕ) := motion (money K d j n) i • Assembly.jet (p j) n
   have ht j n (hk:j∈range (r+1)): ContDiffAt ℝ ω (u j n) 0:= ((levelJet ((h j (mem_range_succ_iff.mp hk)).smooth.contDiffAt) n).factor (motion (money K d j n) i)).smooth.contDiffAt
   rw [show born p K d r i= ∑ j∈range (r+1),∑ n∈range ((m j).toNat+1),u j n from funext fun x=> by rw [message K d r h]; simp_rw [Finset.sum_apply]; rfl, iteratedFDeriv_sum_apply]; swap; · intro j hj; rw [show (∑ n∈_,_)= (fun x=>∑ n∈range ((m j).toNat+1),u j n x) from funext fun x=> Finset.sum_apply ..]; exact ContDiffAt.sum fun n _=> (ht j n hj).of_le le_top
   apply Finset.sum_congr rfl; intro j hj
   have hu:= (h j (mem_range_succ_iff.mp hj)); let l:= range ((m j).toNat+1)
   rw [iteratedFDeriv_sum_apply (fun n _=> (ht j n hj).of_le le_top),sum_eq_single k]; unfold u; rw [iteratedFDeriv_const_smul_apply ((levelJet hu.smooth.contDiffAt k).smooth.contDiffAt.of_le le_top), crop hu.smooth.contDiffAt k k,if_pos rfl]
   · intro i hi hz; unfold u; rw [iteratedFDeriv_const_smul_apply ((levelJet hu.smooth.contDiffAt i).smooth.contDiffAt.of_le le_top), crop hu.smooth.contDiffAt i k,if_neg hz.symm,smul_zero]
   intro hk; have he : m j<k:= by simp only [mem_range] at hk; omega
   unfold u; rw [iteratedFDeriv_const_smul_apply ((levelJet hu.smooth.contDiffAt k).smooth.contDiffAt.of_le le_top),crop hu.smooth.contDiffAt _ _,if_pos rfl,hu.high k he,smul_zero]
lemma price (P : T X ℂ 2 →ₗ[ℂ] ℂ)(i:ℕ): P (iteratedFDeriv ℝ 2 (born p K d r i) 0)=∑ j∈ range (r+1),motion (money K d j 2) i * P (iteratedFDeriv ℝ 2 (p j) 0):= by rw [pay K d h, map_sum]; simp_rw [map_smul]; rfl
end Ranking
end YM.Comparison.RG02.Adjacent
