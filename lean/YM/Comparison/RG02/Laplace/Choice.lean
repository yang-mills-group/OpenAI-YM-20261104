import YM.Comparison.RG02.Laplace.Facing
/-!
# Pinning the tree tag and discharging gauge-independence of the Fk rule

 Vary g at fixed step (varying only portal auxiliary arguments). Weight is
 explicitly known function of g>0; aperture estimates chart-analytic. Use uniqueness
 of polarized jets *for every announced horizon*. A can depend on r. Consequently
 Fk itself on the torus is canonical in this branch independent of both
 t and the physical forest. Commutation with orientation/spatial cutoff not
 implied (call density Transport for those structures).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Laplace
open Function Filter Finset MeasureTheory ProbabilityTheory RG Precision Lattice Wilson Exterior Tree
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Actual
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V}
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (F H : Forest S.ratio) (t : S.Choices) (g c₀:ℝ)
  (W : Bulk.Colors R G f) (x : fieldDir G c 1)
variable (D : BudgetPoint) (r : ℕ)
variable (hW : Bulk.Well W)
local notation "Z"=> Next.Fluctuations.Sector.prefactor S G (temperature g)
-- office/wage factors: rho (τ) independent of g

def common (S : StepData c f) (g : ℝ) (F : Forest S.ratio) (G : Gauge) :=
   g ^ Fintype.card (Key F G) * Next.Fluctuations.Sector.prefactor S G (temperature g)
def pad := Gaussian.coat (K.covariance F t) * (tab (O:=O) (F:=F)*calorie K F t c₀ x) / count S
lemma wages (h : 0<g): wage K F t g c₀ x=common S g F G*pad K F t c₀ x := by unfold pad common wage office standard; rw [chartCost_eq .., ← mul_div_assoc]; swap; exact h; ring
lemma common_independent : common S g F G=common S g H G := by unfold common Key; rw [Fintype.card_prod,Fintype.card_prod, Work.F05.free_card F H]
lemma common_free (h : 0<g) : 0<common S g F G := mul_pos (pow_pos h _) (Next.Fluctuations.Sector.prefactor_pos _)
lemma pad_pos : 0<pad K F t c₀ x := by apply div_pos; exact mul_pos (Gaussian.coat_pos (K.positive F t)) (mul_pos (pow_pos K.ratio.scale _) (Real.exp_pos _)); exact Nat.cast_pos.mpr count_pos

include D hW
lemma identical : pad K F t c₀ x=pad K H t c₀ x ∧ Bulk.Fk K F t W x r=Bulk.Fk K H t W x r := by
   obtain ⟨A,hA,wA,hAA⟩:= both K F H c₀ W x D r hW
   let B:=Profiles.reroute F H G '' A
   obtain ⟨hB,hHB,ht⟩:= (show B∈𝓝 1 ∧ IsOpen B ∧ _ from hAA)
   let U:=Bulk.Fk K F t W x r; let V:=Bulk.Fk K H t W x r
   have hv (s): ∀ i≤r,(pad K F t c₀ x:ℂ)*detail U s i=(pad K H t c₀ x:ℂ)*detail V s i:= by
       obtain ⟨he,hh⟩:= ht t s
       let a:=fun g=> (portal K F t c₀ W x (fun _=> A) g).part s
       let b:=fun g=> (portal K H t c₀ W x (fun _=> B) g).part s
       let F' : ℂ:= pad K F t c₀ x; let H' : ℂ:= pad K H t c₀ x
       change ∀ i≤ r, (F' • detail U s) i=(H' • detail V s) i
       let w:= trial_scale F' (f:=a) (he A (Set.Subset.refl _) wA.measurableSet hA).2
       refine trial_gap (trial_congr (y:=H' • b) ?_ w) (trial_scale H' (hh B (Set.Subset.refl _) hHB.measurableSet hB).2)
       filter_upwards [eventually_pos] with g hg
       have hv:= redirects K F H g c₀ _ x hW A t hg
       rw [wages K F t g c₀ x hg,wages K H t g c₀ x hg, common_independent (G:=G) F H g] at hv
       have hC:= congrArg (fun q=> (Poly.part q s)) hv
       simp_rw [Poly.part_smul,Complex.ofReal_mul,mul_assoc] at hC
       exact mul_left_cancel₀ (show (↑(common S g H G):ℂ)≠0 from Complex.ofReal_ne_zero.mpr (common_free H g (G:=G) hg).ne') hC
   have hp:= hv R.quiet 0 (Nat.zero_le _)
   rw [tests_origin _ (Bulk.fk_unit K F ..),tests_origin _ (Bulk.fk_unit K H ..),mul_one,mul_one,Complex.ofReal_inj] at hp
   refine ⟨hp, (sym_coeff _ _ (Bulk.fk_sym ..) (Bulk.fk_sym ..)).2 ?_⟩
   intro i hi; ext s
   have hs:=hv s i hi; rw [hp] at hs
   exact mul_left_cancel₀ (show (↑(pad K H t c₀ x):ℂ)≠0 from Complex.ofReal_ne_zero.mpr (pad_pos ..|>.ne')) hs

lemma unique_θ (t' : S.Choices) : Bulk.Fk K F t W x r=Bulk.Fk K H t' W x r := by
   rw [← Bulk.fkChoice K H t _ _ _ t']
   exact (identical K F H t 0 W x D r hW).2
end YM.Comparison.RG02.Laplace
