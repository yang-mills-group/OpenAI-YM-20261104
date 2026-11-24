import YM.Comparison.RG02.Laplace.Inside
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Laplace.Prism
open Function Filter Finset MeasureTheory
open YM.Marker YM.Multi Order Assembly Actual YM.Lattice YM.Tree
open YM.Precision YM.Next.SectorChange
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff ENNReal
variable {G : Gauge} {V : Type} [DecidableEq V] {R : Census V}
variable {I : Type} [Fintype I] [DecidableEq I]
/-! # General analytic input around the chapter core frame

Can ask for any linear projection slice with fixed counting covariance & gauge charges,
not estimating anything about uniformity here. Generalization of `Laplace.Fields` etc,
consumes the same `Assembly` protocol. Use V × Gauge enlarged parameters later.
-/
open Gaussian PertExtension.Series PertExtension.Series.Tested ProbabilityTheory
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Q : Gaussian.Table I} {f : E→ℝ} {l : Hot R→ℕ} {F : Hot R→E→ℂ}
variable (y : E) (L : (I→ℝ)→ₗ[ℝ] E)
local notation "Λ"=> I→ℝ
local notation "ζ" => Assembly.translate y L
local notation "μ"=> Gaussian.cloud Q

abbrev size (v:I→ℝ) := Radial.zone.w (ζ v)
abbrev Fits (δ : ℝ) (A : ℝ→Set (I→ℝ)) : Prop := ∀ᶠ g in along, ∀ v ∈ A g,g*size y L v ≤ δ
def Major (A : ℝ→Set (I→ℝ)): Prop:= ∃ ε:ℝ, 0 < ε ∧ ∀ᶠ g in along, ∀ v ∉ A g, ε ≤ g*size y L v
abbrev visit (f : ℝ→Lit R (I→ℝ)) (A : ℝ→Set (I→ℝ)) := fun t=> (A t).indicator (f t)

omit [Fintype I] [FiniteDimensional ℝ E] [DecidableEq I] in
lemma size_pos (v : Λ) : 0<size y L v := zero_lt_one.trans_le (le_add_of_nonneg_right (norm_nonneg _))

-- `L¹` cost (for analyzing polynomials not a statement about density).
omit [FiniteDimensional ℝ E] [DecidableEq I] in
@[fun_prop] lemma continuous_ζ : Continuous ζ := by unfold Assembly.translate; exact continuous_const.add L.continuous_on_pi
private lemma whorizon (Q : Gaussian.Table I) : ∃ r:ℝ, 0<r ∧ ∀ p:ℕ, Integrable (fun v=> (size y L v)^p* Radial.shade r (ζ v)) (cloud Q) := by
   letI:= gauss_table Q
   letI : MeasurableSpace E:= borel _
   haveI : BorelSpace E:= ⟨rfl⟩
   let m' := (cloud Q).map ζ
   let T := L.toContinuousLinearMap
   have hT:= continuous_ζ y L
   haveI : IsGaussian m':= by
      unfold m'
      rw [show (cloud Q).map ζ=((cloud Q).map T).map (y+·) by rw [Measure.map_map (show Measurable (y+·) by fun_prop) T.continuous.measurable]; rfl]; infer_instance
   obtain ⟨C,hC,H⟩:= IsGaussian.exists_integrable_exp_sq m'; let r:= C/2
   have hr : 0<r:= half_pos hC; refine ⟨r,hr,fun p=>?_⟩
   let f (x : E):= (1+‖x‖)^p * Radial.shade r x
   have hc:Continuous f:= by unfold f Radial.shade; fun_prop
   obtain ⟨a,ha,h⟩:= Radial.bounded_exp hr p
   have he : Integrable f m' := (H.const_mul a).mono' hc.aestronglyMeasurable (Eventually.of_forall fun z=>by
      have hp : 0 ≤ f z:= by unfold f Radial.shade; positivity
      rw [Real.norm_of_nonneg hp]
      have hh:=h ‖z‖ (norm_nonneg _)
      calc
       _ = (1+‖z‖)^p * Real.exp (-r*‖z‖^2) * Real.exp (C*‖z‖^2) := by unfold f Radial.shade; rw [mul_assoc,← Real.exp_add]; unfold r; ring_nf
       _ ≤ _ := mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le)
   exact he.comp_aemeasurable hT.measurable.aemeasurable

section zonal
variable (r : ℕ) (s : R.Mode) {c : ℝ} {ψ : ℝ→E→Poly R} {π : E→ PTable R}
variable [Fintype V] (hψ : ∀ c:ℝ, 0<c → Zonal (Radial.zone (E:=E)) (Radial.shade c) ψ π)
include hψ
def picture (π : E→ PTable R) (g : ℝ) (v : I→ℝ) : Poly R := Order.value (g:ℂ) (series R r (π (ζ v)))
private def v_one (ψ : ℝ→E→Poly R) : ℝ→Lit R (I→ℝ):= fun t v=> ψ t (ζ v)
variable (Q)
include Q in
lemma crop : ∃ δ : ℝ,0 < δ ∧ ∀ A, Fits y L δ A → Bill (r+1) (fun g=> (charge μ (visit (v_one y L ψ-picture y L r π) A g)).part s) := by
   obtain ⟨c,hC,he⟩:=whorizon y L Q
   let paid := Radial.shade (E:=E) c
   obtain ⟨δ,C,p,hδ,H,h⟩:= (Assembly.Zonal.remainder _ (hψ c hC) s r).cost
   let M (v : Λ):= size y L v ^ p * paid (ζ v)
   have hm (v:Λ): 0 ≤ M v := mul_nonneg (pow_nonneg (size_pos ..).le _) (Real.exp_pos _).le
   refine ⟨δ,hδ,fun A ha=> ?_⟩; apply volume_bill (r+1) s hm (he p) C H
   filter_upwards [Tested.eventually_pos,ha] with t' ht hF v
   by_cases hv : v∈ A t'
   · unfold visit; rw [Set.indicator_of_mem hv, Pi.sub_apply,Pi.sub_apply, Extra.Trajectories.part_sub]; refine (h (ζ v) t' ht (hF v hv)).trans_eq ?_
     unfold M paid; ring
   unfold visit; rw [Set.indicator_of_notMem hv,Poly.part_nil, norm_zero]
   exact mul_nonneg (mul_nonneg H (pow_nonneg ht.le _)) (hm _)

omit [DecidableEq I] [Fintype I] [FiniteDimensional ℝ E] in
lemma budget : ∃ p : ℕ, ∃ C:ℝ, 0 ≤ C ∧ ∀ g:ℝ, |g|≤1 → ∀ v : I→ℝ, ‖(picture y L r π g v).part s‖ ≤ C*size y L v^p := by
   let f := Assembly.rows π s
   let q := Radial.zone (E:=E)
   have hu n : q.Invoice (fun x=> ‖f n x‖):= ((hψ 1 zero_lt_one s).invoice n).norm
   obtain ⟨C,p,hC,H⟩:= Zone.Invoice.fin_sum (range (r+1)) (fun n x=> ‖f n x‖) (fun n _=> hu n)
   refine ⟨p,C,hC,fun g h v=>?_⟩
   have hv : (picture y L r π g v).part s=Zone.eval f r g (ζ v) := Assembly.Zonal.zone_eval ..
   have he i : ‖(g^i • f i (ζ v))‖ ≤ ‖f i (ζ v)‖:= by rw [norm_smul,norm_pow]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) h)
   rw [hv]; refine (norm_sum_le ..).trans ((sum_le_sum fun i _=> he i).trans ?_)
   have hz:= H (ζ v); simp_rw [Finset.sum_apply,Real.norm_eq_abs, abs_of_nonneg (show 0≤∑ i∈ Finset.range (r+1), ‖f i (ζ v)‖ from by positivity)] at hz; exact hz

lemma remit {A} (h : Major y L A) (k : ℕ) : Bill k (fun g=> (charge μ ((A g)ᶜ.indicator (picture y L r π g))).part s) := by
  obtain ⟨C,hC,H⟩:= whorizon y L Q
  obtain ⟨p,m,hm,Hm⟩:= budget y L r s hψ
  obtain ⟨ε,hε,Hε⟩:=h
  let B v:=size y L v^(p+k)*Radial.shade C (ζ v)
  have hb (v : Λ) : 0≤ B v := mul_nonneg (pow_nonneg (size_pos ..).le _) (Real.exp_pos _).le
  apply volume_bill k s hb (H (p+k)) (m/ε^k) (by positivity)
  filter_upwards [Tested.eventually_small (show 0<(1:ℝ) from zero_lt_one), Hε] with g hg he v
  have hp:= hg.1
  let w := size y L v; have hw : 0<w := size_pos y L v
  by_cases h : v∈ A g
  · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr h),Poly.part_nil, norm_zero]; exact mul_nonneg (by positivity) (hb _)
  have he := he v h; have hy : 1 ≤ Radial.shade C (ζ v):= Real.one_le_exp (by positivity)
  rw [Set.indicator_of_mem (Set.mem_compl h)]
  calc
    _ ≤ m*w^p := Hm g (by rw [abs_of_nonneg hp.le]; exact hg.2.le) v
    _ ≤ (m*w^p) * (g*w/ε)^k := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by rw [one_le_div hε]; exact he))
    _ ≤ _ := by
       apply le_trans (b:=(m*w^p)*(g*w/ε)^k*Radial.shade C (ζ v))
       · exact le_mul_of_one_le_right (by positivity) hy
       unfold B w; rw [pow_add]; simp_rw [div_pow,mul_pow,div_eq_mul_inv]; exact Eq.le (by ring)

lemma pays (P : Grade R r) (H : ∀ g:ℝ, Good μ (picture y L r π g) ∧ charge μ (picture y L r π g)=Order.value (g:ℂ) P) :
    ∃ δ:ℝ, 0 < δ ∧ ∀ A, Fits y L δ A → Major y L A →
      (∀ᶠ g in along, MeasurableSet (A g) ∧ Good μ ((A g).indicator (ψ g ∘ ζ))) →
        Trial (detail P s) (fun g=> (charge μ ((A g).indicator (ψ g ∘ ζ))).part s) r := by
   obtain ⟨δ,hδ,Hδ⟩:=crop Q y L r s hψ
   refine ⟨δ,hδ,fun A h m ha=>?_⟩; refine bill_congr ?_ (bill_add (Hδ A h) (bill_neg (remit Q y L r s hψ m (r+1))))
   filter_upwards [ha] with t he; unfold visit
   change (charge μ ((A t).indicator ((ψ t ∘ ζ)- (picture y L r π t)))).part s + -_ =_
   rw [Set.indicator_sub', sub_cost he.2 ((H _).1.on_window he.1)]
   simp only [Extra.Trajectories.part_sub,Pi.sub_apply,tests,←(H _).2]
   rw [split_cost (H _).1 he.1, Poly.part_plus]; abel
end zonal

variable [Fintype V]

local notation "fκ"=>Assembly.numeric l F f
local notation "Qϑ"=>Assembly.prescription y L l F f Q
lemma squeeze (r : ℕ) (s:R.Mode) (hQ:Q.PosDef) (hi : Q.IsSymm) (h : Assembly.Admissible l F f) :
    ∃ δ:ℝ, 0 < δ ∧ ∀ A, Fits y L δ A → Major y L A →
      (∀ᶠ g in along, MeasurableSet (A g) ∧ Good μ ((A g).indicator (Assembly.numeric l F f g ∘ ζ))) →
        Trial (detail (Assembly.prescription y L l F f Q hi r) s) (fun g=> (charge μ ((A g).indicator (Assembly.numeric l F f g ∘ ζ))).part s) r := by
   apply pays Q y L r s (π:=Assembly.expansions l F f) (fun _ hF => Assembly.radial_comparison l F f h hF); intro g
   have he:=moment_integral y L l F f Q hi hQ r (g:ℂ); refine ⟨fun s=> (he s).1,?_⟩; ext i; exact (he i).2.symm
end YM.Comparison.RG02.Laplace.Prism
