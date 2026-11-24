import YM.AveragedStep.Orders.Template
import YM.AveragedStep.Moments.Trophy
/-! The independent (from the represented densities and physical answer)
formal conditional Wilson score coefficients. The Haar terms use the
prescribed fixed exponential ratio A (keep coefficient convention, NO 2π
or angular terms); restricted output only. -/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Lattice RG Wilson Precision MeasureTheory Function Filter Tree Loops Set Metric
open scoped Topology BigOperators Matrix.Norms.Frobenius ENNReal Classical ContDiff
variable {c f:Side}{G:Gauge}{A:ChartRatio G}{S:StepData c f}

-- No Cuff argument anywhere in level and all coefficients. Based on actual elected StepData INPUT
-- grammar and prescribed geometry and Haar convention. Connector uses all
-- same addresses. Not yet claiming equality with any position-scheme normalized coefficient.
-- WP3 exercise integration-by-parts Wilson diagram definition on this table.
def backbone (S:StepData c f)(i:Rim c f)(v:G.Color)(n:ℕ)(Y:Hand G c f):ℝ :=
    ∑ p∈owners S i, tooth S.patch (K:=S.kernel) (sort p) (pick (S:=S) p (Pi.single i v)) (n+1)
         (pick (S:=S) p Y)
def tier (S:StepData c f)(A:ChartRatio G)(i:Rim c f)(v:G.Color)(n:ℕ)(Y:Hand G c f):ℝ:=
     backbone S i v n Y - if n=0 then 0 else gum A v (n-1) (Y i)

-- common bounds on the finite template types (i.e. at this point not
-- allowed to charge their Stirling/sector factors at another P or K).
variable {P:Patch}{K:KernelChoices}
def bits(d: Finset (Interior P))(v:G.Color):Vectors P G:=fun x=>if x∈d then v else 0
def onBit(p:Parcel c f)(i:Rim c f):= Finset.univ.filter fun z:Interior S.patch=> hook S p z = some i
lemma bits_eq(p:Parcel c f)(i:Rim c f)(v:G.Color):pick (S:=S) p (Pi.single i v)= bits (onBit (S:=S) p i) v := by
 funext z
 unfold pick bits onBit; cases he:hook S p z with
 | none=> simp [Option.elim,he]
 | some j=> by_cases h:j=i <;> simp [Option.elim,h,he]
lemma smooth_pick (p:Parcel c f):ContDiff ℝ 1 (pick (G:=G) (S:=S) p):= contDiff_pi.mpr fun i=> by
 unfold pick; cases hook S p i; · exact contDiff_const
 exact contDiff_apply ..
lemma smooth_tier (S:StepData c f)(A:ChartRatio G)(i:Rim c f)(v:G.Color)(n:ℕ):ContDiff ℝ 1 (tier S A i v n):=by
 unfold tier; refine ContDiff.sub ?_ ?_
 · exact ContDiff.sum (fun p _=> (radial_jet _ _).comp (smooth_pick p))
 by_cases h:n=0; · simpa only [if_pos h] using (contDiff_const (c:=0) (𝕜:=ℝ) (E:=Hand G c f) (F:=ℝ) (n:=1))
 simp only [if_neg h]; exact (radial_jet ..).comp (contDiff_apply ..)

private lemma common_sum {I:Type}[Fintype I] {H:I→ℝ→Prop}(hm:∀ i r t,H i r→ r≤t→ H i t)(h:∀ i,∃ C,0≤C∧H i C):∃ C,0≤C∧∀ i,H i C:=by
 choose C he h using h; exact ⟨∑ i,C i,Finset.sum_nonneg (fun i _=>he i),fun i=> hm i (C i) _ (h i) (Finset.single_le_sum (fun j _=>he j) (Finset.mem_univ _))⟩
lemma table_bound (P:Patch)(K:KernelChoices)(v:G.Color)(n:ℕ):∃ C:ℝ,0≤C∧ ∀ a (d:Finset (Interior P)) Z, |tooth P (K:=K) a (bits d v) n Z|≤C*‖Z‖^n := by
 obtain ⟨C,hC,H⟩:=common_sum (I:=Mold × Finset (Interior P)) (H:=fun i C=>∀ Z:Vectors P G, |tooth P (K:=K) i.1 (bits i.2 v) n Z|≤ C*‖Z‖^n) (fun i B C he hZ Z=> (he Z).trans (mul_le_mul_of_nonneg_right hZ (by positivity))) (fun _=> charged _ n)
 exact ⟨C,hC,fun a d Z=>H (a,d) Z⟩
lemma table_cauchy(Q:Cuff P K A)(h:P.Branches K G)(v:G.Color)(n:ℕ):
    ∃ B:ℝ, 0≤B∧ ∀ a:Mold,∀ d:Finset (Interior P), let i:=bits d v
    ∀(Z:Vectors P G)(t:ℝ), 0<t → ‖t • Z‖ ≤2*Q.width →
     |t⁻¹*bandD Q a (t • Z) i -∑ j∈Finset.range (n+1),t^j *tooth (K:=K) P a i (j+1) Z|≤B*t^(n+1)*‖Z‖^(n+2):=by
 obtain ⟨B,hB,H⟩:=common_sum (I:=Mold× Finset (Interior P)) (H:=fun i B=> ∀ Z:Vectors P G,∀ t:ℝ,0<t → ‖t • Z‖ ≤ 2*Q.width→
     |t⁻¹*fderiv ℝ (chip P K i.1 (canon P)) (t • Z) (bits i.2 v) -∑ j∈Finset.range (n+1),t^j *tooth (K:=K) P i.1 (bits i.2 v) (j+1) Z|≤ B*t^(n+1)*‖Z‖^(n+2))
     (fun i r t hK h Z τ hτ hA => (hK Z τ hτ hA).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h (by positivity)) (by positivity))) (fun x=> tooth_cost Q h x.1 _ n)
 refine ⟨B,hB,?_⟩; intro a d i Z t h ht; unfold bandD; rw [if_pos ht]; exact H (a,d) Z t h ht

lemma restrict_pick (a:Parcel c f)(e:Rim c f)(Y:Hand G c f){R:ℝ}(hr:0≤R)(ha:a∈owners S e)(h:∀ i∈home S e, ‖Y i‖≤R): ‖pick (S:=S) a Y‖≤R:=by
 refine (pi_norm_le_iff_of_nonneg hr).mpr fun i=>?_; unfold pick; cases he:hook S a i; · simpa [Option.elim] using hr
 next i=> exact h i (home_owner S ha (land_mem S he))
lemma pick_smul (a:Parcel c f)(Y:Hand G c f)(t:ℝ):pick (S:=S) a (t • Y)=t • pick (S:=S) a Y:=by
 funext i; unfold pick; cases he:hook S a i <;> simp [Option.elim,he]

lemma tier_cost(P:Patch)(K:KernelChoices)(A:ChartRatio G)(v:G.Color)(n:ℕ):∃ B:ℝ,0≤B∧ ∀{c f:Side} (S:StepData c f),S.kernel=K → S.patch=P → ∀(i:Rim c f)(Y:Hand G c f){r:ℝ},1≤r→(∀ j∈home S i,‖Y j‖≤r)→|tier S A i v n Y|≤ B*r^(n+1):=by
 obtain ⟨B,hB,H⟩:=charged (n:=n-1) (fun u=> Cuff.haarScore (A:=A) u v)
 obtain ⟨C,hC,h⟩:= table_bound P K v (n+1)
 let U:=cap (aperture P) parcelCount
 refine ⟨U*C+B,by positivity,fun {c f} S hK hS i Y {r} hr hh=>?_⟩
 have he:0≤r:=zero_le_one.trans hr
 unfold tier backbone
 apply (abs_sub _ _ |>.trans ?_) -- abs_sub yields ?
 subst P K
 rw [add_mul]
 apply add_le_add
 · simp_rw [bits_eq]; apply (Finset.abs_sum_le_sum_abs ..).trans
   calc
     _ ≤ ∑ _p∈owners S i,C*r^(n+1):= Finset.sum_le_sum (fun p hp=> (h _ _ _).trans <| mul_le_mul_of_nonneg_left
             (pow_le_pow_left₀ (norm_nonneg _) (restrict_pick p i Y he hp hh) _) hC)
     _ ≤ _:=by simp only [Finset.sum_const,nsmul_eq_mul,mul_assoc]; gcongr; exact owned S i
 split; · rw [abs_zero]; positivity
 apply (H (Y i)).trans (mul_le_mul_of_nonneg_left _ hB)
 apply (pow_le_pow_left₀ (norm_nonneg _) (hh i (home_self S i)) _).trans (pow_le_pow_right₀ hr _)
 omega
end YM.AveragedStep
