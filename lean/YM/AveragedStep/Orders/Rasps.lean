import YM.AveragedStep.Orders.Table
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Lattice RG Wilson Precision MeasureTheory Function Filter Tree Loops Set Metric
open scoped Topology BigOperators Matrix.Norms.Frobenius ENNReal Classical ContDiff
variable {c f:Side}{G:Gauge}{A:ChartRatio G}{S:StepData c f}
def chorus (S:StepData c f)(A:ChartRatio G)(τ:ℝ)(i:Rim c f)(v:G.Color)(n:ℕ)(Y:Hand G c f):ℝ :=
    ∑ k∈Finset.range (n+1),τ^k * tier S A i v k Y
lemma smooth_chorus (S:StepData c f)(A:ChartRatio G)(τ:ℝ)(i:Rim c f)(v:G.Color)(n:ℕ):ContDiff ℝ 1 (chorus S A τ i v n) :=
  ContDiff.sum (𝕜:=ℝ) (fun k _=> contDiff_const.mul (smooth_tier _ _ i v k))
lemma chorus_cost (P:Patch)(K:KernelChoices)(A:ChartRatio G)(v:G.Color)(d:ℕ):∃ B:ℝ,0≤B ∧ ∀ {c f:Side}(S:StepData c f),S.kernel=K → S.patch=P → ∀ (i:Rim c f)(Y:Hand G c f){r t:ℝ},1≤r → 0 ≤ t → t ≤ 1 → (∀ j∈home S i, ‖Y j‖ ≤ r) → |chorus S A t i v d Y| ≤ B*r^(d+1):=by
 choose B hb h using tier_cost P K A v
 refine ⟨∑ i∈Finset.range (d+1),B i, Finset.sum_nonneg fun i _=>hb i, fun {c f} S hS hK i Y {r t} hr ht hx hy=>?_⟩
 unfold chorus; rw [Finset.sum_mul]; apply (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum ?_); intro l hl; rw [abs_mul,abs_of_nonneg (pow_nonneg ht _)]
 exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ ht hx)).trans ((h l S hS hK i Y hr hy).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hr (Nat.add_le_add_right (Nat.le_of_lt_succ (Finset.mem_range.mp hl)) 1)) (hb _)))
private lemma sing (S:StepData c f)(τ:ℝ)(i:Rim c f)(v:G.Color)(n:ℕ)(Y:Hand G c f): chorus S A τ i v n Y =
    (∑ p∈owners S i, ∑ k∈ Finset.range (n+1),τ^k * tooth S.patch (K:=S.kernel) (sort p)
      (pick (S:=S) p (Pi.single i v)) (k+1) (pick (S:=S) p Y))-
    ∑ k∈Finset.range n,τ^(k+1)*gum A v k (Y i):=by
 unfold chorus tier backbone; simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum]; rw [Finset.sum_comm (s:=Finset.range (n+1)),Finset.sum_range_succ' (fun m:ℕ=>τ^m*(if m=0 then 0 else gum A v (m-1) (Y i)))]; simp

/- Shop on the cutoff-scaled potential entries, all volumes. Still a local
bound; pay radii and all coincidence multiplicities next. -/
lemma chorus_shops {P:Patch}{K:KernelChoices}(Q:Cuff P K A)(hA:LocalRatio A)
    (h:P.Branches K G)(v:G.Color)(d:ℕ):∃ B:ℝ,0≤B∧∀ {c f:Side}(S:StepData c f)(hP:S.patch=P)(hK:S.kernel=K)(i:Rim c f)(Y:Hand G c f){r t:ℝ},1≤r → 0<t → (∀ j∈home S i, ‖Y j‖≤r∧ ‖t • Y j‖ ≤ 2*Q.width) →
     let Q':Cuff S.patch S.kernel A:=hK.symm ▸ (hP.symm ▸ Q : Cuff S.patch K A)
     |(t⁻¹ * flame Q' i (t • Y) v - t*Cuff.haarScore (A:=A) (t • Y i) v) - chorus S A t i v d Y| ≤ B * t^(d+1)*r^(d+2):=by
 obtain ⟨B,hB,H⟩:=table_cauchy Q h v d
 obtain ⟨C,hC,J⟩:=gum_cost Q hA v d
 let U:=cap (aperture P) parcelCount
 refine ⟨U*B+C,by positivity,fun {c f} S hP hK i Y {r t} hr ht he=>?_⟩
 subst P K; dsimp only
 let L (p):=pick (S:=S) p Y
 let j (p:Parcel c f):= onBit (S:=S) p i
 have hh(p)(hp:p∈ owners S i):‖t • L p‖≤ 2*Q.width:=by rw [← pick_smul]; exact restrict_pick p i _ (by have :=Q.active; positivity) hp (fun i hi=> (he i hi).2)
 have hk(p)(hp:p∈ owners S i):‖L p‖≤ r:=restrict_pick p i _ (zero_le_one.trans hr) hp (fun i hi=> (he i hi).1)
 rw [sing]; unfold flame; simp_rw [bits_eq, pick_smul, Finset.mul_sum]
 let fw(p:Parcel c f):= (t⁻¹)*(bandD Q (sort p) (t • L p) (bits (j p) v))
 let g(p:Parcel c f):=∑ k∈Finset.range (d+1), t^k*tooth S.patch (K:=S.kernel) (sort p) (bits (j p) v) (k+1) (L p)
 let T:= t*Cuff.haarScore (A:=A) (t • Y i) v; let V:=∑ k∈Finset.range d,t^(k+1)*gum A v k (Y i)
 change |((∑ p∈owners S i, fw p) - T) - ((∑ p∈owners S i,g p)-V)| ≤ _
 have h' (p)(hp:p∈owners S i):|fw p-g p|≤ B*t^(d+1)*r^(d+2):=(H (sort p) (j p) _ _ ht (hh p hp)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hk p hp) _) (by positivity))
 rw [show ((∑ p∈owners S i, fw p) - T) - ((∑ p∈owners S i,g p)-V)=(∑ p∈owners S i,(fw p-g p))-(T-V) by rw [Finset.sum_sub_distrib]; ring,add_mul,add_mul]
 apply (abs_sub ..).trans (add_le_add ((Finset.abs_sum_le_sum_abs ..).trans ((Finset.sum_le_sum h').trans ?_)) ?_)
 · rw [Finset.sum_const,nsmul_eq_mul,mul_assoc,mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast owned S i) (by positivity) -- assoc mismatch?
 apply (J _ _ ht (he i (home_self S i)).2).trans (mul_le_mul_of_nonneg_left _ (by positivity))
 exact (pow_le_pow_left₀ (norm_nonneg _) (he i (home_self S i)).1 _).trans (pow_le_pow_right₀ hr (Nat.le_add_right ..))
end YM.AveragedStep
