import YM.Integration.ActualNormalizedRayJets
import YM.Integration.NativePaidPacketColors
import YM.Comparison.RG02.Valence.Amplify

/-! Exact marked RG02 Taylor coefficient at every original signed Laurent power. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedFormalPowerLayers
open Function Filter Finset Set Lattice Wilson RG Marker Precision Tree Exterior Multi LocalComparison
open Comparison.RG02 Comparison.RG02.Order Comparison.RG02.Assembly Comparison.RG02.Cumulants Next.Rank NativePaidPacketColors
open scoped BigOperators Classical Topology ContDiff

private theorem shifted_grade {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ×E→ℂ} (hf : ContDiffAt ℝ ω f 0) (b : ℕ) : GradeAt b (fun u : ℝ×E=>u.1^b • f u) := by
  have h0 : GradeAt 0 f := ⟨hf,fun j h=>False.elim (Nat.not_lt_zero j h)⟩
  exact (GradeAt.shifts (fun u : ℝ×E=>u.1) contDiffAt_fst rfl b).scale h0

/-- The original unit coupling turns a stored prefactor into its exact Taylor order shift. -/
theorem shifted {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ×E→ℂ}
    (hf : ContDiffAt ℝ ω f 0) (b k : ℕ) (v : ℝ×E) (hv : v.1=1) :
    Assembly.jet (fun y : ℝ×E=>y.1^b • f y) k v = if b≤k then Assembly.jet f (k-b) v else 0 := by
  obtain ⟨t,A⟩ := v
  change t=1 at hv
  subst t
  have H := shifted_grade hf b
  by_cases hk : b≤k
  · rw [if_pos hk]
    let L : ℝ→L[ℝ] ℝ×E := ContinuousLinearMap.toSpanSingleton ℝ (1,A)
    have e (u : ℝ) : L u=(u,u • A) := by simp [L]
    have he : ContinuousAt (f ∘ L) 0 := hf.continuousAt.comp_of_eq L.continuous.continuousAt L.map_zero
    have hpun : ∀ᶠ u : ℝ in 𝓝[≠]0,(f ∘ L) u=(u^b)⁻¹ • ((u,u • A).1^b • f (u,u • A)) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hn : u≠0 := by simpa using hu
      simp only [Function.comp_apply,e,smul_smul,inv_mul_cancel₀ (pow_ne_zero b hn),one_smul]
    have h := ActualNormalizedRayJets.joint_coefficient H A he hpun (k-b)
    rw [Nat.add_sub_of_le hk] at h
    exact h.symm.trans (by simpa [L] using jet_continuous_right L (hf.of_le le_top) (1:ℝ))
  · rw [if_neg hk]
    exact H.jet_z _ (Nat.lt_of_not_ge hk)

private theorem jet_sum {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s : Finset I)
    (f : I→E→ℂ) (h : ∀i∈s,ContDiffAt ℝ ω (f i) 0) (n : ℕ) (v : E) :
    Assembly.jet (fun y=>∑i∈s,f i y) n v=∑i∈s,Assembly.jet (f i) n v := by
  unfold Assembly.jet
  rw [iteratedFDeriv_fun_sum_apply (fun i hi=>(h i hi).of_le le_top)]
  simp [smul_sum]

variable {V : Type} [DecidableEq V] {R : Census V} {G : Gauge} {c f : Side}
    {D : V→ ComparisonDensity.Address.Orbit} {P : MarkedPackets D G f R} {S : StepData c f} (F : Forest S.ratio)
    {p : BudgetPoint} {ad : V→Support f} {reg : Comparison.Density.Testing.Region (fun v=>(D v).Mood) f}
    {w : V→ℝ} {g width budget : ℝ} {off slope : ℕ}
    (H : P.Paid p ad reg w g width budget off slope) (hg : g≠0)

/-- The genuine whole field function of one independently marked and charged original power stratum. -/
def fiber (P : MarkedPackets D G f R) (x : TestSpace D) (s : Hot R) (z : ℤ) (v : Bulk.Joint S F (G:=G)) : ℂ :=
  NativePaidPacketSeries.value P s.val z x (Work.F03.live F v.2)

include H hg in
theorem analytic (x : TestSpace D) (s : Hot R) (z : ℤ) : ContDiffAt ℝ ω (fiber F P x s z) 0 := by
  have h := NativePaidPacketSeries.value_grade H hg s.val ((hot_iff_ne _).1 s.property) z x
  have h' := h.coarse (g:=fun y : ℝ×fieldDir G f 1=>y.2) contDiffAt_snd rfl
  exact (Bulk.joint_receipt S F (z:=fun _ U=>NativePaidPacketSeries.value P s.val z x U) h').smooth

private theorem eligible (P : MarkedPackets D G f R) {z : ℤ} (hz : z∈powers P) (n : ℕ) :
    exponent P z≤commonPower P+n ↔ z≤(n:ℤ) := by
  have hl := (mem_Icc.mp hz).1
  unfold exponent commonPower
  omega

private theorem index (P : MarkedPackets D G f R) {z : ℤ} (hz : z∈powers P) (n : ℕ) :
    commonPower P+n-exponent P z=((n:ℤ)-z).toNat := by
  have hl := (mem_Icc.mp hz).1
  unfold exponent commonPower
  omega

variable [Fintype V] {h : Clip} {path : PathData G} {O : ChartRatio G} (K : Bulk.Kernel S h path O)

include H hg

/-- For independent original source fields the order n coefficient uses exactly the entries z≤n of their individual signed Laurent series, and the numerical field derivative n−z on each such entry. The possibly arbitrary vacuum does not occur. -/
theorem kernel (vac : ℝ→ Config G f→ℝ) (x : TestSpace D) (s : Hot R) (B : fieldDir G c 1) (n : ℕ) :
    Assembly.kernelJet (Bulk.stage K F B) (Bulk.hinge F) (Bulk.markFn S F (colors P vac x) s) (commonPower P+n)=
      ∑z∈powers P,if z≤(n:ℤ) then Assembly.kernelJet (Bulk.stage K F B) (Bulk.hinge F)
        (fiber F P x s z) ((n:ℤ)-z).toNat else 0 := by
  apply Valence.Enlist.paint_inj
  intro a
  let v := Assembly.translate (Bulk.stage K F B) (Bulk.hinge F) a
  have hv : v.1=1 := by change (1:ℝ)+0=1; exact add_zero _
  let term (z : ℤ) (y : Bulk.Joint S F (G:=G)) := y.1^(exponent P z) • fiber F P x s z y
  have inp : Bulk.markFn S F (colors P vac x) s=fun y=>∑z∈powers P,term z y :=
    funext fun y=>mark_polynomial_eq H hg vac x s y.1 (Work.F03.live F y.2)
  have ht (z : ℤ) (_hz : z∈powers P) : ContDiffAt ℝ ω (term z) 0 :=
    (shifted_grade (analytic F H hg x s z) _).smooth
  rw [Assembly.reading,inp,jet_sum _ term ht,map_sum]
  apply sum_congr rfl
  intro z hz
  change Assembly.jet (fun y : Bulk.Joint S F (G:=G)=>y.1^(exponent P z) • fiber F P x s z y) _ v=_
  rw [shifted (analytic F H hg x s z) _ _ v hv]
  by_cases hzn : z≤(n:ℤ)
  · rw [if_pos hzn,if_pos ((eligible P hz n).2 hzn),Assembly.reading,index P hz n]
  · rw [if_neg hzn,if_neg ((eligible P hz n).not.mpr hzn),map_zero]

/-- The independent native Fk generator receives the same unaltered coupled factorial for every eligible original marked power. -/
theorem generator (vac : ℝ→ Config G f→ℝ) (x : TestSpace D) (B : fieldDir G c 1) (q : S.Choices) (r : ℕ)
    (s : Hot (Order.Board R r)) (hs : (Join.left s.val).val.Nonempty) :
    let n := (Join.right s.val).val.card
    let i : Hot R := ⟨Join.left s.val,hs⟩
    let W := colors P vac x
    Assembly.generator (Bulk.stage K F B) (Bulk.hinge F) W.power (Bulk.markFn S F W) (Bulk.geometric K F q W) r s=
      (n.factorial:ℂ) • ∑z∈powers P,if z≤(n:ℤ) then Assembly.kernelJet (Bulk.stage K F B) (Bulk.hinge F)
        (fiber F P x i z) ((n:ℤ)-z).toNat else 0 := by
  dsimp only [Assembly.generator]
  rw [dif_pos hs]
  exact congrArg ((_:ℂ) • ·) (kernel F H hg K vac x ⟨Join.left s.val,hs⟩ B (Join.right s.val).val.card)

end YM.Integration.SignedFormalPowerLayers
