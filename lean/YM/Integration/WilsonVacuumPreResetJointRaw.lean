import YM.Integration.WilsonVacuumPreResetJointField
import YM.Work.G05.Taylor

/-! The ordered relative-to-raw product is logged about its true compact
background. The one total Taylor polynomial contains all admissible coarse
and fine degrees on the original branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetJointRaw
open Function Filter Lattice RG Wilson Pressure Tree Gauge Precision Push Push.Uniform
open ConnectedActivityE6 Coat Work.G05
open WilsonVacuumPreResetJointField
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}

def relative (P : Finset (Bond c)) (X : Coat T F) (z : Arguments G c f) (e : Bond f) :=
  field P X z e * (field P X 0 e)⁻¹

def changes (P : Finset (Bond c)) (X : Coat T F) (z : Arguments G c f) : Directions G f :=
  fun e => G.plog (G.mat (relative P X z e))

private theorem relative_zero (P : Finset (Bond c)) (X : Coat T F) (e : Bond f) :
    relative P X 0 e = 1 := by simp [relative]

theorem changes_zero (P : Finset (Bond c)) (X : Coat T F) : changes P X 0 = 0 := by
  ext1 e
  simp [changes, relative_zero]

private theorem relative_matrix (P : Finset (Bond c)) (X : Coat T F) (e : Bond f) :
    ContDiffAt ℝ ω (fun z => G.mat (relative P X z e)) 0 := by
  simp only [relative, G.mat_mul]
  exact (links P X 0 0 e).analytic.mul contDiffAt_const

theorem smooth (P : Finset (Bond c)) (X : Coat T F) :
    ContDiffAt ℝ ω (changes P X) 0 := by
  apply contDiffAt_pi.mpr
  intro e
  apply ContDiffAt.comp (g := G.plog) (f := fun z => G.mat (relative P X z e)) _ _ (relative_matrix P X e)
  simpa only [relative_zero, G.mat_one] using G.plog_diff

/-- Every frozen link is restored to its actual value. Its relative log is
zero locally, even if the link itself lies outside any chart at the identity. -/
theorem agrees (P : Finset (Bond c)) (X : Coat T F) :
    field P X =ᶠ[𝓝 0] fun z => RG.increment (field P X 0) (changes P X z) := by
  have branch (e : Bond f) : ∀ᶠ z in 𝓝 (0 : Arguments G c f),
      G.lieExp (changes P X z e) = relative P X z e := by
    have h : ContinuousAt (fun z => relative P X z e) 0 :=
      (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr
        (relative_matrix P X e).continuousAt.tendsto
    have toward := h.tendsto
    rw [relative_zero] at toward
    exact toward.eventually G.plog_right
  filter_upwards [eventually_all.mpr branch] with z hz
  funext e
  rw [RG.increment, hz e, relative, inv_mul_cancel_right]

private theorem polynomial {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} {A B : E → ℝ}
    (h : ∀ i ≤ d, iteratedFDeriv ℝ i A 0 = iteratedFDeriv ℝ i B 0) :
    blockTaylor d A = blockTaylor d B := by
  unfold blockTaylor
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  simp only [Tensor.coeff, h i (by omega)]

/-- Truncation is in the total degree, after the ordered product with the
coarse replica. The saved exterior is the same on both sides. -/
theorem composition (P : Finset (Bond c)) (X : Coat T F) (a : Config G f → ℝ) (d : ℕ)
    (r : ContDiffAt ℝ d (a ∘ RG.increment (field P X 0)) 0) :
    blockTaylor d (a ∘ field P X) =
      blockTaylor d (blockTaylor d (a ∘ RG.increment (field P X 0)) ∘ blockTaylor d (changes P X)) := by
  let H := changes P X
  let A := a ∘ RG.increment (field P X 0)
  have hH : ContDiffAt ℝ d H 0 := (smooth P X).of_le le_top
  have h0 : H 0 = 0 := changes_zero P X
  have hT : blockTaylor d H 0 = 0 := (blockTaylor_zero d H).trans h0
  have h := jets_comp (x:=0) (g:=A) (g':=blockTaylor d A) hH (blockTaylor_contDiff d H _).contDiffAt
    (h0.symm ▸ r) (blockTaylor_contDiff d A _).contDiffAt (h0.trans hT.symm)
    (fun k hk => (blockTaylor_jets hH k hk).symm)
    (fun k hk => by rw [hT]; exact (blockTaylor_jets r k hk).symm)
  have same : a ∘ field P X =ᶠ[𝓝 0] A ∘ H :=
    (agrees P X).mono fun z hz => congrArg a hz
  exact polynomial fun k hk => ((same.iteratedFDeriv ℝ k).eq_of_nhds).trans (h k hk)

/-- Ordered legs in the subset carry coarse directions. The complement carries
fine directions. Their cardinalities sum to n under the same truncation d. -/
theorem degrees (P : Finset (Bond c)) (X : Coat T F) (a : Config G f → ℝ) (d : ℕ)
    (z : Arguments G c f) :
    blockTaylor d (a ∘ field P X) z =
      ∑ n ∈ Finset.range (d+1), ∑ I : Finset (Fin n),
        Tensor.coeff (a ∘ field P X) n 0 (I.piecewise (fun _ => (z.1, 0)) (fun _ => (0, z.2))) := by
  rw [blockTaylor, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n _
  let A := Tensor.coeff (a ∘ field P X) n 0
  have hz : z = (z.1, 0) + (0, z.2) := by ext1 <;> simp
  change Tensor.diagonal A z = _
  conv_lhs => rw [hz]
  exact A.map_add_univ (fun _ => (z.1, 0)) (fun _ => (0, z.2))

end YM.Integration.WilsonVacuumPreResetJointRaw
