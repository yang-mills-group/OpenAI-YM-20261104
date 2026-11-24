import YM.Integration.FVA1Physical.Marked.RootedLeft
import YM.Integration.FVA1Physical.Marked.QuayFunded

/-! At every inherited depth the exact mixed moment of the microscopic physical
basis fields has a period-independent derivative estimate. The source bank
and stem are fixed before testing the complex field voices. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Function Filter Finset Lattice RG YM.Wilson Tree Precision Source Labels Extra.Histories Marker
open LocalLTE.Sail PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Org RG.Supply
open MergeProof.Accent Bandage.Harmonics Next.Foundations PhysicalNext.Repeat.Legato.Round2
open PhysicalNext.Repeat.Roost YM.Integration.FVA1Physical.Round2 YM.Integration.FVA1Physical.Round2.Quay YM.Integration.FVA1Physical.Wilson
open RGComparison.Core16.Lam RGComparison.Core16.Catkin Push.AbsoluteSums Further.LogJets
open scoped Classical BigOperators Topology
variable {G : Gauge} {n : Side}

private theorem entry_germ {F : Frame G 0} (D : SectionData F) (Z : Coefficient F n) (R : Rep G n)
    (o : Site n) {U : Config G n} (hu : U ∈ Boulevard.sunny R.p) :
    Z.exponentialEntry o D R =ᶠ[𝓝 U] ((fun _=>Z.x 0)+(fun V=>∑' i,Z.regular i V)) := by
  filter_upwards [(Boulevard.sky R.p).mem_nhds hu] with V hv
  rw [LocalLTE.Concourse.center_entry]
  change Z.x 0+(∑' i,Z.maskedTerm R i V)=Z.x 0+(∑' i,Z.regular i V)
  apply congrArg (Z.x 0+·)
  apply tsum_congr
  intro i
  apply masked_eq
  unfold Healthy; rw [Boulevard.smoky hv]; simp

theorem rooted_entry {F : Frame G 0} {A : Hol G} {R : Rep G n} {o : Site n}
    {Z : Coefficient F n} {κ h α : ℝ} (D : SectionData F) (shape : Z.Format o A R)
    (cost : Z.remBound o R κ h) (l : List (Operand G n)) (nonempty : l ≠ [])
    (length : l.length ≤ R.p.order) (pos : 0 ≤ α) (room : α*l.length*(6*R.p.B+2:ℝ) ≤ R.p.supportExponent)
    {U : Config G n} (hu : U ∈ Boulevard.sunny R.p) :
    Real.exp (α*wordRadius o l)*‖leftDerivs (Z.exponentialEntry o D R) (l.map compass) U‖ ≤ (R.p.threshold⁻¹)^l.length*h := by
  obtain ⟨a,b,_ha,hb,ab,_hκ,⟨e,credit,limits⟩,_⟩:=cost
  have L : (l.map compass).length ≤ R.p.order := by simpa using length
  have smooth:= (complex_termwise shape.smooth limits credit).smooth_exchange (Boulevard.sky _) U hu
  rw [(UVNext.PricedKernels.left_congr (entry_germ D Z R o hu) _).self_of_nhds,
    Push.Local.left_add _ (show Push.Local.Chart R.p.order (fun _=>Z.x 0) U from contDiffAt_const) smooth.1 L,
    Work.G07.left_const,if_neg (by simpa using nonempty),zero_add]
  exact (rooted_sum shape.smooth limits shape.origin credit l length pos room hu).trans
    (mul_le_mul_of_nonneg_left ((le_add_of_nonneg_right hb).trans ab) (pow_nonneg (inv_nonneg.mpr R.p.threshold_pos.le) _))

variable {X : Metals G} {D : Rolls X.p} {A : Alloy X D} {P : Bolt A} {R : Factor A}
    {ref : ℕ → ℕ} {fields : ∀ d N n,TransferData ((frames G).level d) (Issue.trail P) N n} {p d c : ℕ}

/-- Every mixed subset, finite fixed horizon, true repeated push and every
complex unit test in the registered centered family. At non-bare scales the
regular budget is at most one, with an additional explicit geometric contraction
in the number of inherited steps. The constant is independent of the torus. -/
theorem physical_centered_derivative (books : PhysicalBooks R P ref fields p d c)
    {N n m : ℕ} (hm : m < N) (start : ref 0 ≤ m) {I : Type} [Fintype I] [DecidableEq I]
    (B : Census I) (h : I → ℕ) (v : ∀ j, ((frames G).level (h j)).Coeff)
    (paths : ∀ i : ℕ,LocalLTE.FrameBox.Grove (0:Site (A.B.a.S.side i n)))
    (card : Fintype.card I ≤ c) (grade : ∀ j,h j ≤ d) (fits : ∀ j,ref (h j) ≤ m)
    (test : ∀ j,((frames G).level (h j)).coeffSize (v j) ≤ 1)
    (s : B.Mode) {i : ℕ} (lo : m ≤ i) (hi : i < N)
    (l : List (Operand G ((Issue.trail P).S.side i n))) (nonempty : l ≠ [])
    {α : ℝ} (pos : 0 ≤ α) (U : Config G ((Issue.trail P).S.side i n)) :
    let M:=((Issue.trail P).rep N n i).p
    l.length ≤ M.order → α*l.length*(6*M.B+2:ℝ) ≤ M.supportExponent → U ∈ Boulevard.sunny M →
      Real.exp (α*wordRadius 0 l) *
        ‖leftDerivs (fun V=>(momentTable B (centeredBatch P N n h v) i hi.le V).part s) (l.map compass) U‖ ≤
      (M.threshold⁻¹)^l.length * (1/2:ℝ)^(N-(i+1)) := by
  intro M length room hu
  obtain ⟨F,orator,reads⟩:=(books.registered N n m hm start I B h v paths card grade fits test).1
  let Z:=(F s i).X
  let D':=localSection G 0
  have cert:=(orator s).schedule i lo hi.le
  have read:=(reads i lo hi.le).2 s
  have e : (fun V=>(momentTable B (centeredBatch P N n h v) i hi.le V).part s)
      =ᶠ[𝓝 U] Z.exponentialEntry 0 D' ((Issue.trail P).rep N n i) := by
    filter_upwards [(Boulevard.sky M).mem_nhds hu] with V hv
    rw [←vista_moments P N n h v B i hi.le V]
    have real_part (a : ℝ) (x : Poly B) : (a • x).part s=(a:ℂ)*x.part s := rfl
    simpa only [Poly.part_smul,real_part,Complex.ofReal_inv] using (read.reads V (Boulevard.smoky hv)).2.1
  rw [(UVNext.PricedKernels.left_congr e _).self_of_nhds]
  simpa only [Bandage.Harmonics.limitT,if_neg hi.ne,Bandage.Harmonics.rateSpan] using
    rooted_entry D' cert.certC.format cert.certC.credit l nonempty length pos room hu

end YM.Integration.FVA1Physical.Marked
