import YM.Integration.FVA1Physical.Wilson.AllOrdersOrbit
import YM.RGComparison.Core16.Marks
import YM.Comparison.RG02.Order.Pay

/-! Local complex stencils, mixed products and normalized joint readings on the
same physical exterior and independently normalized interior Wilson kernel. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Marker RGComparison.Core16
open RGComparison.Core16.Descent MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Bulk Comparison.RG02.Order
open scoped Classical Topology
variable {G : Gauge} {f c : Side} {S : StepData c f} {Y : Support f}

structure LocalInsertion (S : StepData c f) (Y : Support f) (φ : Config G f→ℂ) : Prop where
  measurable : Measurable φ
  turn : ∀ k : Site f → G.El, (∀ i,k (S.ratio.embed i)=1) → ∀ U,φ (Lattice.gauge k U)=φ U
  located : LocalOn Y φ
  bound : ∀ U,‖φ U‖ ≤ 1

lemma LocalInsertion.products {I : Type} {F : I → Config G f→ℂ} (h : ∀ i,LocalInsertion S Y (F i)) (s : Finset I) :
    LocalInsertion S Y (fullProduct F s) := by
  refine ⟨Finset.measurable_fun_prod _ fun i _=>(h i).measurable,?_,?_,?_⟩
  · intro k hk U; exact Finset.prod_congr rfl fun i _=>(h i).turn k hk U
  · intro U V eq; exact Finset.prod_congr rfl fun i _=>(h i).located U V eq
  intro U; unfold fullProduct; rw [norm_prod]; exact Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun i _=>(h i).bound U)

lemma LocalInsertion.real {φ : Config G f→ℂ} (h : LocalInsertion S Y φ) :
    GaugeLocal S Y (fun U=>(φ U).re) ∧ ∀ U,|(φ U).re|≤1 := by
  have cap := fun U=>(Complex.abs_re_le_norm (φ U)).trans (h.bound U)
  exact ⟨⟨⟨Complex.continuous_re.measurable.comp h.measurable,1,cap⟩,
    fun k hk U=>congrArg Complex.re (h.turn k hk U),fun U V eq=>congrArg Complex.re (h.located U V eq)⟩,cap⟩

lemma LocalInsertion.imag {φ : Config G f→ℂ} (h : LocalInsertion S Y φ) :
    GaugeLocal S Y (fun U=>(φ U).im) ∧ ∀ U,|(φ U).im|≤1 := by
  have cap := fun U=>(Complex.abs_im_le_norm (φ U)).trans (h.bound U)
  exact ⟨⟨⟨Complex.continuous_im.measurable.comp h.measurable,1,cap⟩,
    fun k hk U=>congrArg Complex.im (h.turn k hk U),fun U V eq=>congrArg Complex.im (h.located U V eq)⟩,cap⟩

variable {I : Type} [DecidableEq I] (C : Census I) (F : I → Config G f→ℂ)

def orbitMoments (E : (Config G f→ℝ)→ℝ) : Poly C :=
  Poly.inject fun s=> ⟨E (fun U=>(fullProduct F s.val U).re), E (fun U=>(fullProduct F s.val U).im)⟩

lemma orbitMoments_quiet (E : (Config G f→ℝ)→ℝ) (oneE : E 1=1) (zeroE : E 0=0) :
    (orbitMoments C F E).part C.quiet=1 := by
  apply Complex.ext
  · change E (fun U=>(fullProduct F ∅ U).re)=1
    exact (congrArg E (show (fun U=>(fullProduct F ∅ U).re)=(1 : Config G f→ℝ) by funext U; simp [fullProduct])).trans oneE
  change E (fun U=>(fullProduct F ∅ U).im)=0
  exact (congrArg E (show (fun U=>(fullProduct F ∅ U).im)=(0 : Config G f→ℝ) by funext U; simp [fullProduct])).trans zeroE

/-- Every allowed source mode uses the same conditional numerator law and empty
mode. The only norm factor here is two for real and imaginary testing. -/
theorem orbit_mixed_price (w : I→ℝ) (hw : ∀ i,0<w i) (E W : (Config G f→ℝ)→ℝ)
    (hF : ∀ i, LocalInsertion S Y (F i)) {ε : ℝ}
    (bill : ∀ φ, GaugeLocal S Y φ → (∀ U,|φ U|≤1) → |W φ-E φ|≤ε) :
    Poly.price w (orbitMoments C F W-orbitMoments C F E) ≤ (∑ s:C.Mode,Poly.toll w s)*(2*ε) := by
  rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro s _
  have h := LocalInsertion.products hF s.val
  have a := bill _ h.real.1 h.real.2
  have b := bill _ h.imag.1 h.imag.2
  let d := (orbitMoments C F W-orbitMoments C F E).part s
  apply mul_le_mul_of_nonneg_left _ (Poly.worth hw s).le
  have cost := Complex.norm_le_abs_re_add_abs_im d
  exact cost.trans ((add_le_add a b).trans_eq (two_mul ε).symm)
end YM.Integration.FVA1Physical.Wilson
