import YM.Comparison.Stencils.Nested
import YM.Next.STATIONARY.Joint.Gauge

/-!
# Color and horizontal properties of the stencil supply

Bare unnormalized density factors need not be invariant separately at each
positive Taylor order under an arbitrary lattice gauge transformation. Here
we use the common *constant* color symmetry for the coefficient space.
For the actual stencils themselves there is full lattice gauge invariance.
Degree zero after section slot scaling is horizontal in links (on adding a
discrete gradient), even before applying any projectors. Higher orders are
not assumed horizontal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.Stencils
open CubicMatch Lattice Function RG Wilson Symbols Labels Source Source.Drops Filter Feed
open Next.Rank.LiftMark (factors weighed factors_C factors_X)
open Next.Foundations
open Planned.PrimaryIntegral295.Place (Spot Dev placeEdge)
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {S S' : Finset Cover} {σ : Type*}

section Rescale
lemma magnitude_scales (p : MvPolynomial σ ℂ) (z : ℂ) (f : σ → ℂ) :
    MvPolynomial.aeval f (factors z p) = MvPolynomial.aeval (fun i => z * f i) p := by
  induction p using MvPolynomial.induction_on with
  | add p q hP hQ => simp only [map_add,hP,hQ]
  | C a => simp
  | mul_X p i h => simp only [map_mul, h, factors_X, MvPolynomial.aeval_X]
                   simp

lemma pure_formula (c : ℂ) (k n : ℕ) : term k (fun t : ℝ => t^n • c) = if k=n then c else 0 := by
  rw [term, iteratedDeriv_smul_const (show ContDiffAt ℝ k (fun x : ℝ => x^n) 0 from contDiffAt_id.pow _),
    iteratedDeriv_fun_pow_zero]; split_ifs with h
  · subst k; rw [smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  · simp

lemma solidarity (f : σ → ℂ) (p : MvPolynomial σ ℂ) (i : ℕ) :
    MvPolynomial.aeval f (portion i p) = term i (fun t : ℝ => MvPolynomial.aeval (fun k => t • f k) p) := by
  induction p using MvPolynomial.induction_on' with
  | add p q hP hQ =>
    have he (j : σ) : ContDiffAt ℝ ω (fun x : ℝ => x • f j) 0 :=
      contDiffAt_id.smul contDiffAt_const
    simp_rw [map_add]
    exact (congrArg₂ (·+·) hP hQ).trans (term_add
      (show ContDiffAt ℝ i (fun t : ℝ => MvPolynomial.aeval (fun k => t • f k) p) 0 from (smooth_pol p he).of_le le_top)
      (show ContDiffAt ℝ i (fun t : ℝ => MvPolynomial.aeval (fun k => t • f k) q) 0 from (smooth_pol q he).of_le le_top)).symm
  | monomial v a =>
    let p := MvPolynomial.monomial v a
    let j := Finsupp.weight (fun _ => (1:ℕ)) v
    have he : Rank p j := MvPolynomial.isWeightedHomogeneous_monomial _ _ _ rfl
    have H (t : ℝ) : MvPolynomial.aeval (fun k => t • f k) p = t^j • MvPolynomial.aeval f p := by
      simp_rw [Complex.real_smul, ← magnitude_scales p]
      rw [coat_rank _ p he, map_smul, Complex.ofReal_pow]; rfl
    change MvPolynomial.aeval f (portion i p) = _
    rw [show term i (fun t : ℝ => MvPolynomial.aeval (fun k => t • f k) p) = _ from
      congrArg (term i) (funext H), pure_formula, on_rank p _ he i]
    split_ifs <;> simp

lemma portion_rays (x : Links ℤ G.Color) (p : LocalPol G S) (i : ℕ) :
    inscribe (Symbols.patch S x) (portion i p) =
      term i (fun t : ℝ => inscribe (Symbols.patch S (t • x)) p) := by
  rw [inscribe, solidarity]
  apply congrArg _
  funext t
  unfold inscribe
  rw [show (fun k : Var G S => (↑(coordinate k (Symbols.patch S (t • x))) : ℂ))=
    fun k => t • (↑(coordinate k (Symbols.patch S x)) : ℂ) by funext k; simp [coordinate_value,Symbols.patch,Complex.real_smul]]

lemma radial_rays (p : Pol G) (i : ℕ) (J : Jet G) :
    Labels.read J (portion i p) = term i (fun t : ℝ => Labels.read (t • J) p) := by
  rw [Labels.read, solidarity]
  apply congrArg _
  funext t
  simp only [Labels.read]
  rw [show (coord (t • J))=fun i => t • coord J i by funext i; simp [coord,Complex.real_smul]]
end Rescale

section Color

def badge (u : G.El) (A : Links ℤ G.Color) : Links ℤ G.Color := G.adjoint u ∘ A
def Hue (P : LocalPol G S) := ∀ (A : Links ℤ G.Color) (u : G.El),
    inscribe (Symbols.patch S (badge u A)) P = inscribe (Symbols.patch S A) P

lemma hue_smul (u : G.El) (t : ℝ) (A : Links ℤ G.Color) : badge u (t • A)=t • badge u A :=
  funext fun _ => (G.adjoint u).map_smul t _

lemma hue_portion {P : LocalPol G S} (h : Hue P) (i : ℕ) : Hue (portion i P) := by
  intro A u
  simp_rw [portion_rays, ← hue_smul, h _ u]

lemma hatch (H : Hol G) (J : Jet G) (d : ℕ) (p : Edge Cover) :
    Tendsto (fun t => H.links d J t p) (𝓝 0) (𝓝 1) := by
  let A (X : Snap G d) := H.links d (expand d X) 1 p
  have he := Work.G02.linkGerm H d p
  have hu : Tendsto A (𝓝 0) (𝓝 1) := (show A 0=1 from he.2.1) ▸
    (show ContinuousAt A 0 from (G.continuous_mat.isClosedEmbedding G.mat_injective).isInducing.continuousAt_iff.mpr he.1.continuousAt).tendsto
  refine (hu.comp ((show trail J d 0=0 from trail_root J d) ▸ (trail_smooth J d).continuous.tendsto 0)).congr' ?_
  filter_upwards with t
  exact (congr_fun (scales H (d := d) J t) p).symm

def ink (H : Hol G) (J : Jet G) (d : ℕ) (t : ℝ) : Links ℤ G.Color := fun i => G.plog (G.mat (H.links d J t i))

lemma ink_changes (u : G.El) (H : Hol G) (J : Jet G) (d : ℕ) :
    ∀ᶠ t in 𝓝 0, Symbols.patch S (ink H (colored u J) d t)=
      Symbols.patch S (badge u (ink H J d t)) := by
  have he (i : Spot S) : ∀ᶠ t : ℝ in 𝓝 0, ink H (colored u J) d t (placeEdge i) =
      G.adjoint u (ink H J d t (placeEdge i)) := by
    filter_upwards [(hatch H J d (placeEdge i)).eventually (Stationary.plog_conj u)] with t ht
    rw [ink, Work.G01.links_colored]
    exact ht
  exact (eventually_all.mpr he).mono fun t ht => funext fun i => ht i

lemma paints (u : G.El) (A : Jet G) (t : ℝ) : colored u (scaleJet A t)=scaleJet (colored u A) t :=
  funext fun _ => map_smul (Taylor.paint u) _ _

lemma hue_output {P : LocalPol G S} (h : Hue P) (H : Hol G) (d : ℕ) :
    projector H d P ∈ invariantSpace G := by
  intro J u
  let Q := rawPi H d P
  change Labels.read (colored u J) Q = Labels.read J Q
  have hm (k : ℕ) (hk : k ≤ d) : Labels.read (colored u J) (tier k Q) = Labels.read J (tier k Q) := by
    have he := jet_reads H d P J k hk
    have hj := jet_reads H d P (colored u J) k hk
    rw [deriv_read J] at he
    rw [deriv_read (colored u J)] at hj
    apply smul_right_injective ℂ (show (k.factorial:ℝ) ≠ 0 by positivity)
    refine hj.trans (Eq.trans ?_ he.symm)
    have hv : (fun t => inscribe (Symbols.patch S (ink H (colored u J) d t)) P) =ᶠ[𝓝 0]
        fun t => inscribe (Symbols.patch S (ink H J d t)) P := by
      filter_upwards [ink_changes (S := S) u H J d] with t ht
      rw [ht]; exact h _ u
    exact hv.iteratedDeriv_eq k
  rw [← limited_cap d Q (raw_cap ..), capRead, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i hi => hm i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

lemma hue_output_portion {P : Pol G} (h : P ∈ invariantSpace G) (i : ℕ) : portion i P ∈ invariantSpace G := by
  intro J u
  simp_rw [radial_rays]
  apply congrArg _
  funext x
  rw [show x • colored u J=colored u (x • J) from (funext fun k => (map_smul (Taylor.paint u) x (J k)).symm)]
  exact h _ u

lemma hue_single {P : LocalPol G S} (h : Hue P) (H : Hol G) (d i : ℕ) : booth H d i P ∈ invariantSpace G := by
  unfold booth; rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  exact fun k _ => hue_output_portion (hue_output (hue_portion h k) H d) _

lemma hue_stages {P : LogSeries G S} (h : ∀ i, Hue (P i)) (H : Hol G) (d n : ℕ) :
    stage H d n P ∈ localFields G d := by
  refine ⟨stage_cap .., ?_⟩
  rw [stage_at]
  exact Submodule.sum_mem _ fun i _ => hue_single (h i) _ _ _

end Color

section Columns
variable {d : ℕ} {F : Frame G d} {T : SectionData F} {H : Hol G}

theorem base_hue (h : T.Sound H) (i : F.Index) (k : ℕ) : Hue (columnSeries T i k) := by
  intro A u
  simp_rw [column_value]
  apply congrArg _
  funext t
  rw [← hue_smul, show linksOf (badge u (t • A)) = gauge (fun _ => u) (linksOf (t • A)) from
    funext fun p => Stationary.adjoint_exp ..]
  exact h.gaugeInvariant _ _ _

lemma portion_eval (A : Links ℤ G.Color) (T : SectionData F) (i : ℕ) (x : F.Coeff) :
    inscribe (Symbols.patch T.stencil A) (columns T x i) =
      ∑ j : F.Index, x j • inscribe (Symbols.patch T.stencil A) (columnSeries T j i) := by
  change inscribe _ ((∑ j : F.Index, x j • columnSeries T j) i) = _
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]

theorem frame_hue (h : T.Sound H) (p : F.Coeff) (i : ℕ) : Hue (columns T p i) := by
  intro A u
  simp_rw [portion_eval]
  exact Finset.sum_congr rfl fun j _ => congrArg _ (base_hue h j i A u)

-- Horizontality of these pure stencil symbols at order zero only.
def shiftGauge (W : Cover → G.Color) : Links ℤ G.Color := fun i => W i.1-W (i.1+step i.2)

lemma link_shift (W : Cover → G.Color) (A : Links ℤ G.Color) (i : Cover) (w : Walk) :
    Exterior.linkSum (A + shiftGauge W) i w = Exterior.linkSum A i w + (W i-W (stop i w)) := by
  induction w generalizing i with
  | nil => simp [Lattice.stop,Exterior.linkSum]
  | cons a w ih =>
    rw [Exterior.linkSum, Exterior.linkSum, ih, stop]
    cases h : a.neg <;> simp [shiftGauge,Step.used,Step.vec,h] <;> simp only [sub_eq_add_neg] <;> abel

theorem letter_horizontal (i : F.Index) (p : Bid.pop T) (W : Cover → G.Color) (A : Links ℤ G.Color) :
    inscribe (Symbols.patch T.stencil (A+shiftGauge W)) (columnSeries T i 0)=
      inscribe (Symbols.patch T.stencil A) (columnSeries T i 0) := by
  obtain ⟨V⟩ := supplied T p i
  simp_rw [column_reads _ _ V, forms_leading _ V.uses V.min_degree, link_shift,
    square_stop, sub_self, add_zero]

theorem initial_horizontal (p : Bid.pop T) (x : F.Coeff) (W : Cover → G.Color) (A : Links ℤ G.Color) :
    inscribe (Symbols.patch T.stencil (A+shiftGauge W)) (columns T x 0)=
      inscribe (Symbols.patch T.stencil A) (columns T x 0) := by
  simp_rw [portion_eval, letter_horizontal _ p W A]
end Columns
end YM.Comparison.Stencils
