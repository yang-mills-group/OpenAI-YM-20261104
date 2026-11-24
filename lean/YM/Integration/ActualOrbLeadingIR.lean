import YM.Integration.ActualLeadingSeries
import YM.Integration.WilsonInversionSchur
import YM.FVA2.BareOrb
import YM.FormalOPE.RG10.Powers

/-! Exact original Orb coefficient identification for the retained
Wilson source film. The finite-regulator identities retain the full
series; the infrared estimates concern its leading coefficient. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.ActualOrbLeadingIR

open Function Filter Lattice Wilson Source PowerSeries
open RG06 RG06.WilsonCompiler XSpace XSpace.Chart2 XSpace.Outline
open PertExtension FVA2 ActualLeadingIR ActualLeadingSeries
open scoped BigOperators Classical Topology ContDiff

variable {G : Gauge} (C : Family G) (N p : ℕ)

private theorem links_roll (T : (actualPeriod C N p).Tree) (u : T.Field G) (t : ℝ) :
    T.links (t • u) = roll (T.covering u) t := by
  funext e
  rw [T.links_apply, map_smul]
  rfl

theorem source_read (d : ℕ) (T : (actualPeriod C N p).Tree)
    (x : Site (C.side N p)) (i : (C.labels.level d).Index) (u : T.Field G) :
    PowerSeries.map (Taylor.evalAt (T.basis G) u).toRingHom
      (ActualLeadingSeries.source C N p d T x i) =
      develop (access G (T.covering u))
        (physicalFilm C N p d x
          (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i))) := by
  ext k : 1
  rw [PowerSeries.coeff_map, ActualLeadingSeries.source_coeff]
  calc
    _ = pit (T.covering u) (coeff k
        (physicalFilm C N p d x
          (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i)))) :=
      log_path T u _
    _ = tone (access G (T.covering u)) (coeff k
        (physicalFilm C N p d x
          (Dict06.Actual.calibrate C N p d ((C.labels.level d).basis i)))) := rfl
    _ = _ := (develop_coeff _ _ k).symm

private theorem garnish_prod {I : Type*} (s : Finset I) (f : I → ℝ → ℂ)
    (P : I → PowerSeries ℂ) (h : ∀ i ∈ s, GSeries.Garnish 0 (f i) (P i)) :
    GSeries.Garnish 0 (fun t => ∏ i ∈ s, f i t) (∏ i ∈ s, P i) := by
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.prod_empty, map_one] using
      GSeries.Garnish.constant 0 (1 : ℂ)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self ..)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private theorem linear_product_expansion
    {J : Type*} [Fintype J] {K : J → Type*} [∀ j, Fintype (K j)]
    {A B : Type*} [CommSemiring A] [Algebra ℂ A]
    [AddCommMonoid B] [Module ℂ B]
    (L : A →ₗ[ℂ] B) (F : (j : J) → K j → A)
    (v : (j : J) → K j → ℂ) :
    L (∏ j, ∑ k, v j k • F j k) =
      ∑ b : (j : J) → K j, (∏ j, v j (b j)) •
        L (∏ j, ∑ k, (Pi.single (b j) (1 : ℂ) : K j → ℂ) k • F j k) := by
  rw [Fintype.prod_sum, map_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.prod_smul, map_smul]
  apply congrArg (fun y : B => (∏ j, v j (b j)) • y)
  apply congrArg L
  apply Finset.prod_congr rfl
  intro j _
  simp [Pi.single_apply]

variable {I : Type*} [Fintype I] (degree : I → ℕ) (x : I → Cover)
    (b : Choices C degree)

/-- Literal product of all original calibrated source germs in the
chosen native tree chart; the denominator has not yet been divided. -/
theorem source_product_stencil (hC : C.Makes) (T : (actualPeriod C N p).Tree) :
    (∏ i, ActualLeadingSeries.source C N p (degree i) T
      (wrap (C.side N p) (x i)) (b i)) =
      BareOrb.stencil T (physicalInversionProduct C N p degree
        (wrap (C.side N p) ∘ x) b Finset.univ) := by
  let O : Config G (actualPeriod C N p).side → ℝ :=
    physicalInversionProduct C N p degree (wrap (C.side N p) ∘ x) b Finset.univ
  change (∏ i, ActualLeadingSeries.source C N p (degree i) T
    (wrap (C.side N p) (x i)) (b i)) = BareOrb.stencil T O
  have hO : Orb.PreTest O := physicalInversionProduct_pretest C N p degree
    (wrap (C.side N p) ∘ x) b hC Finset.univ
  have hs := OrbGerm.tree T hO
  change ContDiffAt ℝ ∞ (O ∘ T.links) 0 at hs
  have hc : ContDiffAt ℝ ∞ (Complex.ofRealCLM ∘ O ∘ T.links) 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0 hs
  ext k : 1
  apply Taylor.from_real (T.basis G)
  intro u
  change coeff k (PowerSeries.map (Taylor.evalAt (T.basis G) u).toRingHom
    (∏ i, ActualLeadingSeries.source C N p (degree i) T
      (wrap (C.side N p) (x i)) (b i))) = _
  rw [map_prod]
  simp_rw [source_read]
  have hg := garnish_prod Finset.univ
    (fun i t => C.O N p
      (Dict06.Actual.calibrate C N p (degree i) ((C.labels.level (degree i)).basis (b i)))
      (wrap (C.side N p) (x i)) (roll (T.covering u) t))
    (fun i => develop (access G (T.covering u))
      (physicalFilm C N p (degree i) (wrap (C.side N p) (x i))
        (Dict06.Actual.calibrate C N p (degree i) ((C.labels.level (degree i)).basis (b i)))))
    (fun i _ => physicalFilm_garnish C N p (degree i)
      (wrap (C.side N p) (x i)) _ (T.covering u))
  rw [hg.coeff]
  change _ = Taylor.evalAt (T.basis G) u
    (coeff k (Taylor.expandTaylor (T.basis G) (Complex.ofRealCLM ∘ O ∘ T.links)))
  rw [Taylor.line_coeff (T.basis G) k u (hc.of_le (GSeries.at_order k))]
  have he : (fun t => (Complex.ofRealCLM ∘ O ∘ T.links) (t • u)) =
      (fun t => ∏ i, C.O N p
        (Dict06.Actual.calibrate C N p (degree i) ((C.labels.level (degree i)).basis (b i)))
        (wrap (C.side N p) (x i)) (roll (T.covering u) t)) := by
    funext t
    change (O (T.links (t • u)) : ℂ) = _
    rw [links_roll]
    exact physicalInversionProduct_real C N p degree
      (wrap (C.side N p) ∘ x) b hC Finset.univ _
  rw [he]
  simp only [GSeries.offer, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- Restoring exactly the original total slot power gives the normalized
Orb series of the literal product on the original inversion regulator. -/
theorem basis_orbit (hC : C.Makes)
    (hV : ∀ i, Bid.pop (C.localSection (degree i))) (T : (actualPeriod C N p).Tree) :
    PowerSeries.X ^ (∑ i, ((C.labels.level (degree i)).grades (b i)).2) *
      ActualLeadingSeries.series C N p degree T x (basisInput C degree b) =
      TaylorWick.into (PowerSeries.mk (Orb.diag (Orb.restrictedO
        (physicalInversionProduct C N p degree (wrap (C.side N p) ∘ x) b Finset.univ)))) := by
  rw [series_basis_restore C N p degree hV, source_product_stencil C N p degree x b hC]
  exact BareOrb.diagram_eq T (physicalInversionProduct_pretest C N p degree
    (wrap (C.side N p) ∘ x) b hC Finset.univ)

/-- The actual normalized Orb coefficient at its original total grade
is exactly the finite quantity whose infrared error was estimated. -/
theorem coefficient (hC : C.Makes)
    (hV : ∀ i, Bid.pop (C.localSection (degree i))) (T : (actualPeriod C N p).Tree) :
    coeff (∑ i, ((C.labels.level (degree i)).grades (b i)).2)
      (TaylorWick.into (PowerSeries.mk (Orb.diag (Orb.restrictedO
        (physicalInversionProduct C N p degree (wrap (C.side N p) ∘ x) b Finset.univ))))) =
      finite C degree (engineeredInput C degree N (basisInput C degree b))
        (actualPeriod C N p) T x := by
  rw [← basis_orbit C N p degree x b hC hV T, coeff_X_pow_mul']
  simp only [le_refl, ↓reduceIte, Nat.sub_self]
  exact series_leading C N p degree T x (basisInput C degree b)

/-- The original normalized Orb coefficients, extended multilinearly in
the independent source coordinates. Every term retains its own original
total grade; all factors in that term share one vacuum denominator. -/
def orbitSeries (v : (i : I) → C.label (degree i)) : PowerSeries ℂ :=
  ∑ b : Choices C degree, (∏ i, v i (b i)) •
    FormalOPE.RG10.lower (∑ i, ((C.labels.level (degree i)).grades (b i)).2)
      (TaylorWick.into (PowerSeries.mk (Orb.diag (Orb.restrictedO
        (physicalInversionProduct C N p degree (wrap (C.side N p) ∘ x) b Finset.univ)))))

private theorem series_expansion (T : (actualPeriod C N p).Tree)
    (v : (i : I) → C.label (degree i)) :
    ActualLeadingSeries.series C N p degree T x v =
      ∑ b : Choices C degree, (∏ i, v i (b i)) •
        ActualLeadingSeries.series C N p degree T x (basisInput C degree b) := by
  unfold ActualLeadingSeries.series
  generalize Bare.normalized T G = L
  simpa [basisInput, Pi.single_apply] using
    (linear_product_expansion L
      (fun i j => lowerFilm ((C.labels.level (degree i)).grades j).2
        (ActualLeadingSeries.source C N p (degree i) T
          (wrap (C.side N p) (x i)) j)) v)

/-- All orders of the actual source series agree with the original Orb
prescription. This is an identification theorem, not an assumed error
bound or a replacement by a chosen Survey. -/
theorem series_eq_orbitSeries (hC : C.Makes)
    (hV : ∀ i, Bid.pop (C.localSection (degree i)))
    (T : (actualPeriod C N p).Tree) (v : (i : I) → C.label (degree i)) :
    ActualLeadingSeries.series C N p degree T x v = orbitSeries C N p degree x v := by
  rw [series_expansion, orbitSeries]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  rw [← basis_orbit C N p degree x b hC hV T, FormalOPE.RG10.lower_delay]

/-- The derived IR estimate applies to the original normalized Orb
prescription uniformly over all independent input coefficients. -/
theorem comparison (hC : C.Makes)
    (hV : ∀ i, Bid.pop (C.localSection (degree i))) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (N p : ℕ) (v : (i : I) → C.label (degree i))
      (_T : (actualPeriod C N p).Tree) (o : Cover),
      Comets.Tall (actualPeriod C N p) o → ∀ (r : ℕ) (x : I → Cover),
      (∀ i, Sail.reach (x i - o) ≤ r) →
      engineeringScale C degree N *
        ‖coeff 0 (orbitSeries C N p degree x v) -
          cover C degree (engineeredInput C degree N v) x‖ ≤
        A * Comets.budget (actualPeriod C N p) r * inputMass C degree v := by
  obtain ⟨A, hA, H⟩ := ActualLeadingSeries.comparison C degree hV
  refine ⟨A, hA, ?_⟩
  intro N p v T o ho r x hx
  rw [← series_eq_orbitSeries C N p degree x hC hV T v]
  exact H N p v T o ho r x hx

/-- The original normalized Orb prescription has the proved leading
infrared limit on the original period sequence at fixed UV cutoff. -/
theorem error_tendsto (hC : C.Makes)
    (hV : ∀ i, Bid.pop (C.localSection (degree i)))
    (N r : ℕ) (v : (p : ℕ) → (i : I) → C.label (degree i)) (M : ℝ)
    (hmass : ∀ᶠ p in atTop, inputMass C degree (v p) ≤ M)
    (T : (p : ℕ) → (actualPeriod C N p).Tree)
    (o : ℕ → Cover) (x : ℕ → I → Cover)
    (hbulk : ∀ᶠ p in atTop, Comets.Tall (actualPeriod C N p) (o p) ∧
      ∀ i, Sail.reach (x p i - o p) ≤ r) :
    Tendsto (fun p => coeff 0 (orbitSeries C N p degree (x p) (v p)) -
      cover C degree (engineeredInput C degree N (v p)) (x p)) atTop (𝓝 0) := by
  have he (p : ℕ) := series_eq_orbitSeries C N p degree (x p) hC hV (T p) (v p)
  simpa only [he] using
    ActualLeadingSeries.error_tendsto C degree hV N r v M hmass T o x hbulk

end YM.Integration.ActualOrbLeadingIR
