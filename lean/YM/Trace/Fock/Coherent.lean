import YM.Trace.Fock.Kernel
import YM.Trace.Fields
/-!
Symmetric transverse slots, the lp/Fock container and Gaussian vectors used in the
relative-locality identity. Only this matrix element is tested; the use of
an unsymmetrized ambient sum in the no-isometry argument does not identify a new physical
collection of observables.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Trace.Shell
open Boundary YM Function MeasureTheory Filter Complex Set
open scoped Topology ENNReal InnerProductSpace BigOperators Pointwise
variable {m n : ℕ}

@[fun_prop] lemma jet_measurable_coord (h : SlotField m) (i : Mode m) : Measurable (fun p : Mom => jet p h i) :=
    (PiLp.continuous_apply 2 _ _).measurable.comp (measurable_jet h)
@[fun_prop] lemma product_measurable (h : SlotField m) : Measurable (productTest (n:=n) h) := by
   unfold productTest rawTensor; refine (PiLp.continuous_toLp 2 (fun _: (Fin n→Mode m) => ℂ)).measurable.comp (f:=fun (p : Cords n) (I : Fin n→Mode m) => ∏ i, jet (p i) h (I i))
       (measurable_pi_iff.mpr (fun i => by fun_prop))
lemma jetBound_nonneg (f : SlotField m) : 0 ≤ jetBound f := by
     unfold jetBound; apply mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _=>orderCost_nonneg ..))
lemma jet_sq (f : SlotField m) : Integrable (fun x => ‖jet x f‖^2) ν := by
   refine integrable_shell_arbitrary_bound _ (by fun_prop) (jetBound f ^2) (4:ℝ) (by norm_num) ?_
   intro x
   have he : (1+‖x‖) ^ (-(4:ℝ)) = (((1+‖x‖)^2)⁻¹)^2 := by
      rw [Real.rpow_neg (by positivity),← show (↑(4:ℕ):ℝ)=4 by norm_num,Real.rpow_natCast,inv_pow, ← pow_mul] -- pow_mul reverse?
   rw [he,← mul_pow,norm_pow,norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (jet_le f x) _
lemma product_memLp (h : SlotField m) : MemLp (productTest (n:=n) h) 2 (νpow n) := by
   refine (memLp_two_iff_integrable_sq_norm (product_measurable ..|>.aestronglyMeasurable)).2 ?_
   unfold productTest; simp_rw [tensor_sq]
   exact Integrable.fintype_prod (fun _=> jet_sq h)
noncomputable def slot (h : SlotField m) (n : ℕ) : Wave m n := (product_memLp h).toLp _
lemma evaluate_slot (h : SlotField m) : (⇑(slot h n)) =ᵐ[νpow n] productTest (n:=n) h := (product_memLp ..).coeFn_toLp
lemma lp_inner (x y : Wave m n) : inner ℂ x y = ∫ p, inner ℂ (x p) (y p) ∂νpow n := MeasureTheory.L2.inner_def ..
lemma lp_sq (x : Wave m n) : ‖x‖^2 = ∫ p, ‖x p‖^2∂νpow n := by
     have h := congr_arg re (MeasureTheory.L2.inner_def (𝕜:=ℂ) x x)
     rw [← RCLike.re_to_complex, ← RCLike.re_to_complex, ← _root_.integral_re (MeasureTheory.L2.integrable_inner (𝕜:=ℂ) ..)] at h
     simp only [inner_self_eq_norm_sq (𝕜:=ℂ)] at h; exact h
noncomputable def cost (f : SlotField m) (n : ℕ) := ‖slot f 1‖^(2*n)
lemma norm_slot_sq (h : SlotField m) : ‖slot h n‖^2=(∫ p, ‖jet p h‖^2∂ν)^n := by
    calc _ = _ := lp_sq _
         _ = ∫ p, ‖productTest (n:=n) h p‖^2∂νpow n := integral_congr_ae ((evaluate_slot h).mono (fun x hx=> by change ‖slot h n x‖^2 = _; rw [hx]))
         _ = _ := by
             have := integral_fintype_prod_eq_prod (ι:=Fin n) (fun i p=> ‖jet p h‖^2) (μ:=fun _ => ν)
             rw [Finset.prod_const,Finset.card_fin] at this -- #check
             simpa only [productTest,tensor_sq] using this

lemma expense (h : SlotField m) : ‖slot h n‖ ^2 = cost h n := by
    unfold cost; rw [pow_mul,norm_slot_sq h (n:=n),norm_slot_sq h (n:=1),pow_one] -- 2*n is numerals

def coefficient (n : ℕ) := (I^n) * ((Real.sqrt (n.factorial:ℝ)):ℂ)⁻¹
lemma coefficient_eq (n : ℕ) : ‖coefficient n‖^2=(n.factorial:ℝ)⁻¹ := by simp [coefficient,norm_pow]
lemma coeff_sums (f : SlotField m) : Summable (fun n : ℕ=> ‖coefficient n‖^2*cost f n) := by
   convert Real.summable_pow_div_factorial (‖slot f 1‖^2) using 1
   funext n; simp_rw [coefficient_eq,cost,pow_mul]; exact inv_mul_eq_div ..
noncomputable def sail (f : SlotField m) : Sum m := by
   refine ⟨(fun n=> coefficient n • slot f n), memℓp_gen_iff (by norm_num) |>.2 ?_⟩
   simp_rw [show (2:ℝ≥0∞).toReal=(↑(2:ℕ):ℝ) by norm_num,Real.rpow_natCast,norm_smul,mul_pow,expense]
   exact coeff_sums f
lemma sail_eval (f : SlotField m) (n : ℕ) : sail f n = coefficient n • slot f n := rfl
/-- Coherent vacuum vectors of the stated comparison for the Hermitian electric tests;
for the reverse-Weyl action on Ω use `pulse (-f)`. -/
noncomputable def pulseFactor (f : SlotField m) : ℝ := Real.exp ((-1/2)*‖slot f 1‖^2)
noncomputable def pulse (f : SlotField m) : Sum m := (pulseFactor f:ℂ) • sail f
lemma pulseFactor_pos (f : SlotField m) : 0<pulseFactor f := Real.exp_pos _
lemma pulse_eval (f : SlotField m) (n : ℕ) : pulse f n = ((pulseFactor f:ℂ)*coefficient n) • slot f n := by
   simp only [pulse, lp.coeFn_smul,Pi.smul_apply, sail_eval,mul_smul]

lemma sum_decompose (x y : Sum m) : inner ℂ x y = ∑' i : ℕ, inner ℂ (x i) (y i) := lp.inner_eq_tsum ..

-- Candidate exact relative identity
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
noncomputable def fockVac (m : ℕ) : Sum m := pulse 0
noncomputable def phase (a : E4) (p : Cords n) := Probe.plane (total p) a
lemma plane_bound (a : E4) (p : Cords n) : ‖phase a p‖ ≤ 1 := by simp [phase]
def transversality (z : Wave m n) : Prop := ∀ᵐ x ∂νpow n, ∀ i (J : Fin n→Mode m),
    ∑ j : SpaceAxis, (((x i j):ℝ):ℂ)*(z x) (Function.update J i ((J i).1, j))=0
def symmetry (z : Wave m n) : Prop := ∀ π : Equiv.Perm (Fin n), ∀ᵐ x ∂νpow n, ∀ I : Fin n→Mode m,
    (z (x ∘ π)) (I ∘ π)=z x I
def ElectricTest (f : SlotField m) : Prop := ∀ i, (Boundary.Probe.bar (f i))=(f i) ∧ HasCompactSupport (⇑(f i))
-- spacelike test names check
noncomputable def supportE (f : SlotField m) := ⋃ i, tsupport (f i)
def openApart (h : SlotField m) (f : Test4) : Prop := ∃ U V : Set E4, IsOpen U ∧ IsOpen V ∧ supportE h⊆U ∧ tsupport f⊆V ∧
       ∀ x∈closure U, ∀ y∈closure V, (x-y) ∈ Mink.spacelike

/-- Vacancy and translation conditions needed only on the trace waves. Inner product
linear in the second slot. `openApart` includes translated small `f` regions with all
finite unions for electric lists; `V` may here be a ball instead. -/
def matrixLocal (w : Test4→ Sum m) (δ : ℝ) : Prop := ∀ (f : Test4), CC f → ∀ (h: SlotField m), ElectricTest h → (
       ∃ U : Set E4, IsOpen U ∧ supportE h⊆U ∧ tsupport f⊆Metric.ball 0 δ ∧
       ∀ x∈closure U, ∀ y∈Metric.closedBall 0 δ, (x-y) ∈ Mink.spacelike) →
       inner ℂ (pulse (-h)) (w f) = inner ℂ (w (Probe.bar f)) (pulse h)
structure FieldImage (w : Test4→L[ℂ] Sum m) : Prop where
  across (f : Test4) (n : ℕ) : transversality (w f n)
  symmetric (f : Test4) (n : ℕ) : symmetry (w f n)
  covariance (f : Test4) (a : E4) (n : ℕ) : ∀ᵐ p : Cords n ∂νpow n, w (Probe.ahead a f) n p = phase a p • w f n p
  compatible (G : Finset (SlotField m)) : (∀ h∈G, supportE h ⊆ Mink.spacelike ∧ ∀ i, CC (h i)) → ∃ δ > 0,
       ∀ᶠ (ε : ℝ) in 𝓝[>] 0, ε<δ ∧ matrixLocal w ε

abbrev θw {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order} (Y : Spec.Final C f S)
    (e : ℝ) := oneWave Y (S.pin 4 (theta Y e))
abbrev fockWave {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order} (Y : Spec.Final C f S)
    (e : ℝ) (U : Y.action.operators.H →ₗᵢ[ℂ] Sum m) := U.toContinuousLinearMap.comp (θw Y e)
structure Comparison {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order} (Y : Spec.Final C f S) (e : ℝ)
    (U : Y.action.operators.H →ₗᵢ[ℂ] Sum m) : Prop where
  vacc : U Y.action.operators.omega.val = fockVac m
  data : FieldImage (fockWave Y e U)

/-- Full intertwining and Eq. nfl for open regions imply the used part. This is
one formulation of the implication directly in the vacuum-test convention
(q and coherent vectors as in the manuscript); if Weyls preserve these vacuum
vectors under action and satisfy `W(-h) = W(h)^*`, lhs is exactly the same pairing. -/
lemma comparison_of_full {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order} (Y : Spec.Final C f S) (e : ℝ)
    (U : Y.action.operators.H →ₗᵢ[ℂ] Sum m) (hp : U Y.action.operators.omega.val = fockVac m)
    (ht : ∀ g n, transversality (U g n)) (hv : ∀ g n, symmetry (U g n))
    (hc : ∀ g a n, ∀ᵐ p : Cords n ∂νpow n, U (Y.action.action.orbit.translation a g) n p =
      phase a p • U g n p) (hd : ∀ (h:SlotField m) (φ:Test4), CC φ → ElectricTest h → openApart h φ →
       inner ℂ (pulse (-h)) (U (θw Y e φ)) = inner ℂ (U (θw Y e (Probe.bar φ))) (pulse h)) : Comparison Y e U := by
   constructor
   · exact hp
   refine ⟨(fun φ n=> by change transversality (U (_:Y.action.operators.H) n); exact ht _ n), (fun φ n=> hv _ n), ?_,?_⟩
   · intro φ a n
     change ∀ᵐ p ∂_, U ((oneWave Y _) _) n p = _
     simp_rw [one_transports Y _ φ a]; exact hc _ _ _
   intro G hG; exact ⟨1,zero_lt_one, Filter.Eventually.mono (Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds (a:=1) (by norm_num : 0<(1:ℝ)))) fun ε hε=>⟨hε,fun φ hφ h hh ⟨U',hU,hp,hk,hl⟩=>
        hd h φ hφ hh ⟨U',Metric.ball 0 ε,hU,Metric.isOpen_ball,hp,hk,fun x hx y hy => hl x hx y ((closure_minimal
          Metric.ball_subset_closedBall Metric.isClosed_closedBall) hy)⟩⟩⟩
end YM.Trace.Shell
