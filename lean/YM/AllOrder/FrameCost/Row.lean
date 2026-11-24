import YM.AllOrder.FrameCost.Step
import YM.OPE.Levy.Transit
import YM.PertExtension.PureBasis

/-!
# Relative step for fixed physical rows

Frames preserve filtration exactly, so project to weight ≥ e **before**
paying. Leading relative coupling windows require all sufficiently fine
lengths in both directions to perform this estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.FrameCost
open Spec Function Filter Set Extraction Climb Table Ward Trace Trace.Pilot Analysis
open Leading Next.UVStress Maxwell Spin Push.FiniteDetection.Free OPE Pert.Scale Pert.RawLabels
open Extra.FD Labels Real Asymptotics
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Spec.Final C f S} {U : ℝ → FamilyFrame S} {g : ℝ → ℝ}
local notation "ℓ" => FrameCost.length
variable {d e : ℕ}
local notation "free" => Bel C.book
set_option quotPrecheck false
local notation "E" => (Bel C.book).Field

/-- Eigenspace label lowering lemma (adapt RG12/Roof/Echelons from its
 construction for d=e). -/
lemma from_low (B : RStage C.labels d) (i : Fin (B.m+1)) (he : e ≤ d) (h : (B.w i).1 ≤ e) :
    ∃ p : E e, (Free.scheme C.labels).rise he p = B.b i := by
  let V := C.labels
  obtain ⟨j,hj⟩ := B.corners i
  have hw : ((C.labels.level d).grades j).1 = (B.w i).1 := by
    refine MvPolynomial.IsWeightedHomogeneous.inj_right (φ:=writes C.labels d (B.b i)) ?_ ?_ (B.weighs i)
    · exact fun he => B.b.ne_zero i (writes_inj V d (he.trans ((writes V d).map_zero.symm)))
    intro v hv; exact congrArg Prod.fst ((weight_collapse v).symm.trans (at_alcove C.labels d j (hj ▸ hv)))
  let v:= PertExtension.Horizon.lowered (C.labels.level d) j
  refine ⟨enroll V e (raiseLabel _ (hw.trans_le h) v),?_⟩
  rw [hj]; apply UVNext.FreeStress.rise_embed V _ (Free.scheme_filters V)

variable (φ : S.Field d→ₗ[ℂ] ℂ)
def scale_row (U : ℝ → FamilyFrame S) (φ : S.Field d →ₗ[ℂ] ℂ) (t : ℝ) : (E d)→L[ℂ] ℂ :=
    LinearMap.toContinuousLinearMap (φ.comp (U (ℓ t) d).toLinearMap)
local notation "Z" => scale_row U φ
lemma traverse (t z : ℝ)(p:E d): Z (t+z) p= Z t (relative U d t z p):=
    congr_arg φ (LinearEquiv.apply_symm_apply (U (ℓ t) d) _).symm

private lemma total_norm_le {I V W : Type*} [Fintype I]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (B : Module.Basis I ℂ V) (T : V→L[ℂ] W) (p : I→ℝ) (h : ∀ i, ‖T (B i)‖ ≤ p i) :
    ‖T‖ ≤ ∑ i, p i * ‖(B.coord i).toContinuousLinearMap‖ := by
    have hp i : 0 ≤ p i := (norm_nonneg _).trans (h i)
    refine ContinuousLinearMap.opNorm_le_bound T
       (Finset.sum_nonneg (fun i _ => mul_nonneg (hp _) (norm_nonneg _))) fun v => ?_
    calc ‖T v‖ = ‖∑ i, B.repr v i • T (B i)‖ := by simp_rw [←map_smul, ←map_sum, B.sum_repr]
         _ ≤ _ := (norm_sum_le ..).trans (by
            rw [Finset.sum_mul]; refine Finset.sum_le_sum fun i _ => ?_
            rw [norm_smul, mul_comm (‖_‖:ℝ), mul_assoc]; exact mul_le_mul (h i)
              ((B.coord i).toContinuousLinearMap.le_opNorm v) (norm_nonneg _) (hp _))

variable (he : e ≤ d) (hφ : ∀ p ∈ Levy.planeAt (U:=F.sector.derivatives) e he, φ p = 0) (h : Aligned F g U)
include hφ he h
lemma omit_slot (B : RStage C.labels d) (i : Fin (B.m+1)) (hp : (B.w i).1 < e) :
    ∀ᶠ t : ℝ in atTop, Z t (B.b i)=0 := by
  cases e with
  | zero => omega
  | succ e =>
    let hs := (Nat.le_succ e).trans he
    obtain ⟨p,hp⟩:= from_low B i hs (Nat.le_of_lt_succ hp)
    filter_upwards [shrinking.eventually (h.nested e d hs)] with t ht
    apply hφ (U (ℓ t) d (B.b i))
    rw [← hp,ht]
    exact LinearMap.mem_range_self (F.sector.derivatives.rise hs) _

lemma row_start : ∃ A : ℝ, 0≤A ∧ ∀ z : ℝ, 0≤z →
    ∀ᶠ t : ℝ in atTop, ‖Z (t+z)‖ ≤ ‖Z t‖*(A*exp (-e*z)) := by
    let B:= recorded C.labels d
    choose c hc hC using pure_step h B
    refine ⟨∑ i, c i * ‖(B.b.coord i).toContinuousLinearMap‖,
       Finset.sum_nonneg (fun i _=>mul_nonneg (hc i) (norm_nonneg (B.b.coord i).toContinuousLinearMap)), fun z hz=> ?_⟩
    have he' i : ∀ᶠ t in atTop, ‖Z (t+z) (B.b i)‖ ≤ ‖Z t‖* (c i * exp (-e*z)) := by
        by_cases ht : (B.w i).1 < e
        · filter_upwards [(show Tendsto (fun t:ℝ=>t+z) atTop atTop from tendsto_atTop_mono (f:=id) (fun _=>le_add_of_nonneg_right hz) tendsto_id).eventually (omit_slot φ he hφ h B i ht)] with t H
          rw [H,norm_zero]; exact mul_nonneg (norm_nonneg (Z t)) (mul_nonneg (hc i) (exp_pos _).le)
        filter_upwards [hC i z hz] with t hx
        rw [traverse]; apply le_trans ((Z t).le_opNorm _)
        apply mul_le_mul_of_nonneg_left (hx.trans (mul_le_mul_of_nonneg_left _ (hc _))) (norm_nonneg _)
        apply exp_monotone
        have he₁ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (le_of_not_gt ht) : (e:ℝ) ≤ _) hz
        linarith
    filter_upwards [eventually_all.mpr he'] with t ht
    apply le_trans (total_norm_le B.b _ _ ht)
    apply le_of_eq; rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

omit he hφ in
lemma row_continue (z : ℝ) : ∃ A : ℝ, 0≤A ∧ ∀ᶠ t : ℝ in atTop, ∀ a ∈ Icc 0 z,
    ‖Z (t+a)‖ ≤ ‖Z t‖*A := by
    let B := recorded C.labels d
    choose c hc hC using fun i=> short_window h (B.b i) z
    refine ⟨∑ i, c i * ‖(B.b.coord i).toContinuousLinearMap‖, Finset.sum_nonneg
       (fun i _=> mul_nonneg (hc i) (norm_nonneg (B.b.coord i).toContinuousLinearMap)), ?_⟩
    filter_upwards [eventually_all.mpr hC] with t ht a ha
    have he i : ‖Z (t+a) (B.b i)‖ ≤ ‖Z t‖*c i := by
       rw [traverse]; exact ((Z t).le_opNorm _).trans (mul_le_mul_of_nonneg_left (ht i a ha.1 ha.2) (norm_nonneg _))
    apply le_trans (total_norm_le B.b _ _ he)
    apply le_of_eq; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
end YM.AllOrder.FrameCost
