import YM.AllOrder.FrameCost.Pair
import YM.OPE.Levy.Inverse
import YM.Pert.Scale.Engineering

/-!
# Relative step prices, all fine real scales

The Gram gives a short proof of quantitative comparison: read the same pair
at the two different lengths, on the free limit. Take the length ratio large,
then let the length tend to zero. The order here is important: uniform in
the length, not an estimate simultaneous as ratio tends to infinity! Later
absorb the constant by taking long *fixed* log steps.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.FrameCost
open Spec Function Filter Set Extraction Climb Table Ward Trace Trace.Pilot Analysis
open Leading Next.UVStress Maxwell Spin Push.FiniteDetection.Free OPE Pert.Scale Pert.Rigid
open Extra.FD Real
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable {F : Spec.Final C f S} {U : ℝ → FamilyFrame S} {g : ℝ → ℝ}
variable (h : Aligned F g U)
variable {d : ℕ}
local notation "free" => Bel C.book
set_option quotPrecheck false
local notation "E" => (Bel C.book).Field
local notation "L" => C.labels
local notation "ℓ" => FrameCost.length

-- reflection preserves scale; complex scalar positive
lemma gear_bar (a : ℝ) (x : E d) :
    Pert.Scale.gear L d a (Levy.reflect d x)=Levy.reflect d (Pert.Scale.gear L d a x) := by
    unfold Levy.reflect
    let T:=Signed.mirror timeAxis
    let c:= (freeTable C.labels).conj (Extra.FD.table_spin C.labels) d
    change Pert.Scale.gear L d a (wear L d T (c x))= wear L d T (c _)
    rw [wear_ride,wear_ride, ← gear_spin]; apply congrArg (rideO C.labels T.ortho d)
    exact (gear_conj C.labels x a).symm

local notation "gramFree" => fun x : Points 2 => Levy.linear₂ ((free).classMoment free (fun _=>d) x)
variable (B : RStage C.labels d)
lemma free_zoom_pair (i : Fin (B.m+1)) (x : Points 2) (hx : x ∈ conf 2)
      (z : ℝ) :
    let k := (B.w i).1
    (gramFree (exp z • x)) (B.b i) (Levy.reflect d (B.b i)) =
      (exp (-z * k)^2:ℝ) • (gramFree x (B.b i) (Levy.reflect d (B.b i))) := by
    intro k; let p:= B.b i; let q:= Levy.reflect d p; let T := (exp z : ℝ); let A:=Pert.Scale.gear L d T
    let w:= T^k; let w' := exp (-z*k)
    have hg: ∀ s: ℝ, (Real.exp s)^k=exp (s*k):= fun s=>by rw [mul_comm s _,Real.exp_nat_mul]
    have hw: w*w'=1:=by unfold w w' T; rw [hg,← exp_add,neg_mul,add_neg_cancel,exp_zero]
    let y:= exp z • x
    let X : E d →ₗ[ℂ] E d →ₗ[ℂ] ℂ := gramFree y
    have hA:A p=(w:ℂ) • p:= by unfold w; rw [Complex.ofReal_pow]; exact rare B i T
    have hu : X (A p) (A q)= gramFree x p q:= by
       have ht:=points_equ (F:=L) hx (d:=d) (![p,q]) (t:=T) (exp_pos z).ne'
       refine Eq.trans ?_ ht
       change (free).classMoment free _ y _=(free).classMoment free _ y _
       apply DFunLike.congr_arg _; funext j; fin_cases j <;> rfl
    have hq:A q=Levy.reflect d (A p):=gear_bar ..
    rw [hq,hA] at hu -- case
    have hz : (w^2:ℝ) • X p q=gramFree x p q:=by
       rw [quadratic d X] at hu
       rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]; change (↑(w^2):ℂ)*_= _; rw [Complex.ofReal_pow]; exact hu
    change X p q = (w'^2:ℝ) • _; rw [← hz,smul_smul,← mul_pow,mul_comm w' w,hw]; simp

/-- `U` wants same realH on both lengths. -/
abbrev relative (U : ℝ → FamilyFrame S) (d : ℕ) (t z : ℝ) :=
    (U (ℓ (t+z)) d).trans (U (ℓ t) d).symm
include h
lemma same_relative : ∀ᶠ t : ℝ in atTop, ∀ z:ℝ, 0 ≤ z → ∀ p:E d,
      let s := relative U d t z p
      leave d (U (ℓ t)) (ℓ t) s (Levy.reflect d s) =
        reader d (U (ℓ (t+z)) d) (ℓ (t+z)) (Real.exp z • detectors) p (Levy.reflect d p) := by
    have hx:= FrameCost.shrinking.eventually (h.respects d)
    obtain ⟨A,hA⟩ := eventually_atTop.1 hx
    filter_upwards [eventually_ge_atTop A] with t ht z hz p s
    have he := hA t ht; have hp := hA (t+z) (by linarith only [ht,hz])
    let W := U (ℓ t) d; let Q:=U (ℓ (t+z)) d
    have hw : W s=Q p:=LinearEquiv.apply_symm_apply ..
    have hL : W (Levy.reflect d s)=Q (Levy.reflect d p) := by
      unfold Levy.reflect; rw [he.1,he.2,hp.1,hp.2,hw]
    change S.classMoment S (fun _=> d) _ _= S.classMoment S _ (_ • (_ • detectors)) _
    rw [smul_smul, FrameCost.overshoot]
    exact DFunLike.congr_arg _ (show ![W s,W (Levy.reflect d s)] = ![Q p,Q (Levy.reflect d p)] from
         by rw [hw,hL])

variable {B}
/-- Usual all-path bounded-relative-span service. Also entering pose for sharp
 Gram steps. Can pay any constant for a fixed span. -/
lemma short_window (p : E d) (z : ℝ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ t in (atTop : Filter ℝ),
    ∀ a : ℝ, 0 ≤ a → a ≤ z → ‖relative U d t a p‖ ≤ A := by
    let q := Levy.reflect d p
    let x:= fun a:ℝ=>Real.exp a • detectors
    haveI : IsBoundedSMul ℝ (Points 2) := .of_norm_smul_le NormedSpace.norm_smul_le
    haveI : ContinuousSMul ℝ (Points 2) := IsBoundedSMul.continuousSMul
    let K:= x '' Set.Icc 0 z
    have hk:IsCompact K:=isCompact_Icc.image (show Continuous x by unfold x; fun_prop)
    have hv:K ⊆ conf 2:= by rintro _ ⟨i,_,rfl⟩; exact (enlarged (exp_pos i) detectors).1 detectors_in
    let v:=fun i:Fin 2=>(⟨d,![p,q] i⟩ : (free).Tag)
    obtain ⟨A,hA⟩:= hk.exists_bound_of_continuousOn ((smoothDisc (Free.hierarchy C.labels).smooth v).continuousOn.mono hv)
    obtain ⟨R,hR⟩:= eventually_atTop.1 (shrinking.eventually (compact_zero h v zero_lt_one hk hv))
    obtain ⟨C',hc,hB⟩:= coercive d h
    refine ⟨C'*(|A|+1)+1,by positivity,?_⟩
    filter_upwards [eventually_ge_atTop R,hB,same_relative (d:=d) h] with t ht he hθ a hp hz
    have hh := he (relative U d t a p); rw [hθ a hp p, readers] at hh
    have hK:x a∈K:= Set.mem_image_of_mem x ⟨hp,hz⟩
    have hu:= (norm_sub_norm_le (tableRead (U (ℓ (t+a))) (ℓ (t+a)) v (x a)) (disc v (x a))).trans (hR (t+a) (by linarith only [ht,hp]) (x a) hK).le
    have hx:‖tableRead (U (ℓ (t+a))) (ℓ (t+a)) v (x a)‖ ≤ |A|+1:= by linarith only [hu,hA (x a) hK,le_abs_self A]
    change _≤ _ * ‖tableRead (U _) _ v (x a)‖ at hh
    nlinarith only [hh,mul_le_mul_of_nonneg_left hx hc.le,sq_nonneg (‖relative U d t a p‖-1),hc,mul_nonneg hc.le (abs_nonneg A)]

/-- Price individual pure input columns, with a constant **independent** of
 chosen log ratio `z`. But onset threshold can of course depend on that
 arbitrarily large test distance. -/
lemma pure_step (B : RStage C.labels d) (i : Fin (B.m+1)) : ∃ A : ℝ, 0 ≤ A ∧ ∀ z : ℝ, 0≤z →
    ∀ᶠ t in (atTop : Filter ℝ), ‖relative U d t z (B.b i)‖ ≤ A * exp (-z * (B.w i).1) := by
    obtain ⟨C',hc,hB⟩ := coercive d h
    let x:= B.b i; let y:= Levy.reflect d x; let a:= ‖Levy.target (C:=C) d x y‖+1
    have ha:0<a:= lt_of_le_of_lt (norm_nonneg _) (lt_add_one _)
    refine ⟨ Real.sqrt (C'*a),Real.sqrt_nonneg _,fun z hz=>?_⟩
    let v:=fun i : Fin 2=>(⟨d,![x,y] i⟩ : (free).Tag)
    let M:=exp z•detectors; let w:=exp (-z*(B.w i).1); have hw : 0<w:=exp_pos _
    have hm:M∈conf 2 := (enlarged (exp_pos z) detectors).1 detectors_in
    obtain ⟨R,hR⟩:= eventually_atTop.1 (shrinking.eventually (compact_zero h v (sq_pos_of_pos hw) isCompact_singleton (singleton_subset_iff.mpr hm)))
    filter_upwards [eventually_ge_atTop R,hB,same_relative (d:=d) h] with t ht he hφ
    let r := ℓ (t+z); let T := relative U d t z x
    have hh:= he T; rw [hφ z hz x, readers] at hh
    have hb : ‖disc v M‖ = w^2 * ‖Levy.target (C:=C) d x y‖ := by
       have hk : disc v M= w^2 • Levy.target (C:=C) d x y := free_zoom_pair B i detectors detectors_in z
       rw [hk,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    have hu : ‖tableRead (U r) r v M‖≤w^2*a := by
       have h:= (norm_sub_norm_le (tableRead (U r) r v M) (disc v M)).trans (hR (t+z) (by linarith only [ht,hz]) M rfl).le
       rw [hb] at h; unfold a; linarith only [h]
    let p:=Real.sqrt (C'*a)
    change ‖T‖ ≤ p*w
    have hv:p^2=C'*a:=Real.sq_sqrt (mul_nonneg hc.le ha.le)
    refine le_of_pow_le_pow_left₀ (n:=2) (by decide) (mul_nonneg (Real.sqrt_nonneg _) hw.le) ?_
    rw [mul_pow,hv]; exact hh.trans ((mul_le_mul_of_nonneg_left hu hc.le).trans_eq (by ring))
end YM.AllOrder.FrameCost
