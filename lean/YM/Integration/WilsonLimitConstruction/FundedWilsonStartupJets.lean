import YM.Integration.WilsonLimitConstruction.FundedWilsonStartup
import YM.Integration.ActualStartupInvoice
import YM.Integration.PositiveNormalizedRayJets
import YM.Integration.FullQLocalRenderedStepData

/-! Every coefficient through the original startup request agrees with the
prescribed complex formal fine action on every independent test. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonLimitConstruction.FundedWilsonStartupJets

open Function Filter Finset Lattice Wilson RG Exterior Marker
open PhysicalNext.Repeat.Legato WilsonStartup WilsonStartup.Start
open WilsonStartup.IterationFour YM.IterationFour YM.IterationFour.Vacuum
open Comparison.RG02 Comparison.RG02.Assembly
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FundedWilsonStartup
open scoped Classical BigOperators ContDiff Topology

variable {G : Gauge} {n : Side}

/-- The original unspent plaquette on each chart ray has its native
order r+3, uniformly as an order statement over all true faces. -/
theorem face (r : ℕ) (B : fieldDir G n 1) (p : Cell n) :
    GradeAt (r+3) (fun t : ℝ => leftOver (r+2) p (FundedWilsonGerm.ray B t)) := by
  have h : GradeAt (r+3) (leftOver (G := G) (r+2) p ∘ increment 1) :=
    ⟨(leftOver_smooth (r+2) p 1).contDiffAt,leftOver_flat (r+2) p⟩
  have ht : ContDiffAt ℝ ω (fun t : ℝ => t • collect G B) 0 := by fun_prop
  have hz : (0:ℝ) • collect G B = 0 := zero_smul _ _
  have he (t : ℝ) : increment 1 (t • collect G B) = FundedWilsonGerm.ray B t := by
    funext e
    simp [FundedWilsonGerm.ray, Precision.represent, increment, collect]
  exact (h.coarse ht hz).depends <| Eventually.of_forall fun t =>
    congrArg (leftOver (r+2) p) (he t)

/-- The complete finite unspent bank keeps that order, including its
original scalar and duplications among oriented plaquettes. -/
theorem unspent (S : Stage) (r : ℕ) (B : fieldDir G n 1) :
    GradeAt (r+3) (fun t : ℝ => residual S r (FundedWilsonGerm.ray B t)) := by
  have hu (s : Finset (Key n)) : GradeAt (r+3) (fun t : ℝ =>
      ∑ i ∈ s, leftOver (r+2) i.positive (FundedWilsonGerm.ray B t)) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (GradeAt.grade_zero (X := ℝ) (Y := ℝ) (r+3))
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (face r B i.positive).add ih
  have hc : GradeAt 0 (fun _ : ℝ => WilsonStartup.share * Design.bulk S.clip) :=
    GradeAt.unchecked contDiffAt_const
  change GradeAt (r+3) (fun t : ℝ => WilsonStartup.share * Design.bulk S.clip *
    ∑ i : Key n, leftOver (r+2) i.positive (FundedWilsonGerm.ray B t))
  simpa only [Nat.zero_add,smul_eq_mul] using hc.scale (hu Finset.univ)

theorem extension (R : Run G) (T : Campaign R) (N p r : ℕ) (hr : 2 ≤ r)
    (B : fieldDir G (R.family.side N p) 1) (C : FundedWilsonGerm.Curve B)
    (e : ℝ → ℂ) (k : ℕ) (hk : k ≤ r) (he : ContDiffAt ℝ k e 0)
    (heval : let X := R.family.path.rep N p N
      let S := R.family.path.levels.params N
      ∀ᶠ t : ℝ in 𝓝[>] 0, e t =
        ((X.path.inChannels X.clip X.p ((t^2)⁻¹) (FundedWilsonGerm.ray B t) +
          unmaskedLayers (album G _ X.p S r) t (FundedWilsonGerm.ray B t) : ℝ):ℂ)) :
    jet e k 1 = ((jet C.value k (1:ℝ) : ℝ) : ℂ) := by
  let S := R.family.path.levels.params N
  let D : ℝ → ℂ := fun t => -(residual S r (FundedWilsonGerm.ray B t) : ℂ)
  let V : ℝ → ℂ := Complex.ofRealCLM ∘ C.value
  have hd : GradeAt (r+3) D := GradeAt.linear_contact (-Complex.ofRealCLM) (unspent S r B)
  have hv : ContDiffAt ℝ k V 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (C.analytic.contDiffAt.of_le le_top)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, (e-V) t = (t^2)⁻¹ • D t := by
    filter_upwards [heval,pointed R T N p r hr B C] with t h₁ h₂
    change e t - (C.value t : ℂ) = _
    rw [h₁,← h₂]
    simp [D,S,Complex.real_smul]
  have hz := PositiveNormalizedRayJets.divided_coefficient
    (hd.lower (by omega : 2 ≤ r+3)) (he.sub hv) hpos
  rw [hd.jet_z 1 (by omega : 2+k < r+3)] at hz
  have hs : jet (e - V) k 1 = jet e k 1 - jet V k 1 := by
    simp only [jet, iteratedFDeriv_sub_apply he hv, _root_.sub_apply,smul_sub]
  change jet (e-V) k 1 = 0 at hz
  rw [hs,sub_eq_zero] at hz
  exact hz.trans (jet_apply_left Complex.ofRealCLM C.value k
    (C.analytic.contDiffAt.of_le le_top) 1).symm

/-- The same coefficient is the prescribed formal fine-action coefficient
for each independent test, with its original color family and input list. -/
theorem formal (R : Run G) (T : Campaign R) {V : Type} [DecidableEq V] [Fintype V]
    {marks : Census V} (J : FullQLocal.RenderedStep.Request V) (d : LocalFormal.Datum R.family marks)
    (hcut : d.cutoff = d.level+1) (r : ℕ) (hr : 2 ≤ r) (hrJ : J.order ≤ r)
    {colors : TestSpace J.tests → Bulk.Colors marks G (R.family.side (d.level+1) d.period)}
    {L : List (Piece G (R.family.side (d.level+1) d.period))} (H : FineWholeAction J d colors L)
    (hL : ∀ g U, unmaskedLayers L g U = unmaskedLayers (album G _
      (R.family.path.levels.budget (d.level+1)) (R.family.path.levels.params (d.level+1)) r) g U)
    (x : TestSpace J.tests) (B : fieldDir G (R.family.side (d.level+1) d.period) 1)
    (C : FundedWilsonGerm.Curve B) (k : ℕ) (hk : k ≤ J.order) :
    jet (fun t => H.formalInputExtension x t B) k 1 = ((jet C.value k (1:ℝ) : ℝ) : ℂ) := by
  have he : jet (fun t => H.inputExtension t B) k 1 =
      jet (fun t => H.formalInputExtension x t B) k 1 := H.input_whole x B k hk
  rw [←he]
  apply extension R T (d.level+1) d.period r hr B C _ k (hk.trans hrJ)
    ((H.input_extension_smooth B).of_le (by exact_mod_cast hk))
  have hm := R.makes.wilson.represents (d.level+1) d.period (d.level+1) le_rfl
  have hc : (R.family.path.rep (d.level+1) d.period (d.level+1)).clip =
      (R.family.path.levels.params (d.level+1)).clip := hm.clip
  have hp : (R.family.path.rep (d.level+1) d.period (d.level+1)).p =
      R.family.path.levels.budget (d.level+1) := hm.vac
  simpa only [hcut,hc,hp,FundedWilsonGerm.ray,hL] using H.input_extension_value B

/-- Numerical credit and the price point leave the original finite
program of ranks, supports, fields and weights literally unchanged. -/
theorem paid_render (P Q : BudgetPoint) (S : Stage) (r : ℕ) (width g : ℝ) (U : Config G n) :
    unmaskedLayers (ActualStartupInvoice.paidAlbum G n P S r width) g U =
      unmaskedLayers (album G n Q S r) g U := by
  simp only [unmaskedLayers,ActualStartupInvoice.paidAlbum,ActualStartupInvoice.repriceLayers,
    WilsonStartup.IterationFour.album,List.map_map]
  rfl

theorem paid (R : Run G) (T : Campaign R) {V : Type} [DecidableEq V] [Fintype V]
    {marks : Census V} (J : FullQLocal.RenderedStep.Request V) (d : LocalFormal.Datum R.family marks)
    (hcut : d.cutoff = d.level+1) (hr : 2 ≤ J.order) (P : BudgetPoint) (width : ℝ)
    {colors : TestSpace J.tests → Bulk.Colors marks G (R.family.side (d.level+1) d.period)}
    (H : FineWholeAction J d colors (ActualStartupInvoice.paidAlbum G _ P
      (R.family.path.levels.params (d.level+1)) J.order width))
    (x : TestSpace J.tests) (B : fieldDir G (R.family.side (d.level+1) d.period) 1)
    (C : FundedWilsonGerm.Curve B) (k : ℕ) (hk : k ≤ J.order) :
    jet (fun t => H.formalInputExtension x t B) k 1 = ((jet C.value k (1:ℝ) : ℝ) : ℂ) :=
  formal R T J d hcut J.order hr le_rfl H (fun g U => paid_render P _ _ _ width g U) x B C k hk

end YM.Integration.WilsonLimitConstruction.FundedWilsonStartupJets
end
