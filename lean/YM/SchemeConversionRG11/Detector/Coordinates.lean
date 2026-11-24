import YM.SchemeConversionRG11.Read.Supply

/-!
# Local free-orbit coordinates, simultaneously for data and frame

Use real tensor charts for the jets. `Poll.measured` shows the same tests have a nonsingular
Jacobian also in the implemented `Position` Board (complex-array sampling).
-/

set_option autoImplicit false
noncomputable section

namespace YM.SchemeConversionRG11.Detector.Poll
open Function Filter Maxwell Issue Series Pert.Position Affine
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {F : Labels.Frames G} {d : ℕ} (Q : Poll F d)

/-- Input to this chart: per-slot tensor data. Test-profile conditions are frozen in Q. -/
abbrev Inputs := (i : Fin Q.tests) → Tape F d (Q.table i).r ℂ

def getTest (A : Issue F d) : Series Q.Inputs :=
  fun j i ↦ A (Q.table i).r (Q.table i).f j

def blank : Q.Inputs := fun i ↦ gaussian F d (Q.table i).f

def cursorL : (Fin Q.tests → ℝ) →L[ℝ] Buffer F d :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := Fin _ → ℝ) (F' := Buffer F d) Q.pointer

def tapeL (i : Fin Q.tests) : Q.Inputs →L[ℝ] Tape F d (Q.table i).r ℂ := ContinuousLinearMap.proj i

/-- Raw (already framed) data currency. -/
def prices (v : Q.Inputs) (i : Fin Q.tests) : ℝ := (v i (Q.table i).p).re

lemma pricesSmooth : ContDiff ℝ ω Q.prices := by
  apply contDiff_pi.mpr
  intro i
  let L := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (Q.table i).r ↦ E F d) ℂ ((Q.table i).p))
  have hi : ContDiff ℝ ω (tapeL Q i) := ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Q.Inputs) (F:=Tape F d (Q.table i).r ℂ) _
  have hl : ContDiff ℝ ω (fun p : Tape F d (Q.table i).r ℂ ↦ L p) :=
    ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Tape F d (Q.table i).r ℂ) (F:=ℂ) L
  have hz := Complex.reCLM.contDiff.comp (hl.comp hi)
  exact hz

def fareL : Q.Inputs →L[ℝ] Buffer F d :=
  Q.cursorL.comp (ContinuousLinearMap.pi fun i ↦ (Complex.reCLM.comp
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin (Q.table i).r ↦ E F d) ℂ ((Q.table i).p))).comp (tapeL Q i))

theorem fare_at (v : Q.Inputs) : Q.fareL v = Q.pointer (Q.prices v) := rfl

def resolve (p : Q.Inputs × Buffer F d) : Q.Inputs :=
  fun i ↦ Tape.put p.2 (p.1 i)

lemma resolving : ContDiff ℝ ω Q.resolve := by
  apply contDiff_pi.mpr
  intro i
  let K (t : Q.Inputs × Buffer F d) := (t.2, t.1 i)
  have hi : ContDiff ℝ ω (fun t : Q.Inputs × Buffer F d ↦ t.1 i) :=
    (ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Q.Inputs) (F:=Tape F d (Q.table i).r ℂ) (tapeL Q i)).comp contDiff_fst
  have hK : ContDiff ℝ ω K := contDiff_snd.prodMk hi
  exact Tape.placing.comp hK

def scan : Q.Inputs × Buffer F d → Buffer F d := Q.fareL ∘ Q.resolve

theorem scanner : ContDiff ℝ ω Q.scan := by
  have he : ContDiff ℝ ω Q.fareL := ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=Q.Inputs) (F:=Buffer F d) Q.fareL
  exact he.comp Q.resolving

lemma sample_deriv (B : Buffer F d) (i : Fin Q.tests) : HasDerivAt
    (fun t : ℝ ↦ Q.prices (Q.resolve (Q.blank,t • B)) i) (feedback F d (Q.table i) B) 0 := by
  let A := gaussian F d (Q.table i).f
  let q := (Q.table i).p
  let w := fun j ↦ B.val (q j)
  have he : (fun t : ℝ ↦ Q.prices (Q.resolve (Q.blank,t • B)) i) =
    Complex.reCLM ∘ (A ∘ fun t : ℝ ↦ q + t • w) := rfl
  have hD : HasDerivAt (fun t : ℝ ↦ q + t • w) w 0 := by
    apply HasDerivAt.const_add
    convert! (hasDerivAt_id' (0 : ℝ)).smul_const w using 1; simp
  have hA : HasFDerivAt A (A.linearDeriv q) (q + (0:ℝ) • w) := by rw [zero_smul,add_zero]; exact A.hasFDerivAt q
  rw [he]
  convert! Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hA.comp_hasDerivAt 0 hD) using 1
  -- definitions agree directly (at the multilinear free array)

set_option maxHeartbeats 500000 in
theorem checked (B : Buffer F d) : fderiv ℝ Q.scan (Q.blank,0) (0,B) = B := by
  let x (t : ℝ) : Q.Inputs × Buffer F d := (Q.blank, t • B)
  have h : HasDerivAt x (0,B) 0 := by
    have hd : HasDerivAt (fun t : ℝ ↦ t • B) B 0 := by
      convert! (hasDerivAt_id' (0:ℝ)).smul_const B using 1; simp
    have hc : HasDerivAt (fun _ : ℝ ↦ Q.blank) 0 0 := hasDerivAt_const (0:ℝ) Q.blank
    have hh := HasDerivAt.prodMk (𝕜:=ℝ) (F:=Q.Inputs) (G:=Buffer F d) hc hd
    exact hh
  have he : HasFDerivAt Q.scan (fderiv ℝ Q.scan (Q.blank,0)) (x 0) := by
    rw [show x 0 = (Q.blank,0) by simp [x]]; exact (Q.scanner.differentiable (by simp) _).hasFDerivAt
  let J := fun t : ℝ ↦ prices Q (Q.resolve (x t))
  have hQ : HasFDerivAt Q.cursorL Q.cursorL (J 0) := ContinuousLinearMap.hasFDerivAt (𝕜:=ℝ) _
  have hK : HasDerivAt (Q.scan ∘ x) (Q.pointer (fun i ↦ feedback F d (Q.table i) B)) 0 := by
    have hz : HasDerivAt J (fun i ↦ feedback F d (Q.table i) B) 0 := hasDerivAt_pi.mpr (fun i ↦ sample_deriv Q B i)
    have H := hQ.comp_hasDerivAt (𝕜:=ℝ) (F:=Fin Q.tests → ℝ) (E:=Buffer F d) 0 hz
    exact H
  rw [Q.checks B] at hK
  exact (he.comp_hasDerivAt (𝕜:=ℝ) (F:=Q.Inputs × Buffer F d) (E:=Buffer F d) 0 h).unique hK

theorem effective : (fderiv ℝ Q.scan (Q.blank,0) ∘L .inr ℝ Q.Inputs (Buffer F d)).IsInvertible :=
  ⟨ContinuousLinearEquiv.refl ℝ (Buffer F d), ContinuousLinearMap.ext fun B ↦ (checked Q B).symm⟩

abbrev Whole := Q.Inputs × Buffer F d

def location (v : Q.Whole) := (v.1, Q.scan v)

theorem chartRegular : ContDiff ℝ ω Q.location := contDiff_fst.prodMk Q.scanner

theorem coordinateRank : (fderiv ℝ Q.location (Q.blank,0)).IsInvertible := by
  let x : Q.Whole := (Q.blank,0)
  let L := fderiv ℝ Q.scan x
  let T := fderiv ℝ Q.location x
  have he : T = (ContinuousLinearMap.fst ℝ _ _).prod L :=
    (show HasFDerivAt Q.location _ x from (hasFDerivAt_fst (𝕜:=ℝ) (p:=x)).prodMk
      ((Q.scanner.differentiable (by simp) x).hasFDerivAt)).fderiv
  have hu (v : Q.Whole) : T v = (v.1,L (v.1,0) + v.2) := by
    rw [he]; change (v.1,L v) = _; congr 1
    conv_lhs => rw [show v = (v.1, (0:Buffer F d)) + ((0:Q.Inputs), v.2) by simp]
    rw [map_add]; exact congrArg (_ + ·) (Q.checked v.2)
  have hb : Bijective T := by
    constructor
    · intro i j h
      obtain ⟨h₁,h₂⟩ := Prod.mk_inj.mp (show (_,_) = (_,_) from (hu i).symm.trans (h.trans (hu j)))
      apply Prod.ext h₁; rw [h₁] at h₂; exact add_left_cancel h₂
    rintro ⟨i,j⟩
    refine ⟨(i,j - L (i,0)), ?_⟩
    rw [hu]; dsimp only; exact Prod.ext rfl (add_sub_cancel (L (i,0)) j)
  exact ⟨ContinuousLinearEquiv.ofBijective (E:=Q.Whole) (F:=Q.Whole) (𝕜:=ℝ) (𝕜':=ℝ) (σ:=RingHom.id ℝ) T (LinearMap.ker_eq_bot.mpr hb.1)
    (LinearMap.range_eq_top.mpr hb.2), by apply ContinuousLinearMap.ext; intro i; rfl⟩
end YM.SchemeConversionRG11.Detector.Poll
