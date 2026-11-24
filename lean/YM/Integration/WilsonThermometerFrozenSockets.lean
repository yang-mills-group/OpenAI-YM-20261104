import YM.Integration.WilsonOriginalStarGradedScene
import YM.WilsonCoeffUV.Marked.Paths.Vector

/-! The actual top thermometer alphabet has a separately declared raw word
for each socket. Its previously fitted coefficient and two measured scales
stay fixed when the formal coupling is varied. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerFrozenSockets
open Finset Lattice Wilson RG Marker LocalComparison QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Sunrise
open PhysicalNext.Repeat.Legato ActualRunCurvaturePackets NativeCurvatureTensor
open WilsonOriginalStarSceneWords WilsonOriginalStarGradedScene
open WilsonOriginalStarSceneRows WilsonOriginalStarLaurentWallet
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {V T : Type} [DecidableEq V] [Fintype V]
  (d : V→ℕ) {n : Side} (o : V→Site n) (σ g τ : ℝ)
  (v : (j:V)→R.family.label (d j)) (t : V→T→ℂ) (pos : ∀j, 0<d j)
local notation "M" => words R d o σ g τ v t pos

omit [DecidableEq V] [Fintype V] in
theorem stamp (i : Entry R d) : (credit R d pos i).stamp = d (root R d i)+1-pole R d i := by
  have hr := low R d i
  have hp := pole_grade R d i
  change (rank R d i-pole R d i)+d (root R d i)+1-rank R d i = _
  omega

omit [DecidableEq V] [Fintype V] in
theorem separated (i : Entry R d) :
    scalar R d g τ v i = (((g/τ)^(pole R d i):ℝ):ℂ)*scalar R d 1 1 v i := by
  rcases i with j|⟨j,h⟩
  · simp [scalar,pole]
  · simp [scalar,pole,WilsonOriginalStarLaurentWallet.coefficient,mul_assoc]

/-- At any copied site the painter and atom normalization cancel before
taking a coefficient or conditional expectation. -/
theorem painted {f : Side} (i : Entry R d) (s : ℝ) (x : T) (z : Site f) (U : Config G f) :
    (M i).paint x*↑(Loan.letter (M i).lamp (M i).atom z s U) =
      (t (root R d i) x * scalar R d 1 1 v i)*
      (((g/τ)^(pole R d i)*s^(d (root R d i)+1-pole R d i):ℝ):ℂ)*
      ↑((raw R d i).unmasked U z) := by
  let a := raw R d i
  let Z := normalizer a σ
  have shell : (unitAtom a σ).unmasked U z = Z⁻¹*a.unmasked U z := evaluated a σ _
  have nz : ((Z:ℂ) * (Z:ℂ)⁻¹) = 1 := mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (positive a σ).ne')
  change ((Z:ℂ)*scalar R d g τ v i*t (root R d i) x)*
    ↑(s^(credit R d pos i).stamp * (unitAtom a σ).unmasked U z) = _
  rw [stamp,separated R d g τ v,shell]
  simp only [Complex.ofReal_mul,Complex.ofReal_inv]
  change _ = _ * _ * (a.unmasked U z:ℂ)
  linear_combination (t (root R d i) x*scalar R d 1 1 v i*
    ((g/τ)^(pole R d i):ℝ)*(s^(d (root R d i)+1-pole R d i):ℝ)*(a.unmasked U z:ℂ))*nz

/-- Native Wilson path data of precisely the same real socket, before its
complex test and salary scalar. -/
def comet (i : Entry R d) : WilsonCoeffUV.Mer.Rolls.Comet G ℝ (rank R d i) :=
  ⟨(raw R d i).leg,(raw R d i).coeff⟩

omit [DecidableEq V] [Fintype V] in
theorem identical (i : Entry R d) :
    WilsonCoeffUV.Mer.Rolls.dip (comet R d i) (ContinuousLinearMap.id ℝ ℝ) = raw R d i := rfl


open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Mosaic.Near

omit [DecidableEq V] [Fintype V] in
/-- A coupling grade of the actual finite socket reads precisely rank
`h + pole` of its raw Wilson path. This keeps all periodic path aliases. -/
theorem finite_grade (i : Entry R d) (f : Side) (h : ℕ) :
    (volumeR (comet R d i) (rank R d i - pole R d i)).1 f h =
      if rank R d i - pole R d i ≤ h then
        shine (sapR (comet R d i) f (h+pole R d i)) else 0 := by
  unfold volumeR moved
  by_cases head : rank R d i - pole R d i ≤ h
  · have hr := low R d i
    have pos : rank R d i + (h - (rank R d i-pole R d i)) = h+pole R d i := by omega
    simp only [if_pos head]
    exact congrArg (fun l => shine (sapR (comet R d i) f l)) pos
  · simp only [if_neg head]

omit [DecidableEq V] [Fintype V] in
theorem cover_grade (i : Entry R d) (h : ℕ) :
    (volumeR (comet R d i) (rank R d i - pole R d i)).2 h =
      if rank R d i - pole R d i ≤ h then
        shine (august (comet R d i) (h+pole R d i)) else 0 := by
  unfold volumeR moved
  by_cases head : rank R d i - pole R d i ≤ h
  · have hr := low R d i
    have pos : rank R d i + (h - (rank R d i-pole R d i)) = h+pole R d i := by omega
    simp only [if_pos head]
    exact congrArg (fun l => shine (august (comet R d i) l)) pos
  · simp only [if_neg head]

end YM.Integration.WilsonThermometerFrozenSockets
