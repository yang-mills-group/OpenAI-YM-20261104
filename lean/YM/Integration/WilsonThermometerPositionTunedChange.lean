import YM.Integration.WilsonThermometerPositionTunedSurvey
import YM.Integration.WilsonPositionProgramSource

/-! Keep a whole occupied face on its genuine finite inversion measure when
changing the original submitted sections to those of its registered survey. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerPositionTunedChange
open Function Lattice Wilson Labels Source Source.Drops XSpace RegulatorIR.FVAAlt2
open PhysicalNext.Repeat.Legato FVA2
open WilsonThermometerPositionTunedSurvey
open scoped Classical BigOperators ContDiff
variable {G:Gauge} (R:Run G) (W:Initialize G) (P:XSpace.Period) (T:P.Tree)
variable {I:Type} [Fintype I] [LinearOrder I] (d:I→ℕ) (z:I→ Cover)
variable (a : (j:I) → (R.family.labels.level (d j)).Index)

def letter (j:I) (u:T.Field G) : ℂ :=
  (prepared R W (d j)).places (Pi.single (a j) 1) (wrap P.side (z j)) (T.links u)
def earned : Bare.Series T G := ∏j, row R W (d j) P T (wrap P.side (z j)) (a j)
def change (u:T.Field G) : ℂ :=
  (WilsonPositionProgramCopyTop.planted R P d z a (T.links u):ℂ) -
    ∏ j, letter R W P T d z a j u

omit [Fintype I] [LinearOrder I] in
theorem smooth (j:I) : ContDiffAt ℝ ω (letter R W P T d z a j) 0 := by
  change ContDiffAt ℝ ω (fun u =>
    (prepared R W (d j)).places (Pi.single (a j) 1) (wrap P.side (z j)) (T.links u)) 0
  rw [← (R.family.labels.level (d j)).coords_basis (a j)]
  have h:=(represents R W (d j)).2.2 ((R.family.labels.level (d j)).basis (a j))
  have eq : (fun u:T.Field G => (prepared R W (d j)).places
      ((R.family.labels.level (d j)).coords ((R.family.labels.level (d j)).basis (a j))) (wrap P.side (z j)) (T.links u)) =
    Bare.labelFunction T (W.surveys (d j)) (wrap P.side (z j)) ((R.family.labels.level (d j)).basis (a j)).val :=
    funext fun u=>h (expandAt (wrap P.side (z j)) (T.links u))
  rw [eq]
  exact Bare.label_smooth ..

omit [Fintype I] [LinearOrder I] in
private theorem smooth_prod (s:Finset I) : ContDiffAt ℝ ω (∏j∈s,letter R W P T d z a j) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact contDiffAt_const
  | insert j s fresh ih => rw [Finset.prod_insert fresh]; exact (smooth R W P T d z a j).mul ih

omit [Fintype I] [LinearOrder I] in
private theorem prod (s:Finset I) :
    Taylor.expandTaylor (T.basis G) (∏ j∈s, letter R W P T d z a j) =
      ∏ j∈s, Taylor.expandTaylor (T.basis G) (letter R W P T d z a j) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    change Taylor.expandTaylor (T.basis G) (fun _ => (1:ℂ)) = 1
    simpa using Taylor.expand_const (T.basis G) (1:ℂ)
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    rw [Taylor.expand_mul _ (smooth R W P T d z a i)
      (smooth_prod R W P T d z a s),ih]

omit [LinearOrder I] in
theorem shipped :
    Taylor.expandTaylor (T.basis G) (∏j,letter R W P T d z a j) =
      PowerSeries.X^(Kick.depthF Finset.univ d a) * earned R W P T d z a := by
  rw [prod,earned,Kick.depthF,← Finset.prod_pow_eq_pow_sum,← Finset.prod_mul_distrib]
  · apply Finset.prod_congr rfl
    intro j _
    exact (shifted R W (d j) P T (wrap P.side (z j)) (a j)).symm

private theorem expand_sub {f h:T.Field G→ℂ} (hf:ContDiffAt ℝ ∞ f 0) (hh:ContDiffAt ℝ ∞ h 0) :
    Taylor.expandTaylor (T.basis G) (f-h) =
      Taylor.expandTaylor (T.basis G) f-Taylor.expandTaylor (T.basis G) h := by
  apply PowerSeries.ext
  intro n
  apply Taylor.from_real (T.basis G)
  intro u
  let L:ℝ→L[ℝ]T.Field G := (ContinuousLinearMap.id ℝ ℝ).smulRight u
  have hn : (n:ℕ∞ω) ≤ ∞ := by norm_cast; exact le_top
  have lines (v:T.Field G→ℂ) (good:ContDiffAt ℝ ∞ v 0) :
      ContDiffAt ℝ (↑n) (fun r:ℝ=>v (r • u)) 0 := by
    exact ContDiffAt.comp (f:=L) 0 (by simpa using good.of_le hn) L.contDiff.contDiffAt
  simp only [map_sub]
  rw [Taylor.line_coeff (T.basis G) (f:=f-h) n u ((hf.sub hh).of_le hn),
    Taylor.line_coeff (T.basis G) (f:=f) n u (hf.of_le hn),
    Taylor.line_coeff (T.basis G) (f:=h) n u (hh.of_le hn)]
  change _ * iteratedDeriv n (fun r:ℝ=>f (r•u) - h (r•u)) 0 = _
  rw [iteratedDeriv_fun_sub (lines f hf) (lines h hh),mul_sub]

/-- The difference is one actual signed inversion insertion. The power at its
public end is the sum of the ranks of precisely the chosen axes in this face. -/
theorem signed :
    WilsonPositionProgramCopyTop.normalized R P d z a T -
      PowerSeries.X^(Kick.depthF Finset.univ d a) * Bare.normalized T G (earned R W P T d z a) =
    Bare.normalized T G (Taylor.expandTaylor (T.basis G) (change R W P T d z a)) := by
  let f:T.Field G→ℂ := Complex.ofRealCLM ∘ (WilsonPositionProgramCopyTop.planted R P d z a ∘ T.links)
  let h:T.Field G→ℂ := ∏j, letter R W P T d z a j
  have hf:ContDiffAt ℝ ∞ f 0 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (XPos.hears T (WilsonPositionProgramCopyTop.allowed R P d z a))
  have hh:ContDiffAt ℝ ∞ h 0 := (smooth_prod R W P T d z a Finset.univ).of_le le_top
  have diff : change R W P T d z a = f-h := funext fun u=> by simp [change,f,h,Finset.prod_apply]
  rw [diff,expand_sub P T hf hh,map_sub]
  change Bare.normalized T G _ - _ = Bare.normalized T G _ - Bare.normalized T G (Taylor.expandTaylor (T.basis G) h)
  rw [show Taylor.expandTaylor (T.basis G) h=_ from shipped R W P T d z a]
  rw [← Bare.normalized_scalar T, Bare.scalar,map_pow,PowerSeries.map_X]

end YM.Integration.WilsonThermometerPositionTunedChange
end
