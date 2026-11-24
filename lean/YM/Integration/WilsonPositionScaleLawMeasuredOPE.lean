import YM.Integration.WilsonPositionScaleLawMeasuredOutput
import YM.Integration.WilsonPositionProgramTrialPublicJointPivotRestriction

/-! The exact numerical incoming and inverse outgoing changes in a finite OPE experiment.
The electing MS source already contains its own coupling substitution and its two formal field dictionaries. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawMeasuredOPE
open Filter Function Set Finset PowerSeries Maxwell Maxwell.Free XSpace XSpace.Normalize
open FVA2 FVA2.Register FVA2.Scale FVA2.Dframe FVA2.Position.OpenAxis
open FVA2.O FVA2.O.Score FVA2.O.Project
open MS MS.Land MS.Fleet MS.Theater MS.Book.Program
open WilsonPositionScaleLawMeasuredOutput (Space arms field)
open WilsonPositionProgramTrialPublicJointPivotRestriction (coordinates)
open WilsonMSDictionaryFarRead (converted cutoff)
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}{d h n:ℕ}

def incoming (v:Fin n→Sec G d)(b:Fin n→Toon G d)(x:MoveSpace G d) : ℂ :=
  ∏ i,field d x (arms d (v i)) (b i)
def outer (μ:Toon G h→ℂ)(j:Toon G h)(x:MoveSpace G h) : ℂ :=
  ∑ l,(field h x).inverse (arms h ((Daylight (Press.portDeck G) h) j)) l * μ l

theorem enters (v:Fin n→Sec G d)(b:Fin n→Toon G d) : ContDiff ℝ ω (incoming v b) := by
  apply contDiff_prod
  intro i _
  exact (contDiff_apply ℝ ℂ (b i)).comp ((WilsonPositionScaleLawMeasuredOutput.smooth d).clm_apply contDiff_const)
theorem returns (μ:Toon G h→ℂ)(j:Toon G h)(x:MoveSpace G h)(live:(field h x).IsInvertible) :
    ContDiffAt ℝ ω (outer μ j) x := by
  apply ContDiffAt.sum
  intro l _
  exact ((contDiff_apply ℝ ℂ l).contDiffAt.comp x
    ((WilsonPositionScaleLawMeasuredOutput.analytic x live).clm_apply contDiffAt_const)).mul contDiffAt_const
theorem outer_zero (μ:Toon G h→ℂ)(j:Toon G h) : outer μ j 0=μ j := by
  have ident:(1:Space G h→L[ℝ]Space G h).inverse=1:=
    ContinuousLinearMap.inverse_equiv (ContinuousLinearEquiv.refl ℝ _)
  unfold outer
  rw [WilsonPositionScaleLawMeasuredOutput.identity,ident]
  change (∑ l,(Daylight (Press.portDeck G) h).equivFun ((Daylight (Press.portDeck G) h) j) l * μ l)=μ j
  simp [Module.Basis.equivFun_self,ite_mul]

variable (Z:WilsonPrescription G)(M:MS_Data G (Plot (Press.portDeck G)))(ν:ℝ)
def row (below:h≤d)(q:ℕ)(φ:Test n)(v:Fin n→Sec G d)(μ:Toon G h→ℂ)(z:MoveSpace G d×ℝ) : ℂ :=
  ∑ a:Fin n→Toon G d,incoming v a z.1 * ∑j:Toon G h,
    cutoff q z.2 (converted Z M ν (fun i=>flash (a i)) φ (flash j)) * outer μ j (coordinates below z.1)

theorem polynomial (q:ℕ)(c:PowerSeries ℂ) : ContDiff ℝ ω (fun u:ℝ=>cutoff q u c) := by
  unfold cutoff
  apply ContDiff.sum
  intro k _
  exact (Complex.ofRealCLM.contDiff.pow k).mul contDiff_const

theorem admissible (below:h≤d) : ∀ᶠz:MoveSpace G d×ℝ in 𝓝 0,(field h (coordinates below z.1)).IsInvertible := by
  let k:MoveSpace G d×ℝ→MoveSpace G h:=fun w=>coordinates (G:=G) below w.1
  have cash:Continuous k := (coordinates (G:=G) below).continuous.comp continuous_fst
  have kz:k 0=0:=map_zero (coordinates (G:=G) below)
  have restore:=cash.tendsto (0:MoveSpace G d×ℝ)
  rw [kz] at restore
  exact restore.eventually (WilsonPositionScaleLawMeasuredOutput.invertible h)

theorem regular (below:h≤d)(q:ℕ)(φ:Test n)(v:Fin n→Sec G d)(μ:Toon G h→ℂ)(z:MoveSpace G d×ℝ)
    (live:(field h (coordinates below z.1)).IsInvertible) : ContDiffAt ℝ ω (row Z M ν below q φ v μ) z := by
  have low:ContDiffAt ℝ ω (fun w:MoveSpace G d×ℝ=>coordinates below w.1) z :=
    (coordinates below).contDiff.contDiffAt.comp z contDiffAt_fst
  have endRow (j:Toon G h) : ContDiffAt ℝ ω (fun w:MoveSpace G d×ℝ=>outer μ j (coordinates below w.1)) z :=
    by
      change ContDiffAt ℝ ω (outer μ j ∘ (fun w:MoveSpace G d×ℝ=>coordinates (G:=G) below w.1)) z
      exact (returns μ j _ live).comp z low
  have blend (a:Fin n→Toon G d) : ContDiffAt ℝ ω (fun w:MoveSpace G d×ℝ=>∑ j:Toon G h,
      cutoff q w.2 (converted Z M ν (fun i=>flash (a i)) φ (flash j)) * outer μ j (coordinates below w.1)) z := by
    apply ContDiffAt.sum
    intro j _
    exact ((polynomial q _).contDiffAt.comp z contDiffAt_snd).mul (endRow j)
  unfold row
  apply ContDiffAt.sum
  intro a _
  exact ((enters v a).contDiffAt.comp z contDiffAt_fst).mul (blend a)

theorem moving {ι:Type*}{l:Filter ι}(below:h≤d)(q:ℕ)(φ:Test n)(v:Fin n→Sec G d)
    (z:ι→MoveSpace G d×ℝ)(w:MoveSpace G d×ℝ)(arrive:Tendsto z l (𝓝 w))
    (μ:ι→Toon G h→ℂ)(m:Toon G h→ℂ)(paid:∀j,Tendsto (fun i=>μ i j) l (𝓝 (m j)))
    (live:(field h (coordinates below w.1)).IsInvertible):
    Tendsto (fun i=>row Z M ν below q φ v (μ i) (z i)) l (𝓝 (row Z M ν below q φ v m w)) := by
  unfold row
  have first:Tendsto (fun i=>(z i).1) l (𝓝 w.1) := (continuous_fst.tendsto w).comp arrive
  have second:Tendsto (fun i=>(z i).2) l (𝓝 w.2) := (continuous_snd.tendsto w).comp arrive
  have lower:Tendsto (fun i=>coordinates below (z i).1) l (𝓝 (coordinates below w.1)):=
    (coordinates below).continuous.continuousAt.tendsto.comp first
  apply tendsto_finsetSum
  intro a _
  apply ((enters v a).continuous.continuousAt.tendsto.comp first).mul
  apply tendsto_finsetSum
  intro j _
  apply ((polynomial q _).continuous.continuousAt.tendsto.comp second).mul
  unfold outer
  apply tendsto_finsetSum
  intro k _
  apply Tendsto.mul _ (paid k)
  exact (((contDiff_apply ℝ ℂ k).contDiffAt.comp _
    ((WilsonPositionScaleLawMeasuredOutput.analytic _ live).clm_apply contDiffAt_const)).continuousAt.tendsto).comp lower
theorem measured {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{dial:Bool}
    (matchSource:Main.Match Z simple M σ dial)(below:h≤d)(q:ℕ)(t:ℝ)(φ:Test n)(v:Fin n→Sec G d)(μ:Toon G h→ℂ):
    row Z M ν below q φ v μ (0,t) =
      ∑ a:Fin n→Toon G d,(∏i,arms d (v i) (a i)) * ∑ j:Toon G h,
        cutoff q t (Canon.Yield φ (Canon.FarCoefficients (Measure.outlook Z.scheme Z.criterion) (fun i=>flash (a i))) (flash j)) * μ j := by
  simp only [row,incoming,WilsonPositionScaleLawMeasuredOutput.identity,one_apply_eq_self,map_zero,
    outer_zero,WilsonMSDictionaryFarRead.converted_eq Z M ν matchSource]
end YM.Integration.WilsonPositionScaleLawMeasuredOPE
