import YM.Integration.WilsonOriginalAlternativeExchange
import YM.Integration.ActualTrajectoryTransport
import YM.QuadraticLocal.Tariff.Measure

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalAlternativeHearing
open Function Finset MeasureTheory Lattice Wilson RG Marker QuadraticLocal MergeProof.Accent
open WilsonOriginalAlternativeNames WilsonOriginalAlternativeExtraction
open scoped Classical BigOperators
variable {G:Gauge} (C:Family G) (N per:ℕ) {k f:ℕ}

/-- The complete numerator through the original earlier Wilson kernels and their
positive lower vacuum. The upper object is a density, so it is used exactly once. -/
def held (g:Config G (C.side k per)→ℂ) (lower:f ≤ k) (W:Config G (C.side f per)) :=
  ((C.path.rep N per f).eval W)⁻¹ • gust C.path N per k g f lower W

theorem normalized (authentic:C.Makes) (upper:k ≤ N) (g:Config G (C.side k per)→ℂ)
    (lower:f ≤ k) : held C N per g lower=actualTransport C (N:=N)
      (fun U=>((C.path.rep N per k).eval U)⁻¹ • g U) lower := by
  have undo:(fun U=>(C.path.rep N per k).eval U • (((C.path.rep N per k).eval U)⁻¹ • g U))=g:=by
    funext U
    rw [smul_smul,mul_inv_cancel₀ (Multi.AxisShift.chosen_positive authentic.wilson upper U).ne',one_smul]
  funext W
  simp only [held,actualTransport,undo]

private theorem linear (date:f≤k) (F H:Config G (C.side k per)→ℂ)
    (first:Integrable F (prior G _)) (second:Integrable H (prior G _)) :
    gust C.path N per k (F-H) f date=gust C.path N per k F f date-gust C.path N per k H f date := by
  induction date using Nat.decreasingInduction with
  | self => rw [gust_base,gust_base,gust_base]
  | of_succ i hi ih =>
    rw [gust_step _ _ _ _ _ hi,gust_step _ _ _ _ F hi,gust_step _ _ _ _ H hi,ih]
    funext U
    simp only [StepData.push,Pi.sub_apply,smul_sub]
    exact integral_sub (StepData.push_slice (C.path.levels.transition_mass ..) _ _ (gust_live _ _ _ _ _ first hi))
      (StepData.push_slice (C.path.levels.transition_mass ..) _ _ (gust_live _ _ _ _ _ second hi))

variable {V T μ:Type} [Fintype V] [DecidableEq V] (J:Census V)
    {W:Rep G (C.side k per)} {o:V→Site (C.side k per)}
    (A:Gallery T μ (o∘Prod.fst) W (board J)) (x:T)

def source (c:V→Port) (s:J.Mode) (U:Config G (C.side k per)) :=
  (read J c (A.density x U)).part s

/-- All remaining ports are fixed on the same physical numerator. No re-election
of hard gas, companion sites, or the normalization is needed at the earlier field. -/
theorem exchange [Countable μ] {w:V×Port→ℝ} (positive:∀z,0<w z)
    {b e κ σ c v t h:ℝ} (income:A.Pays w b e κ) (width:0≤b) (law:W.Lawful σ c v t h)
    (F:Config G (C.side k per)→Poly J) (P:Config G (C.side k per)→V→ℂ)
    (same:∀U,A.density x U=stamped J (F U) (P U)) (c₀:V→Port) (j:V) (s:J.Mode) (active:j∈s.val)
    (lower:f ≤ k) (V₀:Config G (C.side f per)) :
    let atPort (t':Port):=source C per J A x (Function.update c₀ j t') s
    held C N per (atPort 2) lower V₀ = held C N per (atPort 0) lower V₀ -
      held C N per (atPort 1) lower V₀ := by
  intro atPort
  have input:atPort 2=atPort 0-atPort 1:=by
    funext U
    simp only [atPort,source,Pi.sub_apply,same]
    exact WilsonOriginalAlternativeExchange.original J (F U) (P U) c₀ j s active
  have raw:=QuadraticLocal.Tariff.integrable (board J) (o∘Prod.fst) w positive A x income width law
  have truth (tag:Port):Integrable (atPort tag) (prior G _):=
    (Poly.get ((names J (Function.update c₀ j tag)).share s)).integrable_comp raw
  rw [input]
  unfold held
  rw [linear C N per lower _ _ (truth 0) (truth 1),Pi.sub_apply,smul_sub]

theorem entries (F:Config G (C.side k per)→Poly J) (P:Config G (C.side k per)→V→ℂ)
    (same:∀U,A.density x U=stamped J (F U) (P U))
    (quiet:∀U,(F U).part J.quiet=(W.eval U:ℂ)) (s:J.Mode) (lower:f ≤ k) :
    held C N per (source C per J A x (fun _=>0) s) lower = held C N per (fun U=>(F U).part s) lower ∧
    held C N per (source C per J A x (fun _=>1) s) lower =
      held C N per (fun U=>(W.eval U:ℂ)*∏i∈s.val,P U i) lower ∧
    held C N per (source C per J A x (fun _=>2) s) lower =
      held C N per (fun U=>∑a:J.Mode,∑b:J.Mode,if Poly.merges a b s then
        (F U).part a*(∏i∈b.val,-P U i) else 0) lower := by
  constructor
  · exact congrArg (fun g=>held C N per g lower) (funext (fun U=>by
      simp only [source,same,WilsonOriginalAlternativeExtraction.original]))
  constructor
  · exact congrArg (fun g=>held C N per g lower) (funext (fun U=>by
      simp only [source,same,WilsonOriginalAlternativeExtraction.trial,quiet]))
  · exact congrArg (fun g=>held C N per g lower) (funext (fun U=>by
      simp only [source,same,WilsonOriginalAlternativeExtraction.mixed]))

end YM.Integration.WilsonOriginalAlternativeHearing
