import YM.Integration.WilsonIndependentNotebookReflectedTally
import YM.Integration.WilsonPositionProgramTrialStationHome

/-! The complete physical and survey sections on which the funded finite trial actually sits. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentNotebookReflectedFilm
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer WilsonCoeffUV.Wheel.Motion
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato XSpace
open WilsonIndependentMatchedFiledIncome (plate)
open WilsonIndependentMatchedNamedPair (sectionAt)
open WilsonIndependentNotebookReflectedSource (Paired)
open scoped BigOperators Classical
variable {G:Gauge}{h k e d D:ℕ}{F:Labels.Frame G h}

theorem pictured (X:Island F D)(priced:Shimmer X)(s:Signed)(v:Verse F):
    Paired s (Shrine X v) (Shrine X (Cosmos.paintC F s*ᵥv)):=by
  intro n
  let U:=imprint X (Cosmos.paintC F s)
  have hX i:shellK (valence F i) (X.1 n i):=(priced.scan.solo i).launch _
  have hU i:shellK (valence F i) (U.1 n i):=(Solo.affixing X.1 X.2 priced.scan.solo (paintCap F s) i).launch _
  have reflected i:Wreathe (affix (v i) (X.1 n i)) (affix (v i) (U.1 n i)) s:=
    incense _ _ _ _ (hX _) (hU _) (priced.scan.spirit s n i)
  rw [←Shrine_t]
  unfold Shrine
  simp only [Prod.fst_sum,Finset.sum_apply]
  exact pulseJ _ (fun i _=>reflected i) (fun i _=>shell_mon (affix_shell _ _ (hX i)) (valence_cap ..))
    (fun i _=>shell_mon (affix_shell _ _ (hU i)) (valence_cap ..))

theorem named (R:Run G)(W:Initialize G)(kind:Bool)(dim:d<D)(cap:d ≤ k)
    (s:Signed)(v:Verse (R.family.labels.level d))(a:ℝ):
    let P:=plate (sectionAt R W kind d) dim
    let f:=fun c=>a • Shrine P c
    On k (f v) ∧ On k (f (Cosmos.paintC (R.family.labels.level d) s*ᵥv)) ∧
      Paired s (f v) (f (Cosmos.paintC (R.family.labels.level d) s*ᵥv)):=by
  intro P f
  have film:Shimmer P:=by
    cases kind with
    | true=>
      have issue:=WilsonOriginalPivotWardSurvey.issued R W d
      exact freshly _ W.hol dim issue.1 issue.2.1
    | false=>exact freshly _ _ dim (R.makes.sections d) (FVAAlt2.Block.clothes R d)
  let S:=Cosmos.paintC (R.family.labels.level d) s
  have l:=Shrine_on P film v cap
  have r:=Shrine_on P film (S*ᵥv) cap
  exact ⟨l.μ a,r.μ a,fun n=>swellG (pictured P film s v n) (l.launch n) (r.launch n) a⟩

end YM.Integration.WilsonIndependentNotebookReflectedFilm
