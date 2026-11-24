import YM.Integration.WilsonMSDictionaryVector

/-! At any fixed perturbative order the actual finite independent output
has a bounded total coefficient price throughout a compact coupling interval. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkIndependentFee
open Filter Function Finset Lattice Maxwell XSpace XSpace.Normalize XSpace.Structure1
open FVA2 FVA2.Register FVA2.Scale FVA2.O FVA2.O.Score FVA2.O.Project
open MS MS.Land MS.Fleet MS.Theater PowerSeries RG17 WilsonMSDictionaryFarRead WilsonMSDictionaryVector
open scoped Classical BigOperators Topology
variable {G:Gauge}

def dose (C:Family G)(h:ℕ)(y:Free C h):ℝ:=∑k,‖(WilsonMSDictionaryVector.basis C h).repr y k‖
theorem continuous_dose (C:Family G)(h:ℕ):Continuous (dose C h):=by
  unfold dose
  apply continuous_finsetSum
  intro k _
  exact (WilsonMSDictionaryVector.basis C h).coord k |>.toContinuousLinearMap.continuous.norm

theorem prediction_continuous (C:Family G){n:ℕ}(d:Fin n→ℕ)(h:ℕ)
    (Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)
    (v:∀i,Free C (d i))(ψ:Test n)(q:ℕ):Continuous (prediction C d h Z M ν v ψ q):=by
  have cut (row:PowerSeries ℂ):Continuous (fun t:ℝ=>cutoff q t row):=by
    unfold cutoff;exact continuous_finsetSum _ fun k _=>(Complex.continuous_ofReal.pow k).mul continuous_const
  let b:=WilsonMSDictionaryVector.basis C h
  let u:=fun (j:∀i,Dframe.Toon G (d i)) (k:Dframe.Toon G h)=>converted Z M ν (fun i=>Dframe.flash (j i)) ψ (Dframe.flash k)
  have piece(j:∀i,Dframe.Toon G (d i))(k:Dframe.Toon G h):
      Continuous (fun t:ℝ=>cutoff q t (u j k) • b k):=(cut (u j k)).smul continuous_const
  have row(j:∀i,Dframe.Toon G (d i)):Continuous (fun t:ℝ=>∑k,cutoff q t (u j k) • b k):=
    continuous_finsetSum _ fun k _=>piece j k
  exact continuous_finsetSum _ fun j _=>(row j).const_smul (∏i,(WilsonMSDictionaryVector.basis C (d i)).repr (v i) (j i))

theorem original (C:Family G){n:ℕ}(d:Fin n→ℕ)(h:ℕ)(Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)(v:∀i,Free C (d i))(ψ:Test n)
    {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)(q:ℕ):
    let P:=((ms.separatedOPE ν).wilson.light h).choose
    ∃K:ℝ,0≤K ∧ ∀t∈Set.Icc (-1:ℝ) 1,∀ᶠs:ℝ in atTop,dose C h (experiment C d h Z M ν v ψ P q t s)≤K:=by
  dsimp only
  let P:=((ms.separatedOPE ν).wilson.light h).choose
  have live:Read.Detected (Measure.outlook Z.scheme Z.criterion) P:=((ms.separatedOPE ν).wilson.light h).choose_spec.2
  have cont:Continuous (fun t=>dose C h (prediction C d h Z M ν v ψ q t)):=
    (continuous_dose C h).comp (prediction_continuous C d h Z M ν v ψ q)
  obtain ⟨a,cap⟩:BddAbove ((fun t=>dose C h (prediction C d h Z M ν v ψ q t)) '' Set.Icc (-1:ℝ) 1):=
    (isCompact_Icc.image cont).bddAbove
  refine ⟨max 0 a+1,by have:=le_max_left 0 a;linarith,?_⟩
  intro t ht
  have bound:=cap (Set.mem_image_of_mem (fun t=>dose C h (prediction C d h Z M ν v ψ q t)) ht)
  have top:dose C h (prediction C d h Z M ν v ψ q t)< max 0 a+1:=
    lt_of_le_of_lt (bound.trans (le_max_right _ _)) (lt_add_one _)
  exact ((continuous_dose C h).continuousAt.tendsto.comp
    (experiment_limit C d h Z M ν v ψ ms P live q t)).eventually (ge_mem_nhds top)

variable (C:Family G){n:ℕ}(d:Fin n→ℕ)(h:ℕ)(Z:WilsonPrescription G)
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))(ν:ℝ)(v:∀i,Free C (d i))(ψ:Test n)
    {simple:G.Simple}{σ:Prescription (Press.portDeck G)}{branch:Bool}(ms:Main.Match Z simple M σ branch)

/-- One price for this finite normalized independent input and smooth profile, before
the running physical scale or either of its regulators are specified. -/
def allowance (q:ℕ):ℝ:=(original C d h Z M ν v ψ ms q).choose

theorem pays (q:ℕ):
    0≤allowance C d h Z M ν v ψ ms q ∧ ∀t∈Set.Icc (-1:ℝ) 1,∀ᶠ s:ℝ in atTop,
    dose C h (experiment C d h Z M ν v ψ ((ms.separatedOPE ν).wilson.light h).choose q t s)≤allowance C d h Z M ν v ψ ms q:=
  (original C d h Z M ν v ψ ms q).choose_spec

end YM.Integration.WilsonPublicForkIndependentFee
