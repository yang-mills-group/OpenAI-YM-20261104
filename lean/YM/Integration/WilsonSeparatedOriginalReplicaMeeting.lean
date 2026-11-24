import YM.Integration.WilsonSeparatedOriginalProfilePortfolio
import YM.Integration.WilsonSeparatedOriginalReplicaRegularity

/-! The actual full center integral and the seven clamped physical experiments commute on a single jointly cropped source. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalReplicaMeeting
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Extra.Histories RG05Readout
open RG05Readout.Native RG05Readout.Pulse RG05Readout.Flatten RG05Readout.Nuclear RG05Readout.Address
open PhysicalNext.Repeat.Legato WilsonSeparatedOriginalPairedFolio
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n N per u:ℕ}
variable (s:Fin 3→ℕ)(v:(i:Fin 3)→Palette R.family (s i))(o:Fin 3→Site (R.family.side n per))(h:n≤N)
local notation "H"=>Fin 3 → Config G (R.family.side N per)
local notation "wave"=> WilsonSeparatedOriginalReplicaWave.scalp (C:=R.family) s v o h

private def observe (U:H):Wave (Fin 3)→ₗ[ℂ]ℂ:= (LinearMap.proj U).comp wave

private def mark (f:Fin 3→Body):C(H,ℂ):=
  ⟨wave (joint univ f),by
    rw [WilsonSeparatedOriginalReplicaWave.carving]
    exact continuous_finsetProd _ fun i _=>(Records.clinic_cut ..).comp (continuous_apply i)⟩

variable {B:Type*}{allow:(Fin 3→Body)→Prop}{book:(Fin 3→Body)→(B→ℂ)→Prop}
private def field (g:Body)(L:List (Entry s allow book)):C(H,ℂ):=
  (L.map (fun e=>ink g e • mark R s v o h e.test)).sum

private theorem point (g:Body)(L:List (Entry s allow book))(U:H):
    field R s v o h g L U=exposed g L (observe R s v o h U):=by
  induction L with
  | nil=>rfl
  | cons e L ih=>change ink g e*wave (joint univ e.test) U+field R s v o h g L U=_
                 rw [ih];rfl

private theorem carried (g:Body)(L:List (Entry s allow book))(op:u+1≤N)(V:Config G (R.family.side u per)):
    let μ:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per op V
    letI:=WilsonMacroscopicRichFlatPosteriorLaw.prob R op le_rfl V
    WilsonSeparatedOriginalReplicaFunctional.listener μ (field R s v o h g L)=
      exposed g L (WilsonSeparatedOriginalReplicaScanner.sample R s v o h op V):=by
  let μ:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per op V
  letI:=WilsonMacroscopicRichFlatPosteriorLaw.prob R op le_rfl V
  change WilsonSeparatedOriginalReplicaFunctional.listener μ _=_
  have receipt (f:Fin 3 → Body):WilsonSeparatedOriginalReplicaFunctional.listener μ (mark R s v o h f)=WilsonSeparatedOriginalReplicaScanner.sample R s v o h op V (joint univ f):=by
    rw [WilsonSeparatedOriginalReplicaFunctional.measured,WilsonSeparatedOriginalReplicaScanner.measured];rfl
  induction L with
  | nil=>exact map_zero _
  | cons e L ih=>
    change WilsonSeparatedOriginalReplicaFunctional.listener μ (ink g e • mark R s v o h e.test+field R s v o h g L)=_
    rw [map_add,map_smul,ih,receipt]
    rfl

private theorem signed (g:Body)(L:List (Entry s allow book))(Ψ:Wave (Fin 3))(r:ℝ)
    (jets:∀z∈Native.box,∀d≤∑i,s i,∀t:Fin 3→Site (R.family.S.toDepth h per).count,
      pie (submitted L z) (cropX Ψ o r z) d (placeR (R.family.S.toDepth h per) ∘ t)):
    field R s v o h g L=⟨WilsonSeparatedOriginalReplicaRegularity.meeting s v o h Ψ r g,
      WilsonSeparatedOriginalReplicaRegularity.regular s v o h Ψ r g⟩:=by
  ext U;rw [point,←WilsonSeparatedOriginalPairedFolio.measured]
  apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet;intro z hz
  exact congrArg (fun T:H → ℂ=>g.val z*T U) (WilsonSeparatedOriginalReplicaWave.cuts s v o h _ _ (jets z hz))

theorem original (op:u+1≤N)(V:Config G (R.family.side u per))(Ψ:Wave (Fin 3))(r:ℝ)(g:Body)
    (L:List (Entry s allow book))
    (jets:∀z∈Native.box,∀d≤∑i,s i,∀t:Fin 3→Site (R.family.S.toDepth h per).count,
      pie (submitted L z) (cropX Ψ o r z) d (placeR (R.family.S.toDepth h per) ∘ t)):
    WilsonSeparatedOriginalReplicaMeasure.read (WilsonMacroscopicRichFlatPosteriorLaw.law R N per op V)
      (WilsonSeparatedOriginalReplicaRegularity.meeting s v o h Ψ r g) =
    ∫z in Native.box,g.val z*WilsonSeparatedOriginalReplicaScanner.sample R s v o h op V (cropX Ψ o r z):=by
  letI:=WilsonMacroscopicRichFlatPosteriorLaw.prob R op le_rfl V
  let μ:=WilsonMacroscopicRichFlatPosteriorLaw.law R N per op V
  let Y:C(H,ℂ):=⟨_,WilsonSeparatedOriginalReplicaRegularity.regular s v o h Ψ r g⟩
  change WilsonSeparatedOriginalReplicaMeasure.read μ Y=_
  rw [←WilsonSeparatedOriginalReplicaFunctional.measured μ Y,show Y=field R s v o h g L from (signed R s v o h g L Ψ r jets).symm,carried R s v o h g L op V,←WilsonSeparatedOriginalPairedFolio.measured]
  apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet;intro z hz
  exact congrArg (fun a:ℂ=>g.val z*a) (WilsonSeparatedOriginalReplicaScanner.same R s v o h op V _ _ (jets z hz))

end YM.Integration.WilsonSeparatedOriginalReplicaMeeting
