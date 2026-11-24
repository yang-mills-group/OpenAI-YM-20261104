import YM.Integration.WilsonOriginalPublicTrialPhaseRate
import YM.Integration.WilsonOriginalPublicTrialPhaseCoFiled
import YM.Integration.WilsonOriginalPublicTrialPhaseWhole
import YM.RG05Readout.Many.Stage

/-! An original many-name input board at the actual interior birth date. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonOriginalPublicTrialPhasePaidBoard
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Cells Extra.Histories
open MergeProof MergeProof.Accent MergeProof.Ribbons MergeProof.Ribbons.ManyCopies MergeProof.Ribbon MergeProof.Float
open Push Local Marker Motion PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign Extra.Multi OPE.Therm
open RG05Readout RG05Readout.Address RG05Readout.Many
open WilsonOriginalPublicTrialPhaseFiling WilsonOriginalPublicTrialPhaseTiles WilsonOriginalPublicTrialPhaseRate
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){K N per:ℕ}{I:Type}[Fintype I][DecidableEq I]
local notation "C" => R.family
local notation "H" => (C).path
local notation "P" => (H).rep N per K

open Extra.Histories RG05Readout.Address

/-- All slots of the original marked K bank are the actual prefiled invoices or their true rotated copies. -/
theorem original (live:K≤N)(tiles:Tiling ((C).side K per))
    (d:I→ℕ)(z:I→Site ((C).side K per))(v:∀i,(C).label (d i))
    (q:∀j,Coefficient ((C).labels.level (d j)) ((C).side K per))
    (writes:∀j U,(q j).density (z j) ((C).localSection (d j)) (P) U=
      ((P).eval U:ℂ)*WilsonPositionProgramBlockedTrialAddBack.uncut R (d j) N per K (z j) (v j) U)
    (dom₀:∀j,Dominated (q j).forced)(ψ:I→MergeProof.Response G ((C).side K per))
    (won:∀j,Attainment (P).p (z j) (ψ j) (reserve R (N:=N) (d j) (z j) (v j)))
    (hook:∀j,profile (P).activities (q j).forced=MergeProof.hook (P).activities (P).p.threshold (ψ j))
    (moves:∀i,(P).activities.Moves (motion tiles i).1 (tiles.translateBy i))
    (opening:WilsonOriginalPublicTrialPhaseRate.volume (P).p.B*(H).levels.clock.forcedAllowance K≤Real.log 2/2)
    (ex:0≤(P).p.supportExponent-3):
    let F:=fun i:tiles.Cell×I=>tiles.copy i.1 (WilsonPositionProgramBlockedTrialAddBack.uncut R
      (d i.2) N per K (z i.2) (v i.2))
    let o:=fun i:tiles.Cell×I=>tiles.copyMap i.1 (z i.2)
    let w:=fun i=>wage (P).p.B (Fintype.card I*Fintype.card Signed) (reserve R (N:=N) (d i) (z i) (v i))
    let Z:=fun i=>RG05Readout.Address.invoice (q i) (z i) ((C).localSection (d i)) (P)
    let Q:=WilsonOriginalPublicTrialPhaseCoFiled.copies (P) 0 (motion tiles) tiles.translateBy moves Z
    (∀i U,(Q i).1 U=((P).eval U:ℂ)*F i U) ∧ (∀i,0<w i) ∧
      MenuBoard (P) Q (birth (Names tiles.Cell I) (P) F) o (fun i=>w i.2) ((P).p.supportExponent-3) 1:=by
  intro F o w Z Q
  let load:=Fintype.card I*Fintype.card Signed
  obtain ⟨t,radius,bound,cap⟩:=rents (P).p.B load _ opening
  have occ:Occupancy (whereAt 0 (motion tiles) tiles.translateBy z) load:=by
    rw [funext (pin tiles z)]
    exact seats tiles z
  have wpos i:0<w i:=(radius _).1
  obtain ⟨head,dom,reading,born⟩:=WilsonOriginalPublicTrialPhaseCoFiled.original R live d z v q writes dom₀ ψ won hook
    0 (motion tiles) tiles.translateBy moves occ w wpos (fun i=>(radius _).2) t.le ex bound cap
  have eq (i:tiles.Cell×I)(U):(Q i).1 U=((P).eval U:ℂ)*F i U:=by
    simpa only [picture tiles _ i] using head i U
  have cov (i:tiles.Cell×I):Continuous (F i):=by
    have h:Continuous (WilsonPositionProgramBlockedTrialAddBack.uncut R (d i.2) N per K (z i.2) (v i.2)):=
      continuous_const.add (((C).localSection _).continuous_places _ _)
    have h':=h.comp (continuous_pull (G:=G) (tiles.omega i.1) (tiles.translateBy i.1))
    unfold F Tiling.copy
    by_cases sign:tiles.hand i.1
    · simpa only [if_pos sign,Function.comp_def,Pi.star_apply] using h'.star
    · simpa only [if_neg sign,Function.comp_def] using h'
  have quiet:=RG02.Actual.eval_cont R.makes.wilson live (p:=per)
  have hip:Integrable (birth (Names tiles.Cell I) (P) F) (prior G ((C).side K per)):=
    (hatCont (C) K per F cov quiet (Names tiles.Cell I)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨eq,wpos,hip,?_,?_⟩
  · intro i
    refine ⟨dom i,funext (fun U=>(reading i U).symm),?_⟩
    have measured:=((Poly.get ((Names tiles.Cell I).fire i)).restrictScalars ℝ).integrable_comp hip
    change Integrable (fun U=>((birth (Names tiles.Cell I) (P) F U).part ((Names tiles.Cell I).fire i))) _ at measured
    rw [funext (eq i)]
    simpa only [Accent.boot] using measured
  · simpa only [funext (picture tiles _),funext (pin tiles z)] using ManyCopies.Serves.sold born

end YM.Integration.WilsonOriginalPublicTrialPhasePaidBoard
end
