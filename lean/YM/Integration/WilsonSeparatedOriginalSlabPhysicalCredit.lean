import YM.Integration.WilsonReportHarvestSlabCenteredPhysical
import YM.Integration.WilsonSeparatedOriginalSlabPhysicalBlade
import YM.RG16.Unmasked.Report

/-! Every resident mode reads its true fine product with the full original Wilson density at the capture cell. -/
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalSlabPhysicalCredit
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi Push.GridApprox
open PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station Ribbons
open WilsonReportHarvestSlabLabels WilsonAllDateHarvestPropagation WilsonReportHarvestSlabCenteredPush
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
open private pushed from YM.Integration.WilsonReportHarvestSlabCenteredPhysical
local notation "S₀"=>Stock.census (Fin 3)

variable {G:Gauge} (C:Family G){u n m N per:ℕ}
    (o:Fin 3→Site (C.side n per))(E:Fin 3→Motion)(s:Fin 3→ℕ)(q:ManyStem C o n→Body)
    (S:(i:Fin 3)→Emblems C (s i))(x:(i:Fin 3)→Palette C (s i))
local notation "J"=>Mine.ward o E (Stock.census (Fin 3))
local notation "Y"=>C.path.rep N per
local notation "F"=>WilsonAllDateHarvestPhysical.columns o E s q S x m N n
local notation "Cₙ"=>WilsonSeparatedOriginalCaptureAtOrigin.clinics o E s q S x m N

theorem original (h:C.Makes)(nN:n≤N)(mask:(S₀).Mode)(V:Config G (C.side n per)):
    (baseFold o E S₀ (gust C.path N per N (birth (J n) (Y N) F) n nN V)).part mask=
      RG16.Literal.credit C N per 0 (fun U=>∏i∈mask.val,Cₙ i U) n nN V:=by
  let a:=Mine.remap o E
  let A:=Mine.tree o E
  have upper:Integrable (birth (J n) (Y N) F) (prior G (C.side N per)):=
    (hatCont C N per F (fun _=>Records.clinic_cut ..) (show Continuous ((Y N).eval) by
      rw [(h.wilson.starts ..).2];exact bare_cont _) (J n)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have equal:Many.combine (A.labelY n) (fun _=>1) F=Cₙ:=by
    funext i;unfold Many.combine
    rw [Finset.sum_eq_single (a.symm i)]
    · rw [if_pos (show A.labelY n (a.symm i)=i from rfl),one_smul]
      exact WilsonSeparatedOriginalCaptureAtOrigin.registered o E s q S x m N i
    · intro z _ nz
      rw [if_neg (show A.labelY n z≠i from fun k=>nz (a.injective (k.trans (a.apply_symm_apply i).symm))),zero_smul]
    · simp
  obtain ⟨fin,branch⟩:=blended F (fun _=>1) (chamber S₀ (A.labelY n)) nN upper
  rw [equal] at fin branch
  have back:(fun W=>baseFold o E S₀ (gust C.path N per N (birth (J n) (Y N) F) n nN W))=
      gust C.path N per N (birth S₀ (Y N) Cₙ) n nN:=branch.symm
  have here:=congrArg (fun Z=>(Z V).part mask) back
  refine here.trans ?_
  have point:=congr_fun (pushpart nN (birth S₀ (Y N) Cₙ) mask fin) V
  rw [point,RG16.Literal.credit,pow_zero,one_smul]
  rw [pushed C.path N per N _ nN]
  congr 2;funext W
  rw [birth,Poly.part_smul,Mach,pass_fire,(h.wilson.starts N per).2]

end YM.Integration.WilsonSeparatedOriginalSlabPhysicalCredit
