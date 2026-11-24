import YM.Integration.WilsonSeparatedOriginalSlabReplicaLaw
import YM.Integration.WilsonSeparatedOriginalSlabReplicaShift
import YM.Integration.WilsonSeparatedOriginalSlabChildWords
import YM.Integration.WilsonSeparatedOriginalSlabCubicPosting

/-! The registered centered subcell and the complete, translated, independent
cutoff copies have identical readings under the genuine earlier Wilson law. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabReplicaSensor
open Function MeasureTheory Lattice Wilson RG Source Extraction Push.GridApprox
open OPE.Therm PhysicalNext.Repeat.Legato RG05Readout.Records
open RG05Readout Address Native Pulse WilsonSeparatedOriginalSlabChildSites
open WilsonSeparatedOriginalReplicaMeasure WilsonSeparatedOriginalReplicaScanner
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){b N per:ℕ}(top:b+1≤N)
local notation "C"=>R.family
local notation "A"=>R.family.S.oneStep b per
local notation "D"=>R.family.S.toDepth top per
local notation "μ"=>WilsonMacroscopicRichFlatPosteriorLaw.law R N per top (1:Config G ((C).side b per))

theorem original (s:Fin 3→ℕ)(v:(i:Fin 3)→Palette (C) (s i))(o:Fin 3→Site ((C).side (b+1) per))
    (c:Site ((C).side (b+1) per))(φ:Wave (Fin 3)):
    sample R s v (site A o c) top top 1 φ=read μ (fun W=>WilsonSeparatedOriginalReplicaWave.scalp s v o top φ
      (fun i=>pull 1 ((D).embed c) (W i))):=by
  let q:=-(A).parent (o 0+c)
  let w:=fun i=>o i+c
  let X:=WilsonSeparatedOriginalReplicaWave.scalp («C»:=R.family) s v w top φ
  have axis:=WilsonSeparatedOriginalSlabChildLaw.embedded (C).S (A) (D) ((C).S.toDepth (b.le_succ.trans top) per) q
  have level:(fun i=>w i+(A).embed q)=site A o c:=by rfl
  have transfer (W:Fin 3 → Config G ((C).side N per)):
      X (fun i=>pull 1 (((C).S.toDepth (b.le_succ.trans top) per).embed q) (W i))=
        WilsonSeparatedOriginalReplicaWave.scalp s v (site A o c) top φ W:=by
    rw [←axis];exact (WilsonSeparatedOriginalSlabChildWords.copies («C»:=R.family) top s v w ((A).embed q) φ W).trans (congrArg (fun y=>WilsonSeparatedOriginalReplicaWave.scalp s v y top φ W) level)
  rw [WilsonSeparatedOriginalReplicaScanner.measured]
  calc
    _=read μ (fun W=>X (fun i=>pull 1 (((C).S.toDepth (b.le_succ.trans top) per).embed q) (W i))):=congrArg (read μ) (funext (fun W=>(transfer W).symm))
    _=read μ X:=WilsonSeparatedOriginalSlabReplicaShift.original μ _ (WilsonSeparatedOriginalSlabReplicaLaw.law R top q) X
    _=_:=congrArg (read μ) (funext (fun W=>(WilsonSeparatedOriginalSlabChildWords.copies («C»:=R.family) top s v o c φ W).symm))

end YM.Integration.WilsonSeparatedOriginalSlabReplicaSensor
