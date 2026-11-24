import YM.Integration.WilsonSeparatedOriginalSlabReplicaSurface
import YM.Integration.WilsonSeparatedOriginalSlabReplicaSensor
import YM.Integration.WilsonSeparatedOriginalSlabChildAverage

/-! The genuine clamped conditional third cumulant of the complete original
signed profile, with one shared translated coordinate. Averages are over the
real affine subcells. The funded older projection may be substituted at each
after that same profile has been tested. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabReplicaFiscal
open Function MeasureTheory Set Finset Lattice Wilson RG Source
open OPE.Therm PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Records
open RG05Readout.Address RG05Readout.Native RG05Readout.Pulse RG05Readout.Flatten
open WilsonSeparatedOriginalSlabReplicaReading WilsonSeparatedOriginalSlabReplicaFilm
open WilsonSeparatedOriginalSlabChildSites WilsonSeparatedOriginalSlabChildAverage
open WilsonPositionSeparatedProfileCenteredCells 
open private filed from YM.Integration.WilsonSeparatedOriginalReplicaScanner
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){b N per:ℕ}(top:b+1≤N)
local notation "C"=>R.family
local notation "I"=>Fin 3
local notation "Sites"=>Site ((C).side (b+1) per)
local notation "μ"=>WilsonMacroscopicRichFlatPosteriorLaw.law R N per top (1:Config G ((C).side b per))
local instance probability:IsProbabilityMeasure μ:=WilsonMacroscopicRichFlatPosteriorLaw.prob R top le_rfl 1

def registered (s:I→ℕ)(v:(i:I)→Palette (C) (s i))(o:I→Sites)(c:Sites):Wave I→ₗ[ℂ]ℂ:=
  WilsonSeparatedOriginalReplicaScanner.sample R s v (site ((C).S.oneStep b per) o c) top top 1

theorem charged (s:I→ℕ)(v:(i:I)→Palette (C) (s i))(r:ℝ)(Ψ:Wave I)(m:ℕ)(g:Body)(c:Sites):
    WilsonSeparatedOriginalReplicaFunctional.listener μ
      (turn («C»:=R.family) (((C).S.toDepth top per).embed c) (paper s v r Ψ top m g))=
      WilsonSeparatedOriginalSlabWholeProfile.whole R s (registered R top s v) r Ψ m g c:=by
  rw [WilsonSeparatedOriginalSlabReplicaSurface.register]
  simp only [map_smul,map_sum,smul_eq_mul]
  unfold WilsonSeparatedOriginalSlabWholeProfile.whole
  apply congrArg (fun z:ℂ=>premiums (C) s m (b+1) r*z)
  apply Finset.sum_congr rfl;intro o _
  let meter: ContinuousMap (I → Config G ((C).side N per)) ℂ→ₗ[ℂ]ℂ:=(WilsonSeparatedOriginalReplicaFunctional.listener μ).comp
    (turn («C»:=R.family) (((C).S.toDepth top per).embed c))
  change meter (film s v o top Ψ r g)=∫z in Native.box,g.val z*registered R top s v o c (cropX («C»:=R.family) Ψ o r z)
  rw [WilsonSeparatedOriginalSlabReplicaFilm.original]
  apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet;intro z _
  apply congrArg (fun x:ℂ=>g.val z*x)
  exact (WilsonSeparatedOriginalSlabReplicaReading.moved μ _ (filed s v o top (cropX («C»:=R.family) Ψ o r z))).trans
    (WilsonSeparatedOriginalSlabReplicaSensor.original R top s v o c _).symm

def observable (s:I→ℕ)(v:(i:I)→Palette (C) (s i))(r:ℝ)(Ψ:Wave I)(m:ℕ)(g:Body):ℂ:=
  WilsonSeparatedOriginalReplicaFunctional.listener μ (paper s v r Ψ (b.le_succ.trans top) m g)

theorem original (s:I→ℕ)(v:(i:I)→Palette (C) (s i))(r:ℝ)(Ψ:Wave I){cap:ℝ}
    (rp:0<r)(enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap)(room:r*cap+2*(C).S.a b<(C).S.radius per)(m:ℕ)(g:Body):
    observable R (per:=per) top s v r Ψ m g=WilsonSeparatedOriginalSlabChildAverage.average (fun a:Bud (C) per b=>
      WilsonSeparatedOriginalSlabWholeProfile.whole R s (registered R top s v) r Ψ m (Many.headFee (C) per b a g) (child (C) per b a)):=by
  unfold observable
  rw [WilsonSeparatedOriginalSlabReplicaSurface.cut s v r Ψ top rp enclosed room]
  unfold WilsonSeparatedOriginalSlabChildAverage.average;apply congrArg (fun z:ℂ=>(Fintype.card (Bud (C) per b):ℂ)⁻¹*z)
  apply Finset.sum_congr rfl;intro a _
  exact charged R top s v r Ψ m _ _

end YM.Integration.WilsonSeparatedOriginalSlabReplicaFiscal
