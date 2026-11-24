import YM.Integration.WilsonSeparatedOriginalReplicaSupport
import YM.Integration.WilsonSeparatedOriginalReplicaRegularity
import YM.Integration.WilsonSeparatedOriginalResidentExpectation

/-! The uncentered, joint Wilson reading of a single three-position wave at an earlier held field. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabWave
open PhysicalNext.Repeat.Legato
open Function Set MeasureTheory Lattice Wilson RG Source Extraction Push.GridApprox
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Pulse RG05Readout.Flatten RG05Readout.Records
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){N per n u:ℕ}(s:Fin 3→ℕ)(v:(i:Fin 3)→Palette R.family (s i))
variable (o:Fin 3→Site (R.family.side n per))(nN:n ≤ N)
local notation "C"=>R.family

private theorem chart (Ψ:Wave (Fin 3)):Continuous (Pulse.scalp (p:=per) s v o nN Ψ):=by
  change Continuous (fun U=>Pulse.scalp (p:=per) s v o nN Ψ U)
  simp only [Pulse.scalp,LinearMap.sum_apply,LinearMap.smul_apply,Finset.sum_apply,Pi.smul_apply,
    LinearMap.comp_apply,smul_eq_mul]
  apply continuous_finsetSum;intro t _;apply continuous_const.mul
  change Continuous (fun U=>∑a:(i:Fin 3)→Mark C (s i),
    _ * ∏i,Pulse.key C N per (s i) (v i) (a i) _ U)
  apply continuous_finsetSum;intro a _;apply continuous_const.mul
  apply continuous_finsetProd;intro i _;unfold Pulse.key
  apply Continuous.const_smul;exact (((C).localSection _).continuous_places _ _).comp (continuous_pull ..)

private def deposited:Wave (Fin 3)→ₗ[ℂ]C(Config G (R.family.side N per),ℂ) where
  toFun Ψ:=⟨Pulse.scalp (p:=per) s v o nN Ψ,chart R s v o nN Ψ⟩
  map_add' f g:=by ext U;exact congrFun (map_add (Pulse.scalp (p:=per) s v o nN) f g) U
  map_smul' c f:=by ext U;exact congrFun (map_smul (Pulse.scalp (p:=per) s v o nN) c f) U

def scan (uN:u+1 ≤ N)(U:Config G (R.family.side u per)):Wave (Fin 3)→ₗ[ℂ]ℂ:=
  (WilsonSeparatedOriginalResidentExpectation.mean R uN U).comp (deposited R s v o nN)

theorem measured (uN:u+1 ≤ N)(U:Config G (R.family.side u per))(Ψ:Wave (Fin 3)):
    scan R s v o nN uN U Ψ=∫W,Pulse.scalp (p:=per) s v o nN Ψ W ∂WilsonMacroscopicRichFlatPosteriorLaw.law R N per uN U:=rfl

theorem same (uN:u+1 ≤ N)(U:Config G (R.family.side u per))(f g:Wave (Fin 3))
    (jets:∀d≤∑i,s i,∀t:Fin 3→Site ((C).S.toDepth nN per).count,pie f g d (placeR ((C).S.toDepth nN per) ∘ t)):
    scan R s v o nN uN U f=scan R s v o nN uN U g:=by
  rw [measured,measured]
  apply integral_congr_ae
  filter_upwards with W
  rw [←WilsonSeparatedOriginalReplicaRegularity.diagonal s v o nN f W,←WilsonSeparatedOriginalReplicaRegularity.diagonal s v o nN g W,
    WilsonSeparatedOriginalReplicaWave.cuts s v o nN f g jets]

theorem clinics (uN:u+1 ≤ N)(U:Config G (R.family.side u per))(f:Fin 3→Body):
    scan R s v o nN uN U (joint Finset.univ f)=actualTransport C (N:=N)
      (fun W=>∏i:Fin 3,Records.clinic C per N (s i) (v i) n (o i) (1,false) (f i) W) (Nat.le_of_succ_le uN) U:=by
  change WilsonSeparatedOriginalResidentExpectation.mean R uN U (deposited R s v o nN (joint Finset.univ f))=_
  rw [WilsonSeparatedOriginalResidentExpectation.value]
  exact congrArg (fun F:Config G ((C).side N per)→ℂ=>actualTransport C (N:=N) F (Nat.le_of_succ_le uN) U)
    (Pulse.carving s v o nN f)

theorem absent (uN:u+1 ≤ N)(U:Config G (R.family.side u per)){r cap:ℝ}(rp:0<r)(Ψ:Wave (Fin 3))
    (shape:∀x∈tsupport Ψ.val,∀i:Fin 3,‖x i‖≤cap)(J:ℕ)(outside:o∉Pulse.area («C»:=R.family) (p:=per) (b:=n) J)
    (reach:r*cap+2*(C).S.a n≤(C).S.a n*(J:ℝ))(z:E4)(hz:z∈Native.box):
    scan R s v o nN uN U (cropX Ψ o r z)=0:=by
  rw [measured]
  have gone:=WilsonSeparatedOriginalReplicaSupport.absent s v nN rp Ψ shape J o outside reach z hz
  have eq:(fun W:Config G ((C).side N per)=>Pulse.scalp (p:=per) s v o nN (cropX Ψ o r z) W)=0:=by
    funext W;rw [←WilsonSeparatedOriginalReplicaRegularity.diagonal s v o nN _ W,gone];rfl
  rw [eq];exact integral_zero ..

end YM.Integration.WilsonSeparatedOriginalSlabWave
