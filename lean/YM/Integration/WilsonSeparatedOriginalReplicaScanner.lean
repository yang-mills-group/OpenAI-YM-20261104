import YM.Integration.WilsonSeparatedOriginalReplicaCubic
import YM.Integration.WilsonSeparatedOriginalReplicaFunctional

/-! The complete common smooth wave enters one linear read of genuine conditional copies of the Wilson measure. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonSeparatedOriginalReplicaScanner
open MeasureTheory Lattice Wilson RG Source Extraction Push.GridApprox
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Pulse RG05Readout.Flatten
open RG05Readout.Records WilsonSeparatedOriginalMarkedCubic PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}{C:Family G}{N per b u:ℕ}(s:Fin 3→ℕ)(v:(i:Fin 3)→Palette C (s i))
variable (o:Fin 3 → Site (C.side b per))(h:b≤N)

private theorem currency {d:ℕ}(x:Palette C d)(a:Mark C d)(y:Site (C.side N per)):
    Continuous (Pulse.key C N per d x a y):=by
  unfold Pulse.key;apply Continuous.const_smul
  exact ((C.localSection _).continuous_places _ _).comp (continuous_pull ..)

private theorem regular (Ψ:Wave (Fin 3)):
    Continuous (WilsonSeparatedOriginalReplicaWave.scalp (C:=C) s v o h Ψ):=by
  change Continuous (fun U=>WilsonSeparatedOriginalReplicaWave.scalp (C:=C) s v o h Ψ U)
  simp only [WilsonSeparatedOriginalReplicaWave.scalp,LinearMap.sum_apply,LinearMap.smul_apply,
    Finset.sum_apply,Pi.smul_apply,LinearMap.comp_apply,smul_eq_mul]
  apply continuous_finsetSum;intro t _;apply continuous_const.mul
  change Continuous (fun U:Fin 3 → Config G (C.side N per)=>∑a:(i:Fin 3)→Mark C (s i),
    _ * ∏i,Pulse.key C N per (s i) (v i) (a i) _ (U i))
  exact continuous_finsetSum _ fun a _=>continuous_const.mul (continuous_finsetProd _ fun i _=>
    (currency (v i) (a i) _).comp (continuous_apply i))

private def filed : Wave (Fin 3) →ₗ[ℂ] C(Fin 3 → Config G (C.side N per),ℂ) where
  toFun Ψ:=⟨WilsonSeparatedOriginalReplicaWave.scalp (C:=C) s v o h Ψ,regular s v o h Ψ⟩
  map_add' F H:=by ext U;exact congrFun (map_add (WilsonSeparatedOriginalReplicaWave.scalp (C:=C) s v o h) F H) U
  map_smul' a F:=by ext U;exact congrFun (map_smul (WilsonSeparatedOriginalReplicaWave.scalp (C:=C) s v o h) a F) U

variable (R:Run G)

def sample (s:Fin 3→ℕ)(v:(i:Fin 3)→Palette R.family (s i))(o:Fin 3 → Site (R.family.side b per))
    (h:b≤N)(op:u+1≤N)(V:Config G (R.family.side u per)):Wave (Fin 3) →ₗ[ℂ] ℂ:=by
  letI:=WilsonMacroscopicRichFlatPosteriorLaw.prob R op le_rfl V
  exact (WilsonSeparatedOriginalReplicaFunctional.listener (WilsonMacroscopicRichFlatPosteriorLaw.law R N per op V)).comp
    (filed s v o h)

theorem measured (s:Fin 3→ℕ)(v:(i:Fin 3)→Palette R.family (s i))(o:Fin 3 → Site (R.family.side b per))
    (h:b≤N)(op:u+1≤N)(V:Config G (R.family.side u per))(Ψ:Wave (Fin 3)):
    sample R s v o h op V Ψ=WilsonSeparatedOriginalReplicaMeasure.read
      (WilsonMacroscopicRichFlatPosteriorLaw.law R N per op V) (WilsonSeparatedOriginalReplicaWave.scalp (C:=R.family) s v o h Ψ):=by
  letI:=WilsonMacroscopicRichFlatPosteriorLaw.prob R op le_rfl V
  exact WilsonSeparatedOriginalReplicaFunctional.measured _ (filed s v o h Ψ)

theorem same (s:Fin 3→ℕ)(v:(i:Fin 3)→Palette R.family (s i))(o:Fin 3 → Site (R.family.side b per))
    (h:b≤N)(op:u+1≤N)(V:Config G (R.family.side u per))(f g:Wave (Fin 3))
    (matchData:∀i≤∑j,s j,∀ t:Fin 3 → Site (R.family.S.toDepth h per).count,
      pie f g i (fun j=>placeR (R.family.S.toDepth h per) (t j))):
    sample R s v o h op V f=sample R s v o h op V g:=by
  rw [measured,measured,WilsonSeparatedOriginalReplicaWave.cuts s v o h f g matchData]

theorem clinic (s:Fin 3→ℕ)(v:(i:Fin 3)→Palette R.family (s i))(o:Fin 3 → Site (R.family.side b per))
    (h:b≤N)(op:u+1≤N)(V:Config G (R.family.side u per))(f:Fin 3→Body):
    sample R s v o h op V (joint Finset.univ f)=
      cubic (moment R.family id (fun i=>Records.clinic R.family per N (s i) (v i) b (o i) (1,false) (f i))
        (Nat.le_of_succ_le op) V):=(measured ..).trans (WilsonSeparatedOriginalReplicaCubic.clinic ..)

end YM.Integration.WilsonSeparatedOriginalReplicaScanner
