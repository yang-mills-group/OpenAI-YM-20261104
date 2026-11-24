import YM.Integration.WilsonSeparatedOriginalReplicaWave
import YM.Integration.WilsonSeparatedOriginalReplicaMeasure
import YM.Integration.WilsonSeparatedOriginalPosteriorTransport
import YM.Integration.WilsonMacroscopicRichFlatPosteriorLaw

/-! Positive conditional copies of a common spatial test at a fixed old field. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedOriginalReplicaCubic
open RG05Readout RG05Readout.Address RG05Readout.Pulse RG05Readout.Native
open MeasureTheory Finset Set RG Lattice Wilson Source Extraction Push.GridApprox
open OPE.Therm PhysicalNext.Repeat.Legato RG05Readout.Records WilsonSeparatedOriginalMarkedCubic
open scoped BigOperators Classical Topology
open WilsonSeparatedOriginalReplicaMeasure
variable {G:Gauge} (R:Run G){N per u b:ℕ}

theorem physical (opened:u+1≤N)(V:Config G (R.family.side u per))(f:Fin 3 → Goods G (R.family.side N per))
    (regular:∀i,Continuous (f i)):
    read (WilsonMacroscopicRichFlatPosteriorLaw.law R N per opened V) (fun U=>∏i:Fin 3,f i (U i))=
      cubic (moment R.family id f (Nat.le_of_succ_le opened) V):=by
  rw [grouped]
  congr 1;funext a
  let F:=fun W=>∏i∈a,f i W
  have cont : Continuous F:=continuous_finsetProd _ fun i _=>regular i
  letI:IsProbabilityMeasure (scene R.family.path N per N):=OPE.Therm.probability R.makes.wilson le_rfl
  have paid:Integrable F (scene R.family.path N per N):=cont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have price:=WilsonMacroscopicRichFlatPosteriorLaw.reading R opened le_rfl V F paid
  have same:=congrFun (WilsonSeparatedOriginalPosteriorTransport.realized R.makes le_rfl (Nat.le_of_succ_le opened) F paid) V
  exact price.symm.trans same

theorem clinic (opened:u+1≤N)(h:b≤N)(V:Config G (R.family.side u per))(s:Fin 3→ℕ)
    (v:(i:Fin 3)→Palette R.family (s i))(o:Fin 3 → Site (R.family.side b per))(f:Fin 3→Body):
    read (WilsonMacroscopicRichFlatPosteriorLaw.law R N per opened V)
      (WilsonSeparatedOriginalReplicaWave.scalp (C:=R.family) s v o h (joint univ f))=
      cubic (moment R.family id (fun i=>Records.clinic R.family per N (s i) (v i) b (o i) (1,false) (f i))
        (Nat.le_of_succ_le opened) V):=by
  rw [WilsonSeparatedOriginalReplicaWave.carving (C:=R.family) s v o h f]
  apply physical
  exact fun _=>Records.clinic_cut ..

end YM.Integration.WilsonSeparatedOriginalReplicaCubic
