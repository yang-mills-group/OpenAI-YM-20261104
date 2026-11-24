import YM.Integration.WilsonSeparatedOriginalSlabFolioAddress
import YM.Integration.WilsonSeparatedOriginalReplicaExperiments

/-! The one list chosen from the original separated profile represents every center Body and all three independent gauge fields, with its genuine stamped prices. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabFolioEnrollment
open Function Finset Set MeasureTheory Lattice Wilson RG Source Extraction RG05Readout RG05Readout.Address RG05Readout.Native
open RG05Readout.Nuclear RG05Readout.Pulse RG05Readout.Records RG05Readout.Flatten PhysicalNext.Repeat.Legato
open WilsonSeparatedOriginalPairedFolio WilsonSeparatedOriginalSlabFolioAddress WilsonSeparatedOriginalSlabDriven
open scoped BigOperators Classical Topology
variable {G:Gauge}{C:Family G}{n N per:ℕ}{s:Fin 3→ℕ}

def legal (allow:(Fin 3→Body)→Prop)(s:Fin 3→ℕ)(f:Fin 3→Body):Prop:=allow f ∧ ∀i,Tall (f i) (s i+2) 1 1

private theorem attained {allow:(Fin 3→Body)→Prop}{F:E4→Wave (Fin 3)}{D:ℝ}
    (h:Bouquet s Native.box allow F D):Bouquet s Native.box (legal allow s) F D:=by
  induction h with
  | empty=>exact .empty
  | bloom f a t ha hx ht hf hc=>exact .bloom f a t ha hx ht hf ⟨hc,hf⟩
  | add _ _ ia ib=>exact .add ia ib
  | permit _ x p ia=>exact .permit ia x p

variable {T:Type*}(book:(Fin 3→Body)→(T→ℂ)→Prop)

theorem original (o:Fin 3→Site (C.side n per))(top:n≤N){r η X:ℝ}(rp:0<r)(room:r≤C.S.a n)
    (ep:0<η)(small:η≤1)(Ψ:Wave (Fin 3))(rank:ℕ)(grade:(∑i:Fin 3,(s i+2))+4*Fintype.card (Fin 3)<rank+1)
    (scatter:Scattering Ψ η)(xp:0≤X)(sizeX:Tall Ψ (rank+1) 1 X)
    (bought:∀f,legal (Pulse.buy C n per o (r*η/2)) s f→∃a,book f a):
    ∃L:List (Entry s (legal (Pulse.buy C n per o (r*η/2)) s) book),
      (L.map price).sum≤tariff*(earn s C n rank η r*X) ∧
      (∀e∈L,∀H:ℕ,Priced H (stamp e) 1) ∧
      ∀(v:(i:Fin 3)→Palette C (s i))(g:Body)(U:Fin 3→ Config G (C.side N per)),
        WilsonSeparatedOriginalReplicaRegularity.meeting s v o top Ψ r g U=
          (L.map (fun e=>((price e:ℂ)*stamp e g)*∏i:Fin 3,
            Records.clinic C per N (s i) (v i) n (o i) (1,false) (e.test i) (U i))).sum:=by
  obtain ⟨F,source,jets⟩:=regent s (C:=C) (p:=per) top o r η Ψ rp room ep small grade scatter xp sizeX
  obtain ⟨L,rent,represented⟩:=WilsonSeparatedOriginalPairedFolio.issued (attained source) bought
  refine ⟨L,(ledger L).le.trans (mul_le_mul_of_nonneg_left rent WilsonSeparatedOriginalSlabDriven.positive.le),fun e _ H=>WilsonSeparatedOriginalSlabFolioAddress.issued e H,?_⟩
  intro v g U
  let K:Wave (Fin 3)→ₗ[ℂ]ℂ:=(LinearMap.proj U).comp (WilsonSeparatedOriginalReplicaWave.scalp (p:=per) s v o top)
  have eq (z:E4)(hz:z∈Native.box):K (submitted L z)=K (cropX Ψ o r z):=by
    rw [represented hz]
    exact congrFun (WilsonSeparatedOriginalReplicaWave.cuts s v o top _ _ (jets z)) U
  have one:WilsonSeparatedOriginalReplicaRegularity.meeting s v o top Ψ r g U=exposed g L K:=by
    rw [←WilsonSeparatedOriginalPairedFolio.measured]
    apply setIntegral_congr_fun Pert.Cellular.cells_compact.measurableSet;intro z hz
    exact congrArg (fun q:ℂ=>g.val z*q) (eq z hz).symm
  rw [one];unfold exposed;apply congrArg List.sum;apply List.map_congr_left;intro e _
  rw [restores];change ink g e*WilsonSeparatedOriginalReplicaWave.scalp (p:=per) s v o top (joint univ e.test) U=_
  rw [WilsonSeparatedOriginalReplicaWave.carving]

end YM.Integration.WilsonSeparatedOriginalSlabFolioEnrollment
