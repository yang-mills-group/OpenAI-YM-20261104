import YM.Integration.WilsonThermometerUnitFilingJointTensor
import YM.Integration.WilsonThermometerUnitFilingCoverPieces
import YM.RegulatorIR.Profiles.Chance

/-! The actual cover opening is the offered symmetric Taylor table of its local script. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCoverBasis
open Function Finset Gauge Lattice RG RegulatorIR Budget Budget.Packet Budget.Layer Budget.Tuple
open Diagram Prim Binding Cluster Motion Halo Profiles Ledger Ledger.Sky Taping PowerSeries
open PertExtension PertExtension.Series Series.Radial Series.Tested
open scoped Classical BigOperators ContDiff PowerSeries Matrix.Norms.Frobenius
variable {G:Gauge} {h:ℕ} (B:Portrait G)

def germ:Micro (Foot G):=fun t x=>B t (win G x)

def material (w:Prim.Run (germ B))(h:ℕ):Orders (Foot G):=fun e r=>
  offer w.inc (WilsonThermometerUnitFilingJointTensor.card
    (WilsonThermometerUnitFilingJointTensor.entry w.script (e+h)) r)

theorem exact (resident:LocalStamp B h)(w:Prim.Run (germ B)):
    BasisT h h B (material B w h) ∧ Ranks h (material B w h):=by
  let Q (e:ℕ):Ranked w.J:=WilsonThermometerUnitFilingJointTensor.card
    (WilsonThermometerUnitFilingJointTensor.entry w.script (e+h))
  have good (e:ℕ):Satin (Q e) ∧ Within (e+h) (Q e) ∧ ∀ x,
      jet w.script (e+h) (1,x)=MvPolynomial.eval x (packed (Q e) (e+h)):=by
    have hp:=WilsonThermometerUnitFilingJointTensor.printed
      (WilsonThermometerUnitFilingJointTensor.entry w.script (e+h))
    exact ⟨hp.1,hp.2.1,fun x=>(WilsonThermometerUnitFilingJointTensor.applied _ _ x).symm.trans (hp.2.2 x).symm⟩
  refine ⟨⟨resident.people,fun _ _=>bound_offer ..,fun e r=>offer_symm w.inc _ ((good e).1 r),?_⟩,?_⟩
  · intro v;change tale (flank (germ B) v)= _;ext i;rw [coeff_X_pow_mul']
    split_ifs with hg
    · rw [shelter,coeff_mk,w.flank_v,inscription,coeff_mk,← Nat.sub_add_cancel hg]
      simp only [add_tsub_cancel_right];unfold material;rw [flute]
      exact (good (i-h)).2.2 _
    exact (Script.actual (w.smooth_v v)).vanish (resident.order v) (by omega)
  · intro e r paid
    apply (good e).2.1
    intro zero;apply paid
    change offer w.inc (Q e r)=0
    rw [zero];ext p;simp [offer,Stalk.collect]

theorem opening {W:Type} {M:W→ℕ} {n:Page M→Side} {S:Heir n G} (T:S.Accounts)
    (bank:W→Portrait G)(law:∀ v,LocalStamp (bank v) h)(v:W)
    (w:Prim.Run (germ (bank v))):
    (WilsonThermometerUnitFilingCoverStock.report T bank law).main (Page.opening M v)=
      material (bank v) w h:=by
  have prepared:=WilsonThermometerUnitFilingCoverStock.opening T bank law v
  obtain ⟨filed,shape⟩:=exact (bank v) (law v) w
  apply certifies prepared.1 filed _ shape
  rw [prepared.2]
  exact (stamp_symbol (law v)).choose_spec.2

end YM.Integration.WilsonThermometerUnitFilingCoverBasis
