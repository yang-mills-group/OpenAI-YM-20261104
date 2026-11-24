import YangMills.WilsonProof.NativeSupport.OPEMatching.Statement
import YangMills.WilsonProof.NativeSupport.CorrelationMatching.Construction.Estimates
import YangMills.WilsonProof.NativeSupport.ContinuumConstruction.GroupOrdinaryTarget

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonFlashScoredGroupReference
open YangMills YangMills.MSbar YangMills.Matching YangMills.CorrelationMatching
open WilsonGraphStandaloneCorrelation

variable (g : GaugeGroup) (hg : g.IsSimple)

theorem agrees : Ordinary.SeparatedValidity.Agrees (_root_.IssuedMaxwell.GraphCoefficients.issued g).correlation
    (graphCoefficient g) :=
  fun n k a x hx => WilsonGraphGroupPositionReference.agreement g n k a x hx

theorem bareAgrees : Ordinary.SeparatedValidity.Agrees (bare g) (graphCoefficient g) :=
  fun n k a x hx => (WilsonGraphGroupPositionReference.agreement g n k a x hx).symm.trans
    (agrees g n k a x hx)

include hg in
theorem determined : OPEMatching.HasReference g :=
  (Ordinary.SeparatedValidity.determinedIff (B := maxwellReference g) (bareAgrees g)).mp
    (GroupOrdinaryTarget.determined g hg)

theorem issued :
    (OPEMatching.reference g (determined g hg)).ope = (_root_.IssuedMaxwell.GraphCoefficients.issued g).ope :=
  (Ordinary.eq_read (maxwellReference g) (determined g hg)
    ((Ordinary.SeparatedValidity.validIff (B := maxwellReference g) (bareAgrees g) _).mp
      (GroupOrdinaryTarget.valid g hg))).symm

theorem named :
    (OPEMatching.reference g (determined g hg)).ope = _root_.IssuedMaxwell.GraphReader.name g :=
  (issued g hg).trans ((GroupOrdinaryTarget.numerical g hg).trans (GroupOrdinaryTarget.named g hg))

abbrev normalization : Normalization g :=
  let I := WilsonGraphGroupPositionReference.external g hg
  ⟨I.menu, I.conversion, I.realization⟩

theorem calibrated : GroupCalibration g (normalization g hg) := by
  let I := WilsonGraphGroupPositionReference.external g hg
  let N := normalization g hg
  refine ⟨⟨rfl, I.admissible, I.everyBareSlope _ rfl, I.valid _ rfl, fun _ _ => rfl⟩, ?_⟩
  have available : Nonempty {P : MSbar.PositionPrescription (maxwellReference g) // MSbar.Admissible P} :=
    ⟨⟨I.menu, I.admissible⟩⟩
  simpa only [groupMenu, dif_pos available] using
    (show some N.prescription = some (MSbar.nominatedMenu available).val from rfl)

theorem stress : ∃! P : WardStress.Series (maxwellReference g),
    WardIdentities g (normalization g hg).conversion.conversion P :=
  (CorrelationMatching.Construction.graphEstimates.{0} g hg id strictMono_id).uniqueStress

end YM.Integration.WilsonFlashScoredGroupReference
end
