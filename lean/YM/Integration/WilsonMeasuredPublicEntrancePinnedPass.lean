import YM.Integration.WilsonMeasuredPublicEntranceOrderedPins
import YM.Integration.WilsonMeasuredPublicEntranceCellWords
import YM.Integration.WilsonOriginalTwoFlatGridScaling
/-! The physical Gibbs reading and the actual uncut submission on the same translated grid and public axes. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntrancePinnedPass
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Source Labels Cells
open Extra.Histories PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonThermometerUnitFilingCoarse
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonReflectedPublicOrientedFaces (displayed)
open OPE Next.Rank Overlay Bid Push.GridApprox MergeProof Ribbons Accent ManyCopies
open WilsonMeasuredPublicEntrancePanel (Panel Reading)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (submitted difference)
open WilsonMeasuredPublicEntranceOrderedBasis (form)
open WilsonMeasuredPublicEntranceOrderedPins (Release publicValue)
open Extraction Spec PertExtension PertExtension.LatticePT
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n:ℕ}(d:Fin n→ℕ){N per f K u:ℕ}
local notation "C₀" => R.family
local notation "H" j:max => R.family.path.levels.clock.hatBeta j
local notation "full" => Stock.final (Fin n)
variable {requested power t:ℕ}{B:ℝ}{fk:f≤K}{cut:K≤N}

theorem cutoff(o:Fin n → Cover)(Y:∀v,(C₀).label (d v))(turn:Fin n→Motion):
    (C₀).omega N per (WilsonMeasuredPublicEntranceCellWords.physical R d Y turn (snap (C₀) f per o) full)=
      WilsonMeasuredPublicEntranceOrderedPins.physical (C:=R.family) d f o N per (fun v=>displayed R (d v) (Y v) (turn v)):=by
  congr 1

def ear (file:Filed R d K)(fk:f≤K)(_cut:K≤N)(road:u≤K)
    (Y:∀v,(C₀).label (d v))(turn:Fin n→Motion)(loc:Fin n→Site ((C₀).side f per))
    (s:(Stock.census (Fin n)).Mode):ℂ:=
  reading R (N:=N) (numerator R N per K (submitted R d (N:=N) file fk Y turn loc s)) u road

theorem phase (file:Filed R d K)(fk:f≤K)(cut:K≤N)(road:u≤K)
    (Y:∀v,(C₀).label (d v))(turn:Fin n→Motion)(loc:Fin n→Site ((C₀).side f per))
    (s:(Stock.census (Fin n)).Mode):
    let raw:=WilsonMeasuredPublicEntranceCellWords.physical R d (N:=N) Y turn loc s
    (C₀).omega N per raw-ear R d file fk cut road Y turn loc s=
      WilsonOriginalTwoFlatGridScaling.gap R N per u (road.trans cut) raw+
        difference R d file fk cut road Y turn loc s:=by
  intro raw
  have cont:Continuous raw:=continuous_finsetProd _ fun i _=>(C₀).continuousO _ _ _ _ _
  have sc:reading R (N:=N) (credit (C₀) N per 0 raw K cut) u road=
      reading R (N:=N) (credit (C₀) N per 0 raw u (road.trans cut)) u le_rfl:=by
    unfold WilsonThermometerUnitFilingCoarse.reading
    rw [WilsonThermometerUnitFilingCoarse.cutoff R cut road raw cont,gust_base]
  change (C₀).omega N per raw-_ = ((C₀).omega N per raw-_)+
    (reading R (N:=N) (credit (C₀) N per 0 raw K cut) u road-_)
  rw [sc]
  unfold ear
  ring

theorem original {order:Extraction.Order}{S:Table (C₀).book}(F:Final (C₀) order S)
    (o:Fin n → Cover)(generic:Order.grid (C₀) f o ∈ YM.generic n)(H₀:Fin n→ℝ):
    ∃step:Release (C:=R.family) (S:=S) (order:=order) d f o H₀,
    ∀N per K (fk:f≤K)(cut:K≤N) requested power t B (A:Panel R d N per f K fk cut requested power t B)
      (file:Filed R d K),A.slot=file.station → A.axis=file.A N per → A.loc=snap (C₀) f per o →
      ∀u (held:u≤f),Reading R d A held → (∀v,1≤A.M v) → ∀E:Fin n→ℕ,
      (∀v b,b≤d v → (C₀).ref b≤N) →
      (∀v,Next.Rank.Spindle.paid (C₀) (d v) f N per (A.names v)≤A.M v*(H f)^(E v)) →
      ∀desired,desired+∑v,E v≤requested →
      let y:=fun v=>displayed R (d v) (A.names v) (A.turn v)
      (∀v,‖y v‖≤H₀ v) →
      let raw:=WilsonMeasuredPublicEntranceCellWords.physical R d (N:=N) A.names A.turn A.loc full
      let trial:=ear R d file fk cut (held.trans fk) A.names A.turn A.loc full
      let correction:=WilsonOriginalTwoFlatGridScaling.gap R N per u (held.trans (fk.trans cut)) raw
      let bill:=(∏v,WilsonAddressedHomeDose.ceiling (R:=R) (d v) (A.M v))*((H f)^desired)⁻¹
      ‖(C₀).omega N per raw-trial-correction‖≤bill ∧
        ‖trial+correction-form d (step.period per) y‖≤ step.ultraviolet N per+bill ∧
        ‖form d (step.period per) y-publicValue (S:=S) d f o y‖≤ step.volume per:=by
  obtain ⟨step⟩:=WilsonMeasuredPublicEntranceOrderedPins.original F d f o generic H₀
  refine ⟨step,?_⟩
  intro N per K fk cut requested power t B A file station axes positions u held sale one E refs cost desired expo y cap raw trial correction bill
  have paid:=WilsonMeasuredPublicEntranceCellWords.paid R d A file station axes held sale one E refs cost full desired expo
  have receipt:‖(C₀).omega N per raw-trial-correction‖≤bill:=by
    calc
      _=‖difference R d file fk cut (held.trans fk) A.names A.turn A.loc full‖:=by
        congr 1
        have h:=phase R d file fk cut (held.trans fk) A.names A.turn A.loc full
        change (C₀).omega N per raw-trial=correction+_ at h
        linear_combination h
      _≤_:=paid
  have top:(C₀).omega N per raw=WilsonMeasuredPublicEntranceOrderedPins.physical (C:=R.family) d f o N per y:=by
    dsimp only [raw]
    rw [positions]
    exact cutoff R d o A.names A.turn
  refine ⟨receipt,?_,step.outer per y cap⟩
  have a:=step.fine N per y cap
  rw [←top] at a
  calc
    _≤‖(C₀).omega N per raw-form d (step.period per) y‖+‖(C₀).omega N per raw-trial-correction‖:=by
      rw [show trial+correction-form d (step.period per) y=((C₀).omega N per raw-form d (step.period per) y)-((C₀).omega N per raw-trial-correction) by ring]
      exact norm_sub_le ..
    _≤_:=add_le_add a receipt

end YM.Integration.WilsonMeasuredPublicEntrancePinnedPass
end
