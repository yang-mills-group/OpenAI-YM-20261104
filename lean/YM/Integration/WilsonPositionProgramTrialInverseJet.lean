import YM.Integration.WilsonPositionProgramTrialPublicSlope
import YM.Integration.WilsonPositionProgramTrialSurveyRows

/-! The genuine numerical constant and first coefficient of every normalized
field, solved at its actual incoming clock on the original finite field basis. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialInverseJet
open Filter Function Finset Matrix Lattice Wilson RG RG.Supply PhysicalNext.Repeat.Legato Precision Source Labels PowerSeries
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Blue WilsonCoeffUV.Embroider
open WilsonCoeffUV.Shard WilsonCoeffUV.Power WilsonCoeffUV.Soil
open WilsonPositionProgramTrialFittedLens (ticket matrix)
open scoped BigOperators Classical
open WilsonPositionProgramTrialFittedTable (head change)
variable {G:Gauge}{h e:ℕ}{F:Frame G h}


open WilsonPositionProgramTrialReverseLens (received)


open WilsonPositionProgramTrialPublicSlope (grade reported)
variable (H:Hol G)(Q:SealR G){U V:Credit}(T:Theatre H Q.ans Q.path e U V){m K N:ℕ}
variable (entered:T.V.anchor ≤ m)(before:m ≤ K)(live:K ≤ N)

include entered before live in
theorem regular:IsUnit (change T.V.draws T.V.paid Q N m K 0).det:=by
  have visit:m+(K-m) ≤ N:=by omega
  have eligible:=ebbing T entered visit false
  rw [change,Matrix.det_mul,line0,←RingHom.map_det]
  exact (wick_unit _ (production T (before.trans live) entered).1 _ _).mul (eligible.1.map _)

include entered before live in
theorem solved (X:Q.Rider):
    let L:=T.V.draws
    let O:=T.V.paid
    let A:=change L O Q N m K 0
    let B:=change L O Q N m K 1
    let w:=received L O Q m K N X
    grade w 0=A⁻¹ *ᵥ grade X 0 ∧
      grade w 1=A⁻¹ *ᵥ (grade X 1-B *ᵥ (A⁻¹ *ᵥ grade X 0)):=by
  intro L O A B w
  have unit:IsUnit A.det:=regular H Q T entered before live
  have read:=WilsonPositionProgramTrialPublicSlope.reported Q N m K H T entered before live T.V.hG T.V.green X
  change A *ᵥ grade w 0=grade X 0 ∧ B *ᵥ grade w 0+A *ᵥ grade w 1=grade X 1 at read
  have restore (y:Alma Q.F→ℝ):A⁻¹ *ᵥ (A *ᵥ y)=y:=by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ unit,Matrix.one_mulVec]
  have zero:grade w 0=A⁻¹ *ᵥ grade X 0:=by rw [←read.1,restore]
  refine ⟨zero,?_⟩
  calc grade w 1=A⁻¹ *ᵥ (A *ᵥ grade w 1):=(restore _).symm
       _=A⁻¹ *ᵥ (grade X 1-B *ᵥ (A⁻¹ *ᵥ grade X 0)):=by rw [←zero,←read.2,add_sub_cancel_left]

open WilsonMaxwellThermometerSurveyCourse (shelf)
open WilsonMaxwellThermometerSurveyIncome (prices)
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonPositionProgramTrialReverseLens (input)
variable {a D k u:ℕ}(R:Run G)(W:XSpace.Initialize G)(l d:Fin (a+1)→ℕ)(fit:∀i,l i<d i)
theorem original (simple:G.Simple)(s:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices s R.kit)
    (pub:prices W R.kit)(big:h<D)(rails:Rails h k u e)(cap:capP (deck (G:=G) l d fit) ≤ k):
    let L:=R.family.path.levels
    let O:=R.metals.O
    ∀ᶠ j:ℕ in atTop,∀tag m K N,j ≤ m → m ≤ K → K ≤ N →
      let Q:=shelf W l d fit tag
      ∀(X:Herit Q) i,
        let A:=change L O (Q i) N m K 0
        let B:=change L O (Q i) N m K 1
        let w:=input L O Q m K N X i
        IsUnit A.det ∧ grade w 0=A⁻¹ *ᵥ grade (X i) 0 ∧
          grade w 1=A⁻¹ *ᵥ (grade (X i) 1-B *ᵥ (A⁻¹ *ᵥ grade (X i) 0)):=by
  intro L O
  filter_upwards [WilsonMaxwellThermometerSurveyCourse.original R W l d fit simple s funded pub big rails cap] with j sale
  obtain ⟨_,Y,levels,cash,_,home,_,_,_,all⟩:=sale
  intro tag m K N late before live Q X i A B w
  obtain ⟨rows,_⟩:=all tag
  let b:=(rows i).some
  have paid:b.p.f.arch.V.anchor ≤ m:=by rw [b.p.tap,home];exact late
  have rank:=regular _ (Q i) b.p.f.arch paid before live
  have formula:=solved _ (Q i) b.p.f.arch paid before live (X i)
  refine ⟨?_,?_⟩
  · simpa only [A,L,O,b.p.lands,b.p.modes,levels,cash] using rank
  · simpa only [A,B,L,O,w,input,b.p.lands,b.p.modes,levels,cash] using formula

end YM.Integration.WilsonPositionProgramTrialInverseJet
end
