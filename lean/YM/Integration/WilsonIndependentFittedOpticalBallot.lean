import YM.Integration.WilsonIndependentFittedStoppedWage
import YM.Integration.WilsonIndependentFittedEarlyGeometry
import YM.Integration.WilsonIndependentMatchedCensusReceipt

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentFittedOpticalBallot
open WilsonCoeffUV WilsonCoeffUV.Cosmos WilsonCoeffUV.Shard
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Bulb Realm PathCost Ore
open WilsonOriginalPublicPlantedStableCredit (span)
open WilsonIndependentMatchedFittedSeat (dose)
open WilsonIndependentFittedStoppedWage (numerical window)
open WilsonIndependentFittedPivotCash (gross)
open WilsonIndependentMatchedCensusReceipt (Filed)
open WilsonIndependentEvenPassport (count old)
open WilsonIndependentExactPlate (Requests)
open RegulatorIR RegulatorIR.Ledger
open scoped BigOperators Topology Classical
variable {G:Gauge}{h D k e u:ℕ}{F:Labels.Frame G h}{H:Hol G}{T:SectionData F}{p:h<D}
    {v:Rails h k u e}{E W K U:Credit}

theorem restored (X:CutsP H T p v E W K U)(L:Torch H T p v E W K)(run:XSpace.Run)
    (base idx f:ℕ)(amp δ η fee:ℝ)(stem:TowerS G D)(fx:Filed X L run base idx f amp δ η fee stem)
    (pos:0<δ)(a:ℝ):|a/amp| *X.fuel=|a| *fee:=by
  have wage:=fx.charge a
  change |a/amp| *(δ^(-η)*X.fuel)=|a| *(δ^(-η)*fee) at wage
  have common:δ^(-η)*(|a/amp| *X.fuel)=δ^(-η)*(|a| *fee):=by
    calc _=|a/amp| *(δ^(-η)*X.fuel):=by ring
         _=_:=wage
         _=_:=by ring
  exact mul_left_cancel₀ (Real.rpow_pos_of_pos pos _).ne' common

theorem original (H:Hol G)(T:SectionData F)(p:h<D)(v:Rails h k u e)(E W K U:Credit)
    (run:XSpace.Run)(base phase:ℕ)(ha:0<base)(good:4≤phase)(B η:ℝ)(positive:0<η):
    ∀ᶠ idx:ℕ in atTop,∀(i:Requests base),i.val=idx →
      let δ:=(run.step i.val).spacing
      ∀(X:CutsP H T p v E W K U)(L:Torch H T p v E W K)(f:ℕ)(amp ξ fee:ℝ)(stem:TowerS G D),
      Filed X L run base i.val f amp δ ξ fee stem →
      L.L.V.anchor=f →
      (∀m≤count run base i.val,L.L.V.y (f+m)≤B) →
      (∀w:Flap (WilsonIndependentExactPlate.M run base),w.volW=i →
        (L.L.V.draws.clock.op (f+(count run base i.val-(w.offset+1))) 0).patch=
          (WilsonIndependentExactPlate.S run base ha phase good).pactP w) →
      ∀(stop:ℕ),stop≤old run base i.val →∀(q:ℕ),q≤e →∀a g:ℝ,
        gross X (f+stop) q g (dose X (a/amp))≤numerical X (f+stop) q g (dose X (a/amp))+
        2*|g|^(q+1)*((Fintype.card (Alma F):ℝ)*((q+1:ℕ):ℝ)*
          (δ^(-((h:ℝ)+η))*(|a| * fee))):=by
  obtain ⟨C,V,olderPay⟩:=WilsonIndependentFittedStoppedWage.original H T p v E W K U
  have half:0<η/2:=half_pos positive
  filter_upwards [WilsonIndependentFittedEarlyGeometry.payment run C
    (WilsonIndependentFittedEarlyGeometry.cost run base B) (η/2) half,
    WilsonOriginalPublicPlantedStableCredit.credit (H:=H) (T:=T) (p:=p) (v:=v)
      (E:=E) (W:=W) (K:=K) (U:=U) run V B (η/2) half] with idx early home i hi δ X L f amp ξ fee stem fx anchor ages acts stop hs q hq a g
  subst idx
  have shared:X.vesselsC=L.L.V:=congrArg (fun Z=>Z.L.V) fx.school
  have atHome:X.vesselsC.y X.m≤B:=by rw [shared,fx.report];exact ages _ (Nat.le_add_right ..)
  have rent:=home X atHome fx.scale
  have root:X.vesselsC.anchor≤f+stop:=by rw [shared,anchor];omega
  have oldDate:f+stop≤X.m:=fx.report ▸ Nat.add_le_add_left hs f
  let I₀:=window X (f+stop) root oldDate
  have dated:I₀.Age≤WilsonIndependentFittedEarlyGeometry.cost run base B*(i.val:ℝ)^2:=by
    let n:=old run base i.val-stop
    have length:X.m-(f+stop)=n:=by dsimp only [n];rw [fx.report];omega
    have ends:f+stop+n=f+old run base i.val:=by dsimp only [n];omega
    change X.vesselsC.y (f+stop)+(X.vesselsC.draws.S.scale (f+stop+(X.m-(f+stop)))-
      X.vesselsC.draws.S.scale (f+stop))+((X.m-(f+stop):ℕ):ℝ)≤_
    rw [length,ends,shared]
    exact WilsonIndependentFittedEarlyGeometry.housed run base phase ha good i L.L.V.draws f
      acts stop hs B _ (ages _ (hs.trans (Nat.le_add_right ..)))
  have earlyRent:=early I₀.Age (zero_le_one.trans I₀.warm) dated
  have δpos:0<δ:=(run.step i.val).positive
  have span_exact:(Real.exp (span X X.i))^h=δ^(-(h:ℝ)):=by
    rw [fx.scale,Real.exp_neg,Real.exp_log δpos,Real.rpow_neg δpos.le,Real.rpow_natCast,inv_pow]
  have wage:=olderPay X (f+stop) (a/amp) g root oldDate q hq
  refine wage.trans (add_le_add_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
    (by positivity)) (by positivity)) _)
  have paid:=restored X L run base i.val f amp δ ξ fee stem fx δpos a
  rw [paid,span_exact]
  have income:0≤|a| *fee:=paid ▸ mul_nonneg (abs_nonneg _) X.hf
  calc
    _ = ((C.buy I₀.Age*V.buy X.Age)*δ^(-(h:ℝ)))*(|a| *fee):=by ring
    _ ≤ ((δ^(-(η/2))*δ^(-(η/2)))*δ^(-(h:ℝ)))*(|a| *fee):=by
      gcongr
      · exact zero_le_one.trans (V.purchase X.windowC.warm)
    _ = _:=by rw [←Real.rpow_add δpos,←Real.rpow_add δpos];congr 2;ring

end YM.Integration.WilsonIndependentFittedOpticalBallot
