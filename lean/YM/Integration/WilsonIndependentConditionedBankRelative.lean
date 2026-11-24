import YM.Integration.WilsonIndependentConditionedBankPair
import YM.Integration.WilsonIndependentNotebookDoseReturn

/-! The inverse Wick coordinates for each public column are evaluated before either profile is chosen. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankRelative
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer
open Filter Function Finset Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Wilson Tree Power PowerSeries
open Embroider Precision AnalyticNext.QuarticMatch.Sheets Exterior Fountain Soil Gauge MultiNext.SignedSource Next.Free
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb Realm PathCost Ore
open WilsonIndependentMatchedCoveredSeats (seat)
open WilsonIndependentMatchedPivotSeat (film)
open WilsonIndependentFittedMixedReturn (word planted)
open WilsonIndependentFittedMixedCash (bill embed)
open WilsonIndependentMatchedPivotStop (Hearing)
open WilsonOlderFreshSoftCoverScalar (clock)
open WilsonPhysicalMarkedDefect.RawBank (cash)
open scoped BigOperators Topology Classical
open WilsonIndependentMatchedFittedSeat (dose receiving)
open WilsonIndependentMatchedCoverProfile (word)
open WilsonIndependentFittedPivotCash (measured view gross)
open WilsonOlderFreshSoftSocketKinetic (reading)
open WilsonIndependentConditionedBankCash (amount reserve)
open WilsonPhysicalMarkedDefect.RawProduct (belt)
variable {G:Gauge}{k e u₀:ℕ}{H:Hol G}{Q₁ Q₂:SealR G}
    {v₁:Rails Q₁.h k u₀ e}{v₂:Rails Q₂.h k u₀ e}{E W K U:Credit}
open WilsonIndependentConditionedBankPair (Cut)
theorem original (Z:Credit):∃ L M:Credit,
    ∀(X:Cut (H:=H) (E:=E) (W:=W) (K:=K) (U:=U) Q₁ v₁)
    (Y:Cut (H:=H) (E:=E) (W:=W) (K:=K) (U:=U) Q₂ v₂)
    (_:AheadT H X.vesselsC W U Q₁ Z)(_:AheadT H Y.vesselsC W U Q₂ Z)
    (_levels:Y.ax=X.ax)(_prior:Y.tx=X.tx)(_vac:Y.N=X.N)(_home:Y.m=X.m)(_top:Y.ceilC=X.ceilC)
    (host:ℕ)(_older:host ≤ X.m)(a b:ℝ)(φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)(y:ℝ)(o:CellR)
    (q:ℕ)(_order:q ≤ e)(g:ℝ)(_small:|g| ≤ 1)(z:Fin 0→YForest G)(u:ℕ)(η:ℝ)(_hη:0 ≤ η),
    let A:=seat X a φ y o X.i
    let B:=seat Y b ψ y o Y.i
    let U:=receiving X a φ y o X.i
    let V:=receiving Y b ψ y o Y.i
    let rawX:=WilsonIndependentMatchedCoverProfile.word (a • X.pt) φ (paceT X.ax.S X.m X.ceilC) y o Q₁.h
    let rawY:=WilsonIndependentMatchedCoverProfile.word (b • Y.pt) ψ (paceT Y.ax.S Y.m Y.ceilC) y o Q₂.h
    let dx:=dose X a
    let dy:=dose Y b
    Hearing X A B host u η →
    (∀j,Hearing Y A (film Y j 0 ψ y o Y.i) host u η) →
    (∀j,Hearing X (film X j 0 φ y o X.i) B host u η) →
    let walletX:=X.vesselsC.cash L X.m; let walletY:=Y.vesselsC.cash M Y.m
    let normX:=amount X host q g (WilsonPositionProgramTrialHomeDose.publicDose Q₁ X a)
    let normY:=amount Y host q g (WilsonPositionProgramTrialHomeDose.publicDose Q₂ Y b)
    let high:=2*|g|^(q+1)*(reserve X host q dx+reserve Y host q dy)
    ‖view X host q g rawX rawY z-view X host q g U V z‖ ≤
      (((q+1:ℕ):ℝ)*η)*((1+walletX*normX)*(1+walletY*normY)+high):=by
  obtain ⟨L,salaryX⟩:=WilsonIndependentNotebookDoseReturn.original H Q₁ v₁ E W K U Z
  obtain ⟨M,salaryY⟩:=WilsonIndependentNotebookDoseReturn.original H Q₂ v₂ E W K U Z
  refine ⟨L,M,?_⟩
  intro X Y oldX oldY levels prior vac home top host older a b φ ψ y o q order g small z u η hη
    A B U V rawX rawY dx dy odd left right walletX walletY normX normY high
  have exactFee:=WilsonIndependentConditionedBankPair.original X Y levels prior vac home top host older a b
    φ ψ y o q order g small z u η η η odd left right
  have costX:amount X host q g dx ≤ walletX*normX:=salaryX X oldX host older a q g
  have costY:amount Y host q g dy ≤ walletY*normY:=salaryY Y oldY host (home ▸ older) b q g
  have nonnegX:0 ≤ walletX*normX:=(Finset.sum_nonneg fun _ _=>norm_nonneg _).trans costX
  have nonnegY:0 ≤ walletY*normY:=(Finset.sum_nonneg fun _ _=>norm_nonneg _).trans costY
  have one:1+amount Y host q g dy+amount X host q g dx ≤ (1+walletX*normX)*(1+walletY*normY):=by
    nlinarith only [costX,costY,mul_nonneg nonnegX nonnegY]
  apply exactFee.trans
  rw [WilsonIndependentConditionedBankCash.separated,WilsonIndependentConditionedBankCash.separated]
  dsimp only [high]
  have wage:=mul_le_mul_of_nonneg_left one (show 0 ≤ ((q+1:ℕ):ℝ)*η by positivity)
  dsimp only [dx,dy] at wage ⊢
  linarith only [wage]

end YM.Integration.WilsonIndependentConditionedBankRelative
