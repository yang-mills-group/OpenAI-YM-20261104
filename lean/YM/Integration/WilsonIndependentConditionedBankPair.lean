import YM.Integration.WilsonIndependentConditionedBankCash
import YM.Integration.WilsonIndependentMatchedTotalTop

/-! Whole signed ordinary pair minus its fitted pair, evaluated after the normalized N-vacuum transfer. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankPair
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
abbrev Cut (Q:SealR G)(v:Rails Q.h k u₀ e):=CutsP H Q.ans Q.path v E W K U

def observe (q:ℕ)(g:ℝ)(z:Fin 0→YForest G):Era G ℝ→+ℂ:=
  (measured q g).comp (AddMonoidHom.mk' (fun P:Era G ℝ=>reading P.2 z) fun P Q=>by
    apply PowerSeries.ext
    intro j
    simp [WilsonOlderFreshSoftSocketKinetic.reading])

theorem original (X:Cut (H:=H) (E:=E) (W:=W) (K:=K) (U:=U) Q₁ v₁)
    (Y:Cut (H:=H) (E:=E) (W:=W) (K:=K) (U:=U) Q₂ v₂)
    (levels:Y.ax=X.ax)(prior:Y.tx=X.tx)(vac:Y.N=X.N)(home:Y.m=X.m)(top:Y.ceilC=X.ceilC)
    (host:ℕ)(older:host ≤ X.m)(a b:ℝ)(φ:Rarity Q₁.D)(ψ:Rarity Q₂.D)(y:ℝ)(o:CellR)
    (q:ℕ)(order:q ≤ e)(g:ℝ)(small:|g| ≤ 1)(z:Fin 0→YForest G)(u:ℕ)(η₀ η₁ η₂:ℝ):
    let A:=seat X a φ y o X.i
    let B:=seat Y b ψ y o Y.i
    let U:=receiving X a φ y o X.i
    let V:=receiving Y b ψ y o Y.i
    let rawX:=WilsonIndependentMatchedCoverProfile.word (a • X.pt) φ (paceT X.ax.S X.m X.ceilC) y o Q₁.h
    let rawY:=WilsonIndependentMatchedCoverProfile.word (b • Y.pt) ψ (paceT Y.ax.S Y.m Y.ceilC) y o Q₂.h
    let dx:=dose X a
    let dy:=dose Y b
    Hearing X A B host u η₀ →
    (∀j,Hearing Y A (film Y j 0 ψ y o Y.i) host u η₁) →
    (∀j,Hearing X (film X j 0 φ y o X.i) B host u η₂) →
    ‖view X host q g rawX rawY z-view X host q g U V z‖ ≤
      ((q+1:ℕ):ℝ)*(η₀+gross Y host q g dy*η₁+gross X host q g dx*η₂):=by
  intro A B U V rawX rawY dx dy odd left right
  have aAuth:Auth k A:=(WilsonIndependentMatchedCoveredSeats.traced X a φ y o).1 _ le_rfl
  have bAuth:Auth k B:=(WilsonIndependentMatchedCoveredSeats.traced Y b ψ y o).1 _ le_rfl
  have uAuth:Auth k U:=(WilsonIndependentFittedMixedReturn.paid X dx φ y o).tall v₁.hk
  have vAuth:Auth k V:=(WilsonIndependentFittedMixedReturn.paid Y dy ψ y o).tall v₂.hk
  have hx:rawX=A+U:=WilsonIndependentMatchedTotalTop.placed X a φ y o
  have hy:rawY=B+V:=WilsonIndependentMatchedTotalTop.placed Y b ψ y o
  have after:host ≤ X.ceilC:=older.trans (Nat.le_add_right _ _)
  have incurred:=WilsonIndependentMatchedTotalTop.transferred X.vesselsC after (X.hc.trans X.hn) A B U V aAuth bAuth uAuth vAuth
  have law:=congrArg (observe q g z) incurred
  simp only [map_sub,map_add] at law
  change view X host q g (A+U) (B+V) z-view X host q g U V z=
    view X host q g A B z+view X host q g A V z+view X host q g U B z at law
  have compare(P S:Era G ℝ):view Y host q g P S z=view X host q g P S z:=by
    change measured q g (reading (cruises Y.ax Y.tx Y.N _ Y.ceilC host (agateV P S)).2 z)=
      measured q g (reading (cruises X.ax X.tx X.N _ X.ceilC host (agateV P S)).2 z)
    rw [levels,prior,vac,top]
  have one:=WilsonIndependentFittedMixedCash.cash_le q g small
    (embed (WilsonIndependentFittedMixedReturn.word X host A B 0 z))
  have first:‖view X host q g A B z‖ ≤ ((q+1:ℕ):ℝ)*η₀:=
    one.trans (WilsonIndependentFittedMixedCash.stopped X A B host q u order η₀ odd z)
  have second:‖view X host q g A V z‖ ≤ gross Y host q g dy*(((q+1:ℕ):ℝ)*η₁):=by
    rw [←compare]
    exact (WilsonIndependentConditionedBankCash.original Y host (home ▸ older) A aAuth dy ψ y o q order g small z u η₁ 0).1 left
  have third:‖view X host q g U B z‖ ≤ gross X host q g dx*(((q+1:ℕ):ℝ)*η₂):=
    (WilsonIndependentConditionedBankCash.original X host older B bAuth dx φ y o q order g small z u 0 η₂).2 right
  rw [hx,hy,law]
  apply (norm_add_le ..).trans
  calc
    _ ≤ (‖view X host q g A B z‖+‖view X host q g A V z‖)+‖view X host q g U B z‖:=
      add_le_add (norm_add_le ..) le_rfl
    _ ≤ _:=by nlinarith only [first,second,third]

end YM.Integration.WilsonIndependentConditionedBankPair
