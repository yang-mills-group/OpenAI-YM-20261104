import YM.Integration.WilsonOlderFreshSoftSocketFaces
import YM.Integration.WilsonIndependentCollarWeightedCruise

/-! The signed Figure and socket faces follow the same actual N-quiet through every dated nonbare child before any period, clock evaluation or norm. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketFlux
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonThermometerDeclaredSeeds (Choice)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketFaces (raw print fill cash)
open WilsonReceivedFixedDigitHistory WilsonCoeffUV.Winding

variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I]{D d:I→ℕ}
omit [Fintype I] in
theorem path (L:Levels G)(O:ChartRatio G)(simple:G.Simple)(ratio:LocalRatio O)
    (N:ℕ)(cells:Digits L I)(seed:Outerm G D)(funded:Wellness d seed)(S:Finset I)
    (days m:ℕ)(y:I → Cover)(cut:m+days≤N):
    levelsO (itinerary L O d N cells days m seed y) S=
      cruises L O N (mass d S) (m+days) m (levelsO (seed (WilsonIndependentCollarOrdinaryCruise.address L cells days m y)) S):=by
  induction days generalizing m y with
  | zero=>simp [itinerary,WilsonIndependentCollarOrdinaryCruise.address,cruises_top]
  | succ e ih=>
    let x:=chartIn (loose L m) y (cells m)
    let V:=itinerary L O d N cells e (m+1) seed
    have live:m<N:=by omega
    have inside:m+1+e≤N:=by omega
    have right:=sound L O d N cells simple ratio seed funded e (m+1) inside
    change levelsO (logO L O m N (V x) d) S=_
    rw [step_S L O m N (V x) d live simple ratio (right.level' x),
      cruises_sub L O N (mass d S) _ (show m < m + (e+1) by omega)]
    apply congrArg (verseI L O m N (mass d S))
    simpa only [WilsonIndependentCollarOrdinaryCruise.address,show m+1+e=m+(e+1) by omega] using ih (m+1) x inside

variable (R:Run G)(d:I→ℕ)(b:Columns R d)(κ:(i:I)→Knob (D i))(pt:I→Chamber)
local notation "F_" => WilsonOlderFreshSoftFigures.stencil R D d b κ pt
local notation "L_" => R.family.path.levels
local notation "O_" => R.metals.O

theorem original (simple:G.Simple)(ratio:LocalRatio O_)(L:ℂ→L[ℝ]ℝ)(N per K:ℕ)
    (cells:Digits L_ I)(S:Finset I)(m:ℕ)(older:m≤K)(live:K≤N)(y:I → Cover):
    L 1 • levelsO (itinerary L_ O_ d N cells (K-m) m F_ y) S=
      ∑q:(i:S)→Choice R d i,L (cash R d b S N per K q) •
        levelsO (itinerary L_ O_ d N cells (K-m) m (raw R d κ pt (fill R d S q)) y) S:=by
  classical
  let z:=WilsonIndependentCollarOrdinaryCruise.address L_ cells (K-m) m y
  have same:m+(K-m)=K:=Nat.add_sub_of_le older
  have cut:m+(K-m)≤N:=by omega
  have hf:Wellness d F_:=(OriginalCoverReanchoring.deposited
    (WilsonOlderFreshSoftFigures.seed R D d b κ pt) (fun _ _=>Nat.le_add_left _ _)).1
  have hq (q:(i:S)→Choice R d i):Wellness d (raw R d κ pt (fill R d S q)):=
    (OriginalCoverReanchoring.deposited (WilsonOlderFreshSoftSocketPole.raw R d κ pt (fill R d S q))
      (fun _ _=>Nat.le_add_left _ _)).1
  have f:=placedO _ (hf.level' z) S
  have h (q:(i:S)→Choice R d i):Auth (mass d S) (print R d κ pt z S q):=placedO _ ((hq q).level' z) S
  have one:=WilsonIndependentCollarWeightedCruise.original L_ O_ simple ratio older live
    (Finset.univ:Finset Unit) (fun _=>L 1) (fun _=>levelsO (F_ z) S) (fun _ _=>f)
  have principal:cruises L_ O_ N (mass d S) K m (L 1 • levelsO (F_ z) S)=
      L 1 • cruises L_ O_ N (mass d S) K m (levelsO (F_ z) S):=by simpa using one
  have bank:=congrArg (cruises L_ O_ N (mass d S) K m)
    (WilsonOlderFreshSoftSocketFaces.original R d b κ pt z S (per:=per) live L)
  rw [principal,WilsonIndependentCollarWeightedCruise.original L_ O_ simple ratio older live
    Finset.univ (fun q=>L (cash R d b S N per K q)) (fun q=>print R d κ pt z S q) (fun q _=>h q)] at bank
  rw [path L_ O_ simple ratio N cells F_ hf S (K-m) m y cut,same]
  trans ∑q:(i:S)→Choice R d i,L (cash R d b S N per K q) • cruises L_ O_ N (mass d S) K m (print R d κ pt z S q)
  · exact bank
  · apply Finset.sum_congr rfl
    intro q _
    rw [path L_ O_ simple ratio N cells _ (hq q) S (K-m) m y cut,same]
    rfl

end YM.Integration.WilsonOlderFreshSoftSocketFlux
end
