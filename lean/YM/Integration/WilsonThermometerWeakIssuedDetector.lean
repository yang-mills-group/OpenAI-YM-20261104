import YM.Integration.WilsonThermometerWeakDetectorStake

/-! Issue one fixed independent detector on the displaced measured Wilson source.
All copies use the same Wick-calibrated basis. The reconstruction holds for every
presentation of its actual signed transfer, including the presentation of the joint post. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakIssuedDetector
open Function Filter Set MeasureTheory RG RG12 Extra.Histories Lattice Wilson Source Labels
open RG05Readout Native Address Many Records Harvest Push.GridApprox Copper Push Marker
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage Extra.Multi Menu
open Trace.Physical Push.Local GermGraph Next.Rank.Spindle Next.Rank Configuration Normal Rise
open Perch Glimmer LiftMark Beamer Station Atlas Tariffs MvPolynomial Ribbon
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonThermometerWeakBasisCalibration WilsonThermometerWeakPhysicalCombination
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {d H:ℕ}
local notation "Rf" => R.family
local notation "A" => R.family.path.levels
local notation "B" => WilsonThermometerOffsetLedger.cash R

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (S:Rules G)
    (exam:Tapes.Panel H) (dH:d≤H) (v:(Rf).label d):
    ∀ᶠ k:ℕ in atTop,∀ N p (_:k≤N),
    let P:=(Rf).path.rep N p k;let g:=GaugeScale Rf k N p;let s:=clim (A) k
    let ξ:=exam.bag ((A).clock.J k);let F:=(Rf).labels.level d;let b:=sizeQ Rf k
    let feed:=Price.weightTag Rf d (mag (A) ξ.band k) v
    ∃(K:Provision Rf d k N p (scouts Rf k) b)(wide:4*b≤wood (A) k),ξ.taylor+1≤P.p.order →
    ∀ (z:Site ((Rf).side N p)) (V:Sight Rf d p) (r:Emblems Rf d),
    Enrolled R.makes R.doors B k N p d (digits R N p z) V r →
    ∀ E:AtlasData G (Rf).S p,Hail Rf k p ξ.taylor E →
    ∃ (u:F.Coeff) (L:poly (Up Rf k p b)),
    let W:=sender K.length P.p.threshold g L;let y:=chunk (C:=Rf) (primaryLetter d) u
    size y≤bill (ξ.credit-1) s ∧ coin W≤bill ξ.credit s ∧ W.totalDegree≤ξ.taylor ∧ Spirit W ∧
    WilsonThermometerWeakGroupCoordinate.contracted R d wide E W=expose F feed ∧
    ∀ (Y:Coefficient F ((Rf).side k p)),V k y (line (primaryLetter d))=invoice Y 0 ((Rf).localSection d) P →
    ∀ U,Healthy (tau (A) k) (Spindle.patch b 0) U →
      ‖Y.exponentialEntry 0 ((Rf).localSection d) P U-signet 0 g W U‖≤bill (1/8-(ξ.taylor:ℝ)) s*size y:=by
  filter_upwards [WilsonThermometerWeakMeasuredBasis.original R simple shop S d exam.θ (dH.trans exam.enough),
    WilsonThermometerWeakDetectorStake.original R simple exam dH v,supports exam.θ Rf simple R.makes] with k basis prices gauge N p hk P g s ξ F b feed
  obtain ⟨K,wide,publish⟩:=basis N p hk
  refine ⟨K,wide,?_⟩
  intro deg z V r paid E hail
  have θ:ξ.taylor=exam.θ:=exam.stable _
  rw [θ] at deg hail
  obtain ⟨X,Q,filedX,terms,read⟩:=publish deg z V r paid
  let H' i:=sender K.length P.p.threshold g (Q i)
  obtain ⟨T,rent,hT⟩:=read E hail
  let h:=P.p.threshold/g
  let u:=T.symm (F.scaled h feed)
  let y:=chunk (C:=Rf) (primaryLetter d) u
  let L:=filed F Q u
  have h0:h≠0:=(div_pos P.p.threshold_pos (gauge N hk p).1).ne'
  have contract:=WilsonThermometerWeakPhysicalCombination.calibrated R wide E H' T rent h0 (fun i=>by obtain ⟨v,eq,see⟩:=hT i;exact ⟨v,eq.symm,see⟩) feed
  have full:F.coeffSize u≤bill (ξ.credit-1) s:=contract.1.trans (prices N p hk).1
  have field:sender K.length P.p.threshold g L=filed F H' u:=by
    simp only [L,filed,Spindle.sender,dustAt,map_sum,map_smul,H']
  have book:=stock F H' (fun i=>(terms i).1) (fun i=>(terms i).2.1) (fun i=>(terms i).2.2.1) u
  refine ⟨u,L,?_,?_,?_,?_,?_,?_⟩
  · rw [size_chunk];exact full
  · rw [field];exact book.1.trans ((prices N p hk).2 _ full)
  · rw [field,θ];exact book.2.1
  · rw [field];exact book.2.2
  · rw [field];exact contract.2
  · intro Y eq U healthy;rw [field,θ,size_chunk]
    exact tested R V g H' X (fun i=>(filedX i).2.2) (fun i=>(terms i).2.2.2)
      u Y eq U healthy

end YM.Integration.WilsonThermometerWeakIssuedDetector
end
