import YM.Integration.WilsonThermometerFundedWeakCells
import YM.Integration.WilsonThermometerMarchNomination

/-! Publish the same intrinsic weak field in every occupied face and read its actual conditional at every prior. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerWeakPublication
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address RG05Readout.Records
open RG17 Climb Trace.Pilot Table Spec Marker MergeProof MergeProof.Accent
open Extra.Multi Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetResidue WilsonThermometerOwnOffsetField
open WilsonPositionThermometerGradedSource WilsonThermometerMarchSource WilsonThermometerFundedWeakCells
open scoped Classical Topology BigOperators
variable {G : Gauge} (R : Run G) {m k N p : ℕ}
local notation "J" => Stock.census (Fin 3)

def weight (k : ℕ) (i : Fin 3) (y : Palette R.family (WilsonThermometerFundedWeakCells.degree i)) : ℂ :=
  ((R.family.S.a k:ℂ)^(WilsonThermometerFundedWeakCells.degree i))*((charge y:ℝ):ℂ)⁻¹

theorem planted (o : Fin 3 → Site (R.family.side N p)) (Q : (i : Fin 3) → Emblems R.family (WilsonThermometerFundedWeakCells.degree i))
    (h : k≤N) (y : (i : Fin 3) → Palette R.family (WilsonThermometerFundedWeakCells.degree i)) (i : Fin 3) :
    WilsonThermometerIntrinsicRoster.source R WilsonThermometerFundedWeakCells.degree o (fun i=>reduce (y i)) Q h i =
      weight R k i (y i) • R.family.O N p (WilsonThermometerWeakEquationCost.column R (p:=p) (Q i) h (y i)) (o i) := by
  let x:=WilsonThermometerWeakEquationCost.column R (p:=p) (Q i) h (y i)
  have head : (R.family.factory (WilsonThermometerFundedWeakCells.degree i) N p).terminal (finer (Q i) h (reduce (y i)) (primaryLetter (WilsonThermometerFundedWeakCells.degree i))) =
      ((charge (y i):ℝ):ℂ)⁻¹ • x := by
    rw [reduce,map_smul,Pi.smul_apply]
    exact (R.family.factory (WilsonThermometerFundedWeakCells.degree i) N p).terminal.map_smul _ _
  unfold WilsonThermometerIntrinsicRoster.source WilsonThermometerOwnOffsetNectar.birth
  rw [head]
  exact (congrArg (((R.family.S.a k:ℂ)^(WilsonThermometerFundedWeakCells.degree i)) • ·)
    ((R.family.linearO N p (WilsonThermometerFundedWeakCells.degree i) (o i)).map_smul ((charge (y i):ℝ):ℂ)⁻¹ x)).trans (smul_smul ..)

theorem deposits (o : Fin 3 → Site (R.family.side N p)) (V : (i : Fin 3) → Sight R.family (WilsonThermometerFundedWeakCells.degree i) p)
    (Q : (i : Fin 3) → Emblems R.family (WilsonThermometerFundedWeakCells.degree i)) (h : k≤N) (y : (i : Fin 3) → Palette R.family (WilsonThermometerFundedWeakCells.degree i))
    {t : ℕ} (filed : WilsonThermometerIntrinsicRoster.filed R WilsonThermometerFundedWeakCells.degree o (fun i=>reduce (y i)) V Q J h t)
    (hm : m≤N) (s : (Stock.census (Fin 3)).Mode) (U : Config G (R.family.side m p)) :
    (WilsonThermometerIntrinsicRoster.density R WilsonThermometerFundedWeakCells.degree o (fun i=>reduce (y i)) Q J h hm U).part s =
      (R.family.path.rep N p m).eval U • actualTransport R.family (N:=N) (fun U =>
        ∏ i∈s.val,weight R k i (y i) *
          R.family.O N p (WilsonThermometerWeakEquationCost.column R (p:=p) (Q i) h (y i)) (o i) U) hm U := by
  let f:=WilsonThermometerIntrinsicRoster.source R WilsonThermometerFundedWeakCells.degree o (fun i=>reduce (y i)) Q h
  let bank:=R.family.path.rep N p
  have bill:=(filed N h (le_rfl : N≤N)).1
  simp only [WilsonThermometerIntrinsicRoster.density,gust_base] at bill
  rw [WilsonThermometerIntrinsicRoster.density,actualTransport_unnormalize R.family R.makes (le_rfl : N≤N)]
  have part:=congr_fun (pushpart hm (Accent.birth J (bank N) f) s bill) U
  rw [part]
  have terms (W) : ((Accent.birth J (bank N) f) W).part s =
      (bank N).eval W • (∏ i∈s.val,weight R k i (y i) *
        R.family.O N p (WilsonThermometerWeakEquationCost.column R (p:=p) (Q i) h (y i)) (o i) W) := by
    unfold Accent.birth Accent.Mach
    rw [Poly.part_smul,pass_fire,Complex.real_smul]
    congr 1
    exact Finset.prod_congr rfl fun i _=>congrFun (planted R o Q h y i) W
  simp_rw [terms]
  rfl

theorem original (simple : G.Simple) (shop : RG05Preconstruction.ReadoutPurchase R.b) :
    ∃ t≥9, ∀ᶠ k : ℕ in atTop, ∀ p N (h:k≤N) (o : Fin 3 → Site (R.family.side N p)),
      (∀ i j, i≠j→(R.family.path.levels.budget k).B^2 <
        separation (WilsonThermometerOwnOffsetJoint.origins R o k i) (WilsonThermometerOwnOffsetJoint.origins R o k j)) →
      ∃ (V : (i:Fin 3)→Sight R.family (WilsonThermometerFundedWeakCells.degree i) p) (Q : (i:Fin 3)→Emblems R.family (WilsonThermometerFundedWeakCells.degree i)),
        (∀ i,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) k N p (WilsonThermometerFundedWeakCells.degree i)
          (digits R N p (o i)) (V i) (Q i)) ∧
        (∀ b≥k, ∀ s:(Stock.census (Fin 3)).Mode, WilsonThermometerMarchFaces.inverse R t k b s ≤
           R.family.path.levels.clock.hatBeta b ^ (3*(t+1)*(b-k+1))) ∧
        ∀ y : (i:Fin 3)→Palette R.family (WilsonThermometerFundedWeakCells.degree i),
        WilsonThermometerIntrinsicRoster.filed R WilsonThermometerFundedWeakCells.degree o (fun i=>reduce (y i)) V Q J h t ∧
        ∀ m (hm:m≤N) s U,
          (WilsonThermometerIntrinsicRoster.density R WilsonThermometerFundedWeakCells.degree o (fun i=>reduce (y i)) Q J h hm U).part s =
            (R.family.path.rep N p m).eval U • actualTransport R.family (N:=N) (fun Z =>
              ∏ i∈s.val, weight R k i (y i) *
                R.family.O N p (WilsonThermometerWeakEquationCost.column R (p:=p) (Q i) h (y i)) (o i) Z) hm U := by
  obtain ⟨t,ht,book⟩:=WilsonThermometerMarchRoster.original R simple shop
  refine ⟨t,ht,book.mono ?_⟩
  intro k go p N h o far
  obtain ⟨V,Q,record,posted,cost⟩:=go p N h o far
  refine ⟨V,Q,record,cost,fun y=>?_⟩
  have one:=posted (fun i=>reduce (y i)) (fun i=>small (y i))
  exact ⟨one,fun _ hm=>deposits R o V Q h y one hm⟩

end YM.Integration.WilsonThermometerWeakPublication
