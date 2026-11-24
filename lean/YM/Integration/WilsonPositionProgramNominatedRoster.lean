import YM.Integration.WilsonPositionProgramThermometerCoordinates
import YM.Integration.WilsonPositionProgramOrderedPinReturn

/-! Before both physical regulators, compare the complete original ordered
programme at two ultraviolet cutoffs with the very same numerically released
(6,4,4) field at either cutoff, at the genuine translated child root. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionProgramNominatedRoster
open Function Filter Finset Lattice Wilson Labels RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress Next.Rank Next.Rank.East
open MergeProof.East Next.Rank.Price WilsonOriginalThermometerPalette WilsonPositionThermometerCapStation
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.PathCost WilsonCoeffUV.Blue WilsonCoeffUV.Shard
open WilsonCoeffUV.Embroider Source Source.Drops WilsonPositionProgramThermometerCoordinates
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonPositionProgramNormalizedMaster (fee)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
  {a h D k u e:ℕ}

def selected (v:Fin (a+1)→Fin 3)(d:Fin (a+1)→ℕ)(fit:∀i,levels (v i)<d i)
    (A:Group R.family 6)(m N p:ℕ)(phase:Fin 3→ℂ →L[ℝ] ℝ):
    Herit (deck (G:=G) (levels ∘ v) d fit):= WilsonPositionProgramSubmittedCoordinates.submitted R
      (levels ∘ v) d fit (fun i=>upper R A m N p (v i)) (phase ∘ v)

theorem selected_fee (v:Fin (a+1)→Fin 3)(d:Fin (a+1)→ℕ)(fit:∀i,levels (v i)<d i)
    (A:Group R.family 6)(m N p e:ℕ)(phase:Fin 3→ℂ →L[ℝ] ℝ)(i:Fin (a+1)):
    fee (selected R v d fit A m N p phase) e i=
      fee (issued R (fun j=>levels j+1) (fun _=>Nat.lt_succ_self _) A m N p phase) e (v i) := rfl

def reading (v:Fin (a+1)→Fin 3)(d:Fin (a+1)→ℕ)(fit:∀i,levels (v i)<d i)
    (A:Group R.family 6)(m N p:ℕ)(phase:Fin 3→ℂ →L[ℝ] ℝ)(b:ℕ)
    (φ:Wilt (deck (G:=G) (levels ∘ v) d fit))(y:ℝ)(o:CellR)(root:Cover)(top:ℕ):Era G ℝ:=
  let L:=R.family.path.levels
  let Q:=deck (G:=G) (levels ∘ v) d fit
  let X:=selected R v d fit A m N p phase
  locale o (cruises L R.metals.O top (capP Q) top b (shifted
    (HearthC Q L R.metals.O φ (normalized L R.metals.O Q X m top) m top top y)
    (WilsonPositionProgramPinnedHearthHistory.pin L.S b top root)))

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices v R.kit)
    (big:h<D)(rails:Rails h k u e)(child:Fin (a+1)→Fin 3)(d:Fin (a+1)→ℕ)(fit:∀i,levels (child i)<d i)
    (cap:capP (deck (G:=G) (levels ∘ child) d fit) ≤ k)(δ:ℝ)(pos:0<δ):
    let Q:=deck (G:=G) (levels ∘ child) d fit
    let L:=R.family.path.levels
    ∀ᶠ j:ℕ in atTop,∀ᶠ m:ℕ in atTop,j ≤ m → 1 ≤ zz L m →
    ∀A:Group R.family 6,A.station.k=m → A.station.checked f H A.horizon →
    ∀(phase:Fin 3→ℂ →L[ℝ] ℝ)(Z:ℝ)(B:Fin (a+1)→ℝ)(ε:ℝ),0<ε →
    ∃K:ℕ,m ≤ K ∧ ∀N p:ℕ,m<N → ∀n n':ℕ,K ≤ n → K ≤ n' →
    ∀ b:ℕ,j ≤ b → b ≤ m → ∀(φ:Wilt Q)(y:ℝ)(o:CellR)(root:Cover),
      Compar L.S (zz L) b m ≤ Z → Bough Q φ y Z B →
      let read:=reading R child d fit A m N p phase b φ y o root
      ∀t r:ℕ,t ≤ e → Fruit root 1 u ((read n).2 t r-(read n').2 t r) ε := by
  intro Q L
  obtain ⟨c,w,settled⟩:=WilsonPositionProgramOrderedPinReturn.original R simple v paid big rails (levels ∘ child) d fit cap
  filter_upwards [settled] with j booked
  filter_upwards [WilsonPositionProgramThermometerCoordinates.original (f:=f) (H:=H) R simple δ pos e
      (fun j=>levels j+1) (fun _=>Nat.lt_succ_self _)]
    with m charged
  intro late clock A date checked phase Z B ε tol
  let money (i:Fin (a+1)):ℝ:=price R e (child i)*‖phase (child i)‖*((L.clock.hatBeta m)^δ*salary R A)
  let gross:=c.buy Z*∏ i,B i*(w.buy (zz L m)*money i)
  let F:=max 1 gross
  obtain ⟨K,stop,_,all⟩:=booked m late F ε (zero_le_one.trans (le_max_left ..)) tol
  refine ⟨K,stop,?_⟩
  intro N p actual n n' hn hn' b after before φ y Z₀ root room shape
  let X:=selected R child d fit A m N p phase
  have wz:0≤w.buy (zz L m):=zero_le_one.trans (w.purchase clock)
  have bound(i:Fin (a+1)):fee X e i ≤ money i:=by
    rw [show fee X e i=_ from selected_fee R child d fit A m N p e phase i]
    exact charged A date checked N p actual phase (child i)
  have fee₀(i:Fin (a+1)):0≤fee X e i:=Finset.sum_nonneg fun _ _=>Finset.sum_nonneg fun _ _=>norm_nonneg _
  have wage:c.buy Z*∏ i,B i*(w.buy (zz L m)*fee X e i) ≤ F:=by
    apply le_trans _ (le_max_right 1 gross)
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans (c.purchase shape.pos))
    apply Finset.prod_le_prod
    · intro i _; exact mul_nonneg (shape.lanes i).1 (mul_nonneg wz (fee₀ i))
    · intro i _; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (bound i) wz) (shape.lanes i).1
  dsimp only
  intro t r grade
  exact (all n n' hn hn' X b after before φ B y Z Z₀ root room shape wage t r grade).2

end YM.Integration.WilsonPositionProgramNominatedRoster
end
