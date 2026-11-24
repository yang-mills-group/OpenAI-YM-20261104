import YM.Integration.FundedMarkedCoverRows
import YM.WilsonCoeffUV.Emit.Rerender
import YM.WilsonCoeffUV.Step.Rotation.Offer

/-! The original finite vacuum complement on the one purchased Run.
Buy the concrete one-level path invoice on its actual sheet, then extract
the same graded vacuum and its independently marked forest transport. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedOriginalVacuumPaths
open Filter Function Lattice RG RG.Supply Precision Next.Foundations Wilson Tree
open PhysicalNext PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Physical
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Bloom WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Blue
open WilsonCoeffUV.Power WilsonCoeffUV.Embroider WilsonCoeffUV.Soil WilsonCoeffUV.Fk
open WilsonLimitConstruction
open scoped BigOperators Topology ContDiff Classical

universe u
variable {G : Gauge}

/-- This is the library's measured vacuum rendering invoice at the actual
stage. It precedes every period, physical cutoff, colour and external test. -/
def guard (s : Sheet G) (j : ℕ) :=
  Real.exp (Real.exp (eventually_atTop.mp (stock_c s id j)).choose)

def prices : FundedCompanySelection.Prediction G := fun {M} {_} {A} _ =>
  guard M.p ≤ A.delay.betaEntry

theorem buy : FundedPredictionSupply.AllPrices (@prices G) := by
  intro s q targets expenses charts programs wages baton valid
  refine ⟨0, ?_⟩
  intro l hl D w U reg post scouts θ stages cost V quarter
  let T : Delays θ := { V with betaEntry := guard (ThroughLaunch.raise s l) ⊔ V.betaEntry }
  refine ⟨T, ⟨le_sup_right, le_rfl, le_rfl, le_rfl⟩, ?_⟩
  intro W hW bar wait paid B0
  dsimp only
  intros
  exact le_sup_left.trans hW.beta

/-- Simultaneously buy the native cover marked operator, real vacuum
corrections and the caller's original independent prediction. -/
theorem original (hG : G.Simple) {δ : ℝ} (hδ : 0 < δ) (v : ℕ → Gear G → ℝ)
    (P : FundedCompanySelection.Prediction G) (hP : FundedPredictionSupply.AllPrices (@P)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      FundedMarkedCoverRows.prices v R.kit ∧ prices R.kit ∧ P R.kit ∧
        NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG δ W := by
  obtain ⟨R, T, W, hcov, hother, hc, hW⟩ := FundedMarkedCoverRows.original.{u} hG hδ v
    (@FundedPredictionSupply.Both G (@prices G) (@P))
    (fun s q => FundedPredictionSupply.both (buy s q) (hP s q))
  exact ⟨R, T, W, hcov, hother.1, hother.2, hc, hW⟩

private theorem mint {e : ℕ} (R : Run G) (paid : prices R.kit) (T : Realm G (e+2) Credit.leanC)
    (h : T.draws = R.family.path.levels) (hy : T.y = zz T.draws)
    (v : ∀ i (hi : T.anchor ≤ i), ∃ j : 5 ≤ T.draws.clock.J (i+1),
      (T.mint i hi).σ = crestM T.draws i j ∧ e ≤ T.draws.clock.J (i+1)) : Minted T Credit.leanC := by
  intro m hm
  rw [Credit.lean_cost, hy]
  obtain ⟨j, hj, he⟩ := v m hm
  refine ⟨j, hj, ?_⟩
  let b := T.draws.clock.J (m+1)
  have hβ : R.alloy.delay.betaEntry b ≤ T.draws.clock.hatBeta m := by
    dsimp [b]; rw [h]; exact R.alloy.B.valid.pays _
  have rate := redeemBill (show guard R.metals.p b ≤ Real.exp (Real.exp (zz T.draws m - 1)) from
    ((paid b).trans hβ).trans_eq (scaledBills T.draws m))
  have k : T.draws.clock.kernel = R.metals.p.kernel := by rw [h]; exact R.alloy.B.valid.kernel
  have stage : T.draws.clock.stage = R.metals.p.profile := by rw [h]; exact R.alloy.B.valid.stage
  exact (eventually_atTop.mp (stock_c R.metals.p id b)).choose_spec _ rate T.draws k stage m rfl j e he

/-- The higher vacuum rows, on the real kinetic `PathData` of the funded
Run. The undifferentiated vacuum constant has its own scalar normalization.
All field-dependent ranks and all admitted tori are included. -/
theorem corrections (R : Run G) (hG : G.Simple) (v : ℕ → Gear G → ℝ)
    (hc : FundedMarkedCoverRows.prices v R.kit) (paid : prices R.kit)
    (e : ℕ) : ∃ W : Credit, ∀ᶠ m : ℕ in atTop,
    let A := R.family.path.levels
    ∃ p : 5 ≤ A.clock.J (m+1),
      let s := min (crestM A m p) (A.params m).width
      let u := untilWidth G e s (lt_min (spatter G _ _ _ _ p).1 (A.params m).width_pos)
      0 < u ∧ u⁻¹ ≤ zz A m ∧ ∀ N, m ≤ N →
        let R' := R.alloy.B.kin.path N m
        let B := (A.params m).clip
        let P := actionW A R.metals.O N m
        ∃ X : SeriesA G, (∀ a ∈ X, 3 ≤ a.grade) ∧ fromBefore X (3+e) ∧
          X.length ≤ meterPre (3+e) ∧ Draw X u (W.buy (zz A m) + zz A m * A.clock.loopCap m) ∧
          ∀ i < 3+e, (breast R' B + sandLift X) i = P i ∧
            ∀ n : Side, ∀ r, (front R' B n + sands X n) i (r+1) = lagoon (P i (r+1)) n := by
  let A := R.family.path.levels
  obtain ⟨W,issue⟩ := against_Kin G e Credit.leanC
  refine ⟨W, ?_⟩
  let k : Fin 0 → ℕ := Fin.elim0
  have hq := FundedMarkedCoverRows.realm R hG v hc 0 k k (fun i => Fin.elim0 i) (e+1) 0 0
  filter_upwards [hq, A.fits.deep.eventually_ge_atTop e] with m hm he
  obtain ⟨T, draws, ratio, hy, anchor, _, _, _, named⟩ := hm
  have hy' : T.y = zz T.draws := hy.trans (congrArg zz draws).symm
  have valid := mint R paid T draws hy' (fun j hj => by
    obtain ⟨z, hz, _⟩ := named j (anchor ▸ hj) hj
    have h' : 5 ≤ T.draws.clock.J (j+1) := by rw [draws]; exact z
    refine ⟨h', ?_, ?_⟩
    · simpa only [draws] using hz
    · rw [draws]; exact he.trans (A.fits.mono (by omega)))
  have transfer : ∀ (U : Levels G) (O : ChartRatio G), U = T.draws → O = T.paid →
      ∀ (H : Horizon U) (K : Kin H O) {s : Sheet G} {l : Rolls s} (C : PostCost l), K.Planned C →
      ∃ p : 5 ≤ U.clock.J (m+1),
        let s := min (crestM U m p) (U.params m).width
        let u := untilWidth G e s (lt_min (spatter G _ _ _ _ p).1 (U.params m).width_pos)
        0 < u ∧ u⁻¹ ≤ zz U m ∧ ∀ N, m ≤ N →
        ∃ X : SeriesA G, (∀ a ∈ X, 3 ≤ a.grade) ∧ fromBefore X (3+e) ∧ X.length ≤ meterPre (3+e) ∧
          Draw X u (W.buy (zz U m) + zz U m*U.clock.loopCap m) ∧
          ∀ i<3+e, (breast (K.path N m) (U.params m).clip + sandLift X) i = actionW U O N m i ∧
            ∀ n : Side, ∀ r, (front (K.path N m) (U.params m).clip n+sands X n) i (r+1) =
              lagoon (actionW U O N m i (r+1)) n := by
    rintro _ _ rfl rfl H K s l C hK
    have result := issue T valid H K C hK m anchor.le
    simpa only [Credit.lean_cost, hy', Epic] using result
  exact transfer A R.metals.O draws.symm ratio.symm R.alloy.B.M R.alloy.B.kin R.alloy.post R.alloy.B.support

/-- Preserve an independently specified certified fine source through any
admitted original forest. The source and its coefficient space remain the
same across the change. This applies before evaluation by any marked test. -/
theorem forests {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (R : Run G) (hG : G.Simple) (N m : ℕ) (hm : m < N) (n : Side)
    (T : Forest (mStep R.family.path.levels n m).ratio) :
    let A := R.family.path.levels
    let S := mStep A n m
    let Q := roam A N m n
    let H := freeForms A N (m+1)
    let P := (story A R.metals.O N (m+1)).1 (n*(loose A m).L)
    ∀ (k : ℕ) (X : Parcelized V G (n*(loose A m).L)), shellK k X → (∀ i, Pure (X i)) → Cert X →
      reed S (repeatF S) H Q R.metals.O P k X = reed S T H Q R.metals.O P k X :=
  (Fk.allForests (V:=V) hG R.alloy.B.ratio hm n T).2.2.2.2.2.2

end YM.Integration.FundedOriginalVacuumPaths
end
