import YM.Integration.FundedMarkedWindingWindow
import YM.WilsonCoeffUV.Winding.Moment

/-! The unmarked reduction has a held field link in each row. Its primitive
is the signed vacuum ground. The positive-action finite tensor and its bulk
periodization change sign together when read as log Boltzmann weights. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.RootedVacuumWinding
open Function Filter Lattice RG Wilson Precision Laurent Bloch Next.Foundations WilsonCoeffUV.Bank.Ticket
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Blue ActualRunAdmissionScales
open scoped Classical Topology BigOperators

variable {G : Gauge} {n : Side} {r : ℕ} {α V : Type}

/-- Hold one exact field bond and its complete internal facet/colour index,
then sum every other field index on the actual finite torus. -/
def held [Fintype α] [DecidableEq α] [NormedAddCommGroup V]
    (slot : Fin (r+1)) (root : Co n α) (s : ℝ) (P : Ten V (Co n α) (r+1)) : ℝ :=
  ∑ x : dock (Site n) α (r+1), if x slot = root then
    Real.exp (s*soar (tor n) x)*‖P x‖ else 0

theorem held_bound [Fintype α] [DecidableEq α] [NormedAddCommGroup V]
    {s B : ℝ} {P : Ten V (Co n α) (r+1)} (h : Amber (tor n) s B P) (hs : 0 < s)
    (slot : Fin (r+1)) (root : Co n α) :
    held slot root (s/2) P ≤ B*(boardPay α ((s/2)/(r+1:ℕ)))^(r+1) := by
  let t := (s/2)/(r+1:ℕ)
  have ht : 0 < t := by dsimp [t]; positivity
  have item (x : dock (Site n) α (r+1)) :
      (if x slot = root then Real.exp ((s/2)*soar (tor n) x)*‖P x‖ else 0) ≤
      B * sail t (tor n) root.1 x := by
    by_cases key : x slot = root
    · rw [if_pos key]
      have legs (j : Fin (r+1)) : (tor n).gap root.1 (x j).1 ≤ soar (tor n) x := by
        rw [← key]
        exact leg_le (tor n) (Prod.fst ∘ x) slot j
      have pay : Real.exp (-(s/2)*soar (tor n) x) ≤ sail t (tor n) root.1 x := by
        simpa only [sub_zero, Nat.cast_zero, mul_zero, neg_zero, Real.exp_zero, one_mul, t] using
          sail_cut (d := tor n) (σ := s/2) (η := 0) (v := 0) (l := soar (tor n) x)
            (Nat.zero_le _) le_rfl (by positivity) (by omega) root.1 x legs
      calc
        _ ≤ Real.exp ((s/2)*soar (tor n) x)*(B*Real.exp (-s*soar (tor n) x)) :=
          mul_le_mul_of_nonneg_left (h.2 x) (Real.exp_pos _).le
        _ = B*Real.exp (-(s/2)*soar (tor n) x) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left pay h.1
    · rw [if_neg key]
      exact mul_nonneg h.1 (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
  calc
    _ ≤ ∑ x : dock (Site n) α (r+1), B*sail t (tor n) root.1 x :=
      Finset.sum_le_sum fun x _ => item x
    _ = B*(∑ x : dock (Site n) α (r+1), sail t (tor n) root.1 x) := (Finset.mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (train_native (α := α) ht root.1 (r+1)) h.1

/-- A density-matrix coefficient row of the actual periodic vacuum compared
with the native periodized cover action. `r = 1` is the full Hessian and
`slot` can be either of its two physical links. The sign below is the
finite log Boltzmann ground minus the likewise signed periodized ground. -/
abbrev ground (A : Levels G) (O : ChartRatio G) (N m : ℕ) (n : Side) (i r : ℕ) :=
    lagoon (freshet A O N m i (r+1)) n - coil0 A O m N n i (r+1)

private def coefficient (r : ℕ) (s : ℝ) (G : Gauge) :=
  (hinges s r+2) * (boardPay (Hooks G) ((perchA s r/2/2)/(r+1:ℕ)))^(r+1)

/-- The signed cost of a positive-rank quiet row on the actual admitted
period, with any chosen physical link/facet/colour held. -/
def Window (R : Run G) (e i r c q : ℕ) (width : Gear G → ℝ) (m : ℕ) : Prop :=
  ∃ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
        Q.draws = R.family.path.levels ∧ Q.paid = R.metals.O ∧
        ∀ N p : ℕ, m < N → let n := R.family.side m p
          let g := Pert.Asymptotics.regulatorRun R.family N p (m+1)
          ∃ B : ℝ, B * g^(-(c:ℝ)) ≤ g^q ∧ ∀ (slot : Fin (r+1)) (root : Co n (Hooks G)),
            held slot root (width (Q.mint m hm).gear)
              (ground R.family.path.levels R.metals.O N m n i r) ≤ B

/-- On the named issued realm the positive vacuum tensor is the negative
of the original signed log-density ground. Every external field root is retained. -/
def ReceiptOn (R : Run G) (e i r c q degree : ℕ) (width : Gear G → ℝ) (m : ℕ)
    (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) : Prop :=
  ∀ N p : ℕ, m < N → let n := R.family.side m p
          let g := Pert.Asymptotics.regulatorRun R.family N p (m+1)
          ∃ B : ℝ, B * g^(-(c:ℝ)) ≤ g^q ∧
            B ≤ (admittedCost R.family.path.levels m)^degree *
              Real.exp (-(width (Q.mint m hm).gear/4)*(n.val:ℝ)) ∧ ∀ (slot : Fin (r+1)) (root : Co n (Hooks G)),
            held slot root (width (Q.mint m hm).gear)
              (ground R.family.path.levels R.metals.O N m n i r) ≤ B

def Receipt (R : Run G) (e i r c q degree : ℕ) (width : Gear G → ℝ) (m : ℕ) : Prop :=
  ∃ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
        Q.draws = R.family.path.levels ∧ Q.paid = R.metals.O ∧
        ReceiptOn R e i r c q degree width m Q hm

/-- Every adequately endowed original realm pays the true signed vacuum
winding at its own gear, including rank two. The quote precedes the choice of R. -/
theorem pricedOnWithRate (e i r : ℕ) (hi : i ≤ e) (w : Gear G → ℝ) (hw : ∀ I, 0 < w I) :
    ∃ (v : ℕ → Gear G → ℝ) (width : Gear G → ℝ) (degree : ℕ), (∀ I, 0 < width I) ∧
      (∀ j I,(width I)⁻¹≤v j I) ∧
      ∀ (R : Run G) (_hG : G.Simple), RG05Preconstruction.ReadoutPurchase R.b → ∀ c q : ℕ,
      ∀ᶠ m : ℕ in atTop, ∀ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
        Q.draws = R.family.path.levels → Q.paid = R.metals.O → Q.y = zz R.family.path.levels →
        v (R.family.path.levels.clock.J (m+1)) (Q.mint m hm).gear ≤ Q.cash Credit.leanC m →
        ReceiptOn R e i r c q degree width m Q hm := by
  obtain ⟨s,c₀,U,hs,take⟩ := purchaseW G e i (r+1) hi Credit.leanC Credit.leanC w hw
  let t (I : Gear G) := perchA (s I) r
  let base (I : Gear G) := max (c₀ I) (max (t I)⁻¹ (coefficient r (s I) G))
  let v : ℕ → Gear G → ℝ := fun _ I => max (base I) ((t I/2/2)⁻¹)
  have ht I : 0 < t I := perch_pos (hs I).1 r
  refine ⟨v,fun I => t I/2/2,(U.d+1)+1,fun I => by dsimp; positivity [ht I],
    fun _ I => le_max_right (base I) _,?_⟩
  intro R hG readout c q
  let A := R.family.path.levels
  let a := (U.d+1)+1
  filter_upwards [FundedMarkedWindingWindow.credit A hG U,
    OriginalPeriodWindingPrice.onRun R hG readout a c q] with m credit flat
  intro Q hm draws chart hy hI
  let I := (Q.mint m hm).gear
  let y := zz A m
  let C := admittedCost A m
  have original : base I ≤ Q.cash Credit.leanC m := (le_max_left _ _).trans hI
  have res : max (c₀ I) (max (t I)⁻¹ (coefficient r (s I) G)) ≤ y := by
    simpa only [base,Realm.cash,hy,Credit.leanC,Credit.buy,one_mul,pow_one] using original
  have hc : c₀ I ≤ Q.cash Credit.leanC m := by
    exact (le_max_left ..).trans original
  have inverse := (le_max_left ..).trans ((le_max_right ..).trans res)
  have coeff := (le_max_right ..).trans ((le_max_right ..).trans res)
  have hC : 0 ≤ C := zero_le_one.trans (admittedCost_one A m)
  have hcash : Q.cash U m = U.buy y := by rw [Realm.cash,hy]
  have hgeom : 0 ≤ coefficient r (s I) G := mul_nonneg
    (by linarith [(hinge_reserve (hs I).1 r).le]) (pow_nonneg (boardPay_nn (by positivity [ht I])) _)
  have geom : U.buy y * coefficient r (s I) G ≤ C^a := by
    rw [show C^a = C^(U.d+1)*C from pow_succ ..]
    exact mul_le_mul credit.2.2 (coeff.trans credit.2.1) hgeom (pow_nonneg hC _)
  intro N p hN n g
  have sight := take Q m N n hm hN hc
  have walk := ((perch Q.draws Q.paid Q.hG Q.green hN).growth i (r+1)).road
  have tensor := costOrbit sight (hs I).1 walk
  let B := (U.buy y * coefficient r (s I) G) * catchW (t I/16) n
  refine ⟨B,?_,?_,?_⟩
  · have tiny := flat N p hN (t I) (ht I) (inverse.trans credit.2.1)
    have hgn : 0 ≤ g := (IterationFour.Currency.g_pos R.makes N p (m+1) (by omega)).le
    have decay := catch_width (show t I/512 ≤ t I/16 by linarith [ht I]) n.val
    calc
      _ = (U.buy y*coefficient r (s I) G) * (g^(-(c:ℝ))*catchW (t I/16) n) := by ring
      _ ≤ C^a * (g^(-(c:ℝ))*catchW (t I/512) n) :=
        mul_le_mul geom (mul_le_mul_of_nonneg_left decay (Real.rpow_nonneg hgn _))
          (mul_nonneg (Real.rpow_nonneg hgn _) (catch_hot ..)) (pow_nonneg hC _)
      _ = (C^a*g^(-(c:ℝ)))*Real.exp (-(t I/512)*(n.val:ℝ)) := by rw [mul_assoc]; rfl
      _ ≤ _ := tiny
  · change B ≤ C^a * Real.exp (-((t I/2/2)/4)*(n.val:ℝ))
    rw [show (t I/2/2)/4=t I/16 by ring]
    exact mul_le_mul_of_nonneg_right geom (Real.exp_nonneg _)
  · intro slot root
    have ordinary := held_bound tensor (by positivity [ht I]) slot root
    change held slot root (t I/2/2) (ground Q.draws Q.paid N m n i r) ≤ _ at ordinary
    have same : ground Q.draws Q.paid N m n i r=ground R.family.path.levels R.metals.O N m n i r := by rw [draws,chart]
    rw [same,hcash] at ordinary
    refine ordinary.trans_eq ?_
    dsimp [windPay,B,coefficient,t]; ring

theorem pricedOn (e i r : ℕ) (hi : i ≤ e) (w : Gear G → ℝ) (hw : ∀ I, 0 < w I) :
    ∃ (v : ℕ → Gear G → ℝ) (width : Gear G → ℝ) (degree : ℕ), (∀ I, 0 < width I) ∧
      ∀ (R : Run G) (_hG : G.Simple), RG05Preconstruction.ReadoutPurchase R.b → ∀ c q : ℕ,
      ∀ᶠ m : ℕ in atTop, ∀ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
        Q.draws = R.family.path.levels → Q.paid = R.metals.O → Q.y = zz R.family.path.levels →
        v (R.family.path.levels.clock.J (m+1)) (Q.mint m hm).gear ≤ Q.cash Credit.leanC m →
        ReceiptOn R e i r c q degree width m Q hm := by
  obtain ⟨v,s,a,hs,_,bought⟩ := pricedOnWithRate e i r hi w hw
  exact ⟨v,s,a,hs,bought⟩

theorem priced (e i r : ℕ) (hi : i ≤ e) (w : Gear G → ℝ) (hw : ∀ I, 0 < w I) :
    ∃ (v : ℕ → Gear G → ℝ) (width : Gear G → ℝ) (degree : ℕ), (∀ I, 0 < width I) ∧
      ∀ (R : Run G) (_hG : G.Simple) (donor : ℕ → Gear G → ℝ),
      FundedMarkedCoverRows.prices donor R.kit →
      (∀ᶠ m : ℕ in atTop, ∀ I, v (R.family.path.levels.clock.J (m+1)) I ≤
        donor (R.family.path.levels.clock.J (m+1)) I) →
      RG05Preconstruction.ReadoutPurchase R.b → ∀ c q : ℕ,
      ∀ᶠ m : ℕ in atTop, Receipt R e i r c q degree width m := by
  obtain ⟨v,width,a,hs,spend⟩ := pricedOn e i r hi w hw
  refine ⟨v,width,a,hs,?_⟩
  intro R hG donor paid dominates readout c q
  let k : Fin 0 → ℕ := Fin.elim0
  filter_upwards [FundedMarkedCoverRows.realm R hG donor paid 0 k k (fun z => Fin.elim0 z) e 0 0,
    dominates,spend R hG readout c q] with m witness hdom invoice
  obtain ⟨Q,draws,chart,hy,anchor,_,_,_,mint⟩ := witness
  have hm : Q.anchor ≤ m := anchor.le
  obtain ⟨_,_,hI⟩ := mint m le_rfl hm
  exact ⟨Q,hm,draws,chart,invoice Q hm draws chart hy ((hdom _).trans hI)⟩


theorem issue (e i r : ℕ) (hi : i ≤ e) (w : Gear G → ℝ) (hw : ∀ I, 0 < w I) :
    ∃ (v : ℕ → Gear G → ℝ) (width : Gear G → ℝ), (∀ I, 0 < width I) ∧
      ∀ (R : Run G) (_hG : G.Simple) (donor : ℕ → Gear G → ℝ),
      FundedMarkedCoverRows.prices donor R.kit →
      (∀ᶠ m : ℕ in atTop, ∀ I, v (R.family.path.levels.clock.J (m+1)) I ≤
        donor (R.family.path.levels.clock.J (m+1)) I) →
      RG05Preconstruction.ReadoutPurchase R.b → ∀ c q : ℕ,
      ∀ᶠ m : ℕ in atTop, Window R e i r c q width m := by
  obtain ⟨v,s,a,hs,presale⟩ := priced e i r hi w hw
  refine ⟨v,s,hs,?_⟩
  intro R hG donor paid dominates readout c q
  filter_upwards [presale R hG donor paid dominates readout c q] with m funded
  obtain ⟨Q,hm,draws,chart,stock⟩ := funded
  refine ⟨Q,hm,draws,chart,?_⟩
  intro N p hN n g
  obtain ⟨B,hB,_,roots⟩ := stock N p hN
  exact ⟨B,hB,roots⟩

end YM.Integration.RootedVacuumWinding
end
