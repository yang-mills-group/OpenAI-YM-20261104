import YM.Integration.FundedMarkedCoverRows
import YM.Integration.RootedPeriodicMarkedWinding
import YM.Integration.OriginalPeriodWindingPrice

/-! The purchased strong winding invoice on the very same finite physical period.
The source family is stated before the block with separate independent named sites.
The comparison is a joint measure with its total variation summed over all
relative displacements and field coordinates, including any fixed Laurent loss. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedMarkedWindingWindow
open Function Filter Lattice Wilson RG Laurent Next.Foundations Precision
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Winding
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Address
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider ActualRunAdmissionScales
open scoped Classical Topology BigOperators

variable {G : Gauge}

private lemma monitor_le (A : Levels G) (m : ℕ) : A.clock.monitor m ≤ admittedCost A m := by
  apply le_trans _ (cost_covers_geometry A m)
  have hp := (A.params m).paths_pos
  have hp' := (A.params (m+1)).paths_pos
  have hc := (A.params m).columns_ge
  have hc' := (A.params (m+1)).columns_ge
  have hr := (A.params m).clip.radius_pos
  have hr' := (A.params (m+1)).clip.radius_pos
  have hm : 0 < A.clock.monitor m := Real.exp_pos _
  have hm' : 0 < A.clock.monitor (m+1) := Real.exp_pos _
  have hl := Real.rpow_nonneg hm.le (A.clock.theta (A.clock.J m))
  have hl' := Real.rpow_nonneg hm'.le (A.clock.theta (A.clock.J (m+1)))
  unfold geometryCost Calendar.loopCap
  linarith [Nat.cast_nonneg (α := ℝ) (A.clock.coverSize m), Nat.cast_nonneg (α := ℝ) (A.clock.coverSize (m+1))]

/-- The physical double log and each fixed credit are covered by explicit
powers of the native admission cost. This uses the actual monitor term. -/
theorem credit (A : Levels G) (hG : G.Simple) (T : Credit) : ∀ᶠ m : ℕ in atTop,
    1 ≤ zz A m ∧ zz A m ≤ admittedCost A m ∧ T.buy (zz A m) ≤ (admittedCost A m)^(T.d+1) := by
  have zlim : Tendsto (zz A) atTop atTop := tendsto_atTop_add_const_left _ _
    (Real.tendsto_log_atTop.comp (Multi.Wage.log_tend hG A))
  filter_upwards [zlim.eventually_ge_atTop (max 2 T.x)] with m hm
  have ha : 2 ≤ zz A m := (le_max_left ..).trans hm
  have hx : T.x ≤ zz A m := (le_max_right ..).trans hm
  have hz := (show 1 ≤ (2:ℝ) by norm_num).trans ha
  have hmon : zz A m ≤ A.clock.monitor m := by
    change _ ≤ Real.exp ((Real.log (Real.log (A.clock.hatBeta m)))^2)
    rw [show Real.log (Real.log (A.clock.hatBeta m)) = zz A m - 1 by simp [zz]]
    exact (by nlinarith only [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hz)] :
      zz A m ≤ (zz A m-1)^2+1).trans (Real.add_one_le_exp _)
  have hzC := hmon.trans (monitor_le A m)
  refine ⟨hz, hzC, ?_⟩
  rw [Credit.buy, pow_succ, mul_comm]
  exact mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans hz) hzC _) (hx.trans hzC)
    (zero_le_one.trans T.good) (pow_nonneg (zero_le_one.trans (admittedCost_one A m)) _)

private def room : Credit := ⟨1,128,by norm_num⟩

private def quote {α : Type} [Fintype α] (r : ℕ) (s c : Gear G → ℝ) (I : Gear G) : ℝ :=
  max (c I) (priceM α r (s I) + tiePay α r (s I/4) + 2)

/-- The purchased current on one chosen stage and all of its admitted tori.
The same realm purchases both the strong addressed integral and the finite
thin curvature path reconstruction. -/
def Window {nmarks : ℕ} (R : Run G) (J Z : Finset (Fin nmarks)) (o : Fin nmarks)
    (D k : Fin nmarks → ℕ) (e i r d c q : ℕ) (w s : Gear G → ℝ) (m : ℕ) : Prop :=
  ∃ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
        Q.draws = R.family.path.levels ∧ Q.paid = R.metals.O ∧ Q.y = zz R.family.path.levels ∧
        Cloze D k Q Credit.leanC ∧ Insure J.card (mass k J) Q Credit.leanC ∧
        ∀ N p : ℕ, m < N → let n := R.family.side m p
        let g := Pert.Asymptotics.regulatorRun R.family N p (m+1)
        let I := (Q.mint m hm).gear
        ∀ (K : ((Fin nmarks) → Cover) → family G D)
          (b : ((Fin nmarks) → Cover) → (Fin nmarks) → Site (loose Q.draws m).L) (A : ℝ), 0 ≤ A →
          (∀ x, Eu k (K x) ∧ (K x) ∅ = 0 ∧ safeB (chartIn (loose Q.draws m) x (b x)) (K x) Z e (w I) A) →
          let x := fun z => PeriodicMarkedWinding.roots n z o
          let F := fun z => ((logO Q.draws Q.paid m N (K (x z)) k J).2 i r)
          let P := fun z => coilH Q.draws Q.paid m N n (K (x z)) k (ratioHigh Q.draws Q.paid N m) J i r
          ∃ B : ℝ, B * g^(-(c : ℝ)) ≤ g^q*A^J.card ∧
            PostMark J o r (RootedPeriodicMarkedWinding.row n J o (fun z => Carp.plume (F z) n-P z))
              (s I/32/2/2/2) B d

/-- Original marked winding on one already named realm and its actual time-`m` gear. -/
def ReceiptOn {V : Type} [Fintype V] [DecidableEq V] (R : Run G) (J Z : Finset V) (o : V)
    (D k : V → ℕ) (e i r d c q degree : ℕ) (w s : Gear G → ℝ) (m : ℕ)
    (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) : Prop :=
        ∀ N p : ℕ, m < N → let n := R.family.side m p
        let g := Pert.Asymptotics.regulatorRun R.family N p (m+1)
        let I := (Q.mint m hm).gear
        ∀ (K : (V → Cover) → family G D)
          (b : (V → Cover) → V → Site (loose Q.draws m).L) (A : ℝ), 0 ≤ A →
          (∀ x, Eu k (K x) ∧ (K x) ∅ = 0 ∧ safeB (chartIn (loose Q.draws m) x (b x)) (K x) Z e (w I) A) →
          let x := fun z => PeriodicMarkedWinding.roots n z o
          let F := fun z => ((logO Q.draws Q.paid m N (K (x z)) k J).2 i r)
          let P := fun z => coilH Q.draws Q.paid m N n (K (x z)) k (ratioHigh Q.draws Q.paid N m) J i r
          ∃ B : ℝ, B * g^(-(c : ℝ)) ≤ g^q*A^J.card ∧
            B ≤ (admittedCost R.family.path.levels m)^degree *
              (Real.exp (-(s I/512)*(n.val:ℝ))*A^J.card) ∧
            PostMark J o r (RootedPeriodicMarkedWinding.row n J o (fun z => Carp.plume (F z) n-P z))
              (s I/32/2/2/2) B d

/-- A receipt issued on the active stencil also handles any larger input
stencil. The estimate itself continues to measure only the named active roots. -/
theorem ReceiptOn.enlarge {V : Type} [Fintype V] [DecidableEq V] {R : Run G}
    {J Z Z' : Finset V} {o : V} {D k : V→ℕ} {e i r d c q a m : ℕ} {w s : Gear G→ℝ}
    {Q : Realm G (e+1) Credit.leanC} {hm : Q.anchor ≤ m}
    (receipt : ReceiptOn R J Z o D k e i r d c q a w s m Q hm) (hZZ' : Z⊆Z') :
    ReceiptOn R J Z' o D k e i r d c q a w s m Q hm := by
  intro N p hN n g I K b A hA pre
  apply receipt N p hN K b A hA
  intro x
  refine ⟨(pre x).1,(pre x).2.1,?_⟩
  exact fun Y hY j hj l => (pre x).2.2 Y (hY.trans hZZ') j hj l

/-- Preserve the stage credit and exponential period price as well as the flat error on the same signed measurement. -/
def Receipt {nmarks : ℕ} (R : Run G) (J Z : Finset (Fin nmarks)) (o : Fin nmarks)
    (D k : Fin nmarks → ℕ) (e i r d c q degree : ℕ) (w s : Gear G → ℝ) (m : ℕ) : Prop :=
  ∃ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
        Q.draws = R.family.path.levels ∧ Q.paid = R.metals.O ∧ Q.y = zz R.family.path.levels ∧
        Cloze D k Q Credit.leanC ∧ Insure J.card (mass k J) Q Credit.leanC ∧
        ReceiptOn R J Z o D k e i r d c q degree w s m Q hm

/-- The rooted current over a completely fixed named source. This identity is
prior to any external test and includes all signs, all displacements and all
undivided address derivatives in the native `PostMark` representation.
The original Gazette tariff is quoted before the run. Every stage whose actual
lean account covers that quote can spend it, alongside any other finite buyer. -/
theorem pricedOnWithRate {V : Type} [Fintype V] [DecidableEq V] {J Z : Finset V} (hj : J ⊆ Z)
    (o : V) (ho : o ∈ J) (D k : V → ℕ)
    (e i r : ℕ) (hi : i ≤ e) (w : Gear G → ℝ) (hw : ∀ I, 0 < w I) (d : ℕ) :
    ∃ (v : ℕ → Gear G → ℝ) (s : Gear G → ℝ) (degree : ℕ), (∀ I, 0 < s I) ∧
      (∀ j I,(s I)⁻¹≤v j I) ∧
      WilsonLimitConstruction.FundedPredictionSupply.AllPrices (@FundedMarkedCoverRows.prices G v) ∧
      ∀ (R : Run G) (_ : G.Simple), RG05Preconstruction.ReadoutPurchase R.b → ∀ c q : ℕ,
      ∀ᶠ m : ℕ in atTop, ∀ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
        Q.y = zz R.family.path.levels →
        v (R.family.path.levels.clock.J (m+1)) (Q.mint m hm).gear ≤ Q.cash Credit.leanC m →
        ReceiptOn R J Z o D k e i r d c q degree w s m Q hm := by
  obtain ⟨s, c₀, U, hs, take⟩ := pledges G e i r hi Credit.leanC Credit.leanC w hw hj D k
  let v : ℕ → Gear G → ℝ := fun _ => quote (α := Hooks G) r s c₀
  let T := riding (Hooks G) r d J o room
  let a := 1+(U.d+1)+(T.d+1)
  refine ⟨v,s,a,fun I => (hs I).1,fun _ I => (hs I).2.trans (le_max_left _ _),
    FundedMarkedCoverRows.purchase v,?_⟩
  intro R hG paid c q
  filter_upwards [credit R.family.path.levels hG U, credit R.family.path.levels hG T,
    OriginalPeriodWindingPrice.onRun R hG paid a c q] with m hU hT hflat
  intro Q hm hy hI
  let I := (Q.mint m hm).gear
  let y := zz R.family.path.levels m
  let C := admittedCost R.family.path.levels m
  have hprice : max (c₀ I) (priceM (Hooks G) r (s I) + tiePay (Hooks G) r (s I/4) + 2) ≤ y := by
    simpa only [v,quote,Realm.cash,hy,Credit.leanC,Credit.buy,one_mul,pow_one] using hI
  have hp := (le_max_right ..).trans hprice
  have hcy := (le_max_left ..).trans hprice
  have rate := (hs I).1
  have hsy := (hs I).2.trans hcy
  have hroom : (s I/32/2/2)⁻¹ ≤ room.buy y := by
    change _ ≤ 128*y^1
    rw [pow_one,show (s I/32/2/2)⁻¹ = 128*(s I)⁻¹ by field_simp [rate.ne']; ring]
    exact mul_le_mul_of_nonneg_left hsy (by norm_num)
  intro N p hN n g _ K b A hA pre x F P
  have cbudget : c₀ I ≤ Q.cash Credit.leanC m := by
    simpa only [Realm.cash,hy,Credit.leanC,Credit.buy,one_mul,pow_one] using hcy
  let M := Q.cash U m*A^J.card
  let f := priceM (Hooks G) r (s I) + tiePay (Hooks G) r (s I/4) + 1
  let B := ((f*M+M)*catchW (s I/32/16) n)*T.buy y
  have hMark (z) : MarkU (x z) J (P z) (F z) (s I) M :=
    take Q m N n hm hN cbudget (K (x z)) (pre _).1 (pre _).2.1 (x z) (b _) A hA (pre _).2.2
  have hcash : Q.cash U m = U.buy y := by rw [Realm.cash,hy]
  have hflat' := hflat N p hN (s I) rate (hsy.trans hU.2.1)
  have hbase : (f+1) * U.buy y * T.buy y ≤ C^a := by
    have hU0 := (zero_le_one.trans (U.purchase hU.1))
    have hT0 := (zero_le_one.trans (T.purchase hT.1))
    have hC0 := (zero_le_one.trans (admittedCost_one R.family.path.levels m))
    rw [show C^a = (C*C^(U.d+1))*C^(T.d+1) by simp [a,pow_add]]
    refine mul_le_mul (mul_le_mul (le_trans ?_ (hp.trans hU.2.1)) hU.2.2 hU0 hC0) hT.2.2 hT0 (by positivity)
    dsimp [f]; linarith
  have exponential : B ≤ C^a*(Real.exp (-(s I/512)*(n.val:ℝ))*A^J.card) := by
    calc
      _ = ((f+1)*U.buy y*T.buy y)*(Real.exp (-(s I/512)*(n.val:ℝ))*A^J.card) := by
        dsimp [B,M,catchW]; rw [hcash,show s I/32/16=s I/512 by ring]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbase (by positivity)
  refine ⟨B,?_,exponential,RootedPeriodicMarkedWinding.measured ho rate F P hMark room hroom hU.1 d⟩
  have ht : B*g^(-(c : ℝ)) = ((f+1)*U.buy y*T.buy y)*
      (g^(-(c : ℝ))*Real.exp (-(s I/512)*(n.val : ℝ))*A^J.card) := by
    dsimp [B,M,catchW]; rw [hcash,show s I/32/16=s I/512 by ring]; ring
  rw [ht]
  have hgn : 0 ≤ g := (IterationFour.Currency.g_pos R.makes N p (m+1) (by omega)).le
  have htail := Real.rpow_nonneg hgn (-(c : ℝ))
  calc
    _ ≤ C^a*(g^(-(c : ℝ))*Real.exp (-(s I/512)*(n.val : ℝ))*A^J.card) :=
      mul_le_mul_of_nonneg_right hbase (by positivity)
    _ = (C^a*g^(-(c : ℝ))*Real.exp (-(s I/512)*(n.val : ℝ)))*A^J.card := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hflat' (pow_nonneg hA _)

theorem pricedOn {V : Type} [Fintype V] [DecidableEq V] {J Z : Finset V} (hj : J ⊆ Z)
    (o : V) (ho : o ∈ J) (D k : V → ℕ)
    (e i r : ℕ) (hi : i ≤ e) (w : Gear G → ℝ) (hw : ∀ I, 0 < w I) (d : ℕ) :
    ∃ (v : ℕ → Gear G → ℝ) (s : Gear G → ℝ) (degree : ℕ), (∀ I, 0 < s I) ∧
      WilsonLimitConstruction.FundedPredictionSupply.AllPrices (@FundedMarkedCoverRows.prices G v) ∧
      ∀ (R : Run G) (_ : G.Simple), RG05Preconstruction.ReadoutPurchase R.b → ∀ c q : ℕ,
      ∀ᶠ m : ℕ in atTop, ∀ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
        Q.y = zz R.family.path.levels →
        v (R.family.path.levels.clock.J (m+1)) (Q.mint m hm).gear ≤ Q.cash Credit.leanC m →
        ReceiptOn R J Z o D k e i r d c q degree w s m Q hm := by
  obtain ⟨v,s,a,hs,_,bought,flow⟩ := pricedOnWithRate hj o ho D k e i r hi w hw d
  exact ⟨v,s,a,hs,bought,flow⟩

theorem priced {nmarks : ℕ} {J Z : Finset (Fin nmarks)} (hj : J ⊆ Z)
    (o : Fin nmarks) (ho : o ∈ J) (D k : Fin nmarks → ℕ) (hk : ∀ i, k i < D i)
    (e i r : ℕ) (hi : i ≤ e) (w : Gear G → ℝ) (hw : ∀ I, 0 < w I) (d : ℕ) :
    ∃ (v : ℕ → Gear G → ℝ) (s : Gear G → ℝ) (degree : ℕ), (∀ I, 0 < s I) ∧
      WilsonLimitConstruction.FundedPredictionSupply.AllPrices (@FundedMarkedCoverRows.prices G v) ∧
      ∀ (R : Run G) (_ : G.Simple) (donor : ℕ → Gear G → ℝ),
      FundedMarkedCoverRows.prices donor R.kit →
      (∀ᶠ m : ℕ in atTop, ∀ I, v (R.family.path.levels.clock.J (m+1)) I ≤
        donor (R.family.path.levels.clock.J (m+1)) I) →
      RG05Preconstruction.ReadoutPurchase R.b → ∀ c q : ℕ,
      ∀ᶠ m : ℕ in atTop, Receipt R J Z o D k e i r d c q degree w s m := by
  obtain ⟨v,s,a,hs,presale,spend⟩ := pricedOn hj o ho D k e i r hi w hw d
  refine ⟨v,s,a,hs,presale,?_⟩
  intro R hG donor hv dominates paid c q
  filter_upwards [FundedMarkedCoverRows.realm R hG donor hv _ k D hk e J.card (mass k J),
    dominates,spend R hG paid c q] with m hrealm hdom invoice
  obtain ⟨Q,hQ,hO,hy,hanchor,closed,tickets,_,reserve⟩ := hrealm
  have hm : Q.anchor ≤ m := hanchor.le
  obtain ⟨_,_,hI⟩ := reserve m le_rfl hm
  exact ⟨Q,hm,hQ,hO,hy,closed,tickets,invoice Q hm hy ((hdom _).trans hI)⟩


theorem issue {nmarks : ℕ} {J Z : Finset (Fin nmarks)} (hj : J ⊆ Z)
    (o : Fin nmarks) (ho : o ∈ J) (D k : Fin nmarks → ℕ) (hk : ∀ i, k i < D i)
    (e i r : ℕ) (hi : i ≤ e) (w : Gear G → ℝ) (hw : ∀ I, 0 < w I) (d : ℕ) :
    ∃ (v : ℕ → Gear G → ℝ) (s : Gear G → ℝ), (∀ I, 0 < s I) ∧
      WilsonLimitConstruction.FundedPredictionSupply.AllPrices (@FundedMarkedCoverRows.prices G v) ∧
      ∀ (R : Run G) (_ : G.Simple) (donor : ℕ → Gear G → ℝ),
      FundedMarkedCoverRows.prices donor R.kit →
      (∀ᶠ m : ℕ in atTop, ∀ I, v (R.family.path.levels.clock.J (m+1)) I ≤
        donor (R.family.path.levels.clock.J (m+1)) I) →
      RG05Preconstruction.ReadoutPurchase R.b → ∀ c q : ℕ,
      ∀ᶠ m : ℕ in atTop, Window R J Z o D k e i r d c q w s m := by
  obtain ⟨v,s,a,hs,all,presale⟩ := priced hj o ho D k hk e i r hi w hw d
  refine ⟨v,s,hs,all,?_⟩
  intro R hG donor paid dom readout c q
  filter_upwards [presale R hG donor paid dom readout c q] with m funded
  obtain ⟨Q,hm,draws,chart,hy,closed,tickets,stock⟩ := funded
  refine ⟨Q,hm,draws,chart,hy,closed,tickets,?_⟩
  intro N p hN n g I K b A hA pre x F P
  obtain ⟨B,hB,_,roots⟩ := stock N p hN K b A hA pre
  exact ⟨B,hB,roots⟩

end YM.Integration.FundedMarkedWindingWindow
end
