import YM.Integration.OriginalFundedMarkedPackets
import YM.Integration.FundedMarkedCoverRows

/-! Rooted physical marked packets bought on the original finite Run.
The bare invoice and the regulated invoice refer to the identical emitted
coefficients. Negative Laurent powers carry a separate radius charge. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalRunMarkedPacketPurchase
open Function Filter Finset Lattice RG RG.Supply Wilson Marker
open PhysicalNext PhysicalNext.Repeat.Legato Next.Foundations
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Express
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Embroider WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Soil
open ComparisonDensity.Address LocalComparison ActualRunAdmissionScales WilsonLimitConstruction
open FundedMarkedPathSelection OriginalRootedPacketLayout OriginalFundedMarkedPackets
open WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Wheel.Flooring
open scoped BigOperators Classical Topology

variable {G : Gauge} {v : ℕ} (C : Census (Fin v)) (k : Fin v → ℕ) {e m N : ℕ}
variable (O : Fin v → Orbit) (R : Run G)
local notation "D" => NativeMarkedAddressTokens.axes O
local notation "St" => Block C k e

def credit (b : St) :=
  OriginalBareMarkedInvoice.reserve G (D) k b.1.val.val (owner C b.1) e

def majorant (b : St) :=
  NativeMarkedAddressTokens.cellPrice O b.1.val.val *
    (admittedCost R.family.path.levels m)^((credit C k O (G:=G) b).d+1)

private theorem nonnegative (b : St) : 0 ≤ majorant C k O R (m:=m) b :=
  mul_nonneg (by unfold NativeMarkedAddressTokens.cellPrice; positivity)
    (pow_nonneg (zero_le_one.trans (admittedCost_one _ _)) _)

theorem row (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) (A : ℝ) (hA : 0≤A)
    (tickets : Insure v (mass k Finset.univ) Q Credit.leanC)
    (paid : ∀ b : St, Q.cash (credit C k O (G:=G) b) m ≤
      (admittedCost R.family.path.levels m)^((credit C k O (G:=G) b).d+1)) (b : St) :
    expenses C k O Q hm (A:=A) b ≤ majorant C k O R (m:=m) b * A^b.1.val.val.card := by
  have h := OriginalBareMarkedInvoice.common («D» := NativeMarkedAddressTokens.axes O) (k:=k) Q hm (owner_mem C b.1) tickets A hA
  have ht := h.trans (mul_le_mul_of_nonneg_right (paid b) (pow_nonneg hA _))
  unfold expenses majorant
  rw [Fintype.card_fin,mul_assoc]
  have cells : 0 ≤ NativeMarkedAddressTokens.cellPrice O b.1.val.val := by
    unfold NativeMarkedAddressTokens.cellPrice
    positivity
  simpa only [credit,mul_assoc] using mul_le_mul_of_nonneg_left ht cells

theorem cleared (A : ℝ) (hA : 0≤A) (w : Fin v→ℝ) (hw : ∀ i,0≤w i)
    {g : ℝ} (hg : 0<g) (hg1 : g≤1) (radii : ∀ i,w i*A≤g^(k i)) (b : St) :
    Poly.toll w b.1.val * ‖(g:ℂ)^(power C k e b)‖ * A^b.1.val.val.card ≤ 1 := by
  let J := b.1.val.val
  have costs : Poly.toll w b.1.val * A^J.card ≤ g^(mass k J) := by
    have h := Finset.prod_le_prod (s:=J) (f:=fun i => w i*A) (g:=fun i => g^(k i))
      (fun i _ => mul_nonneg (hw i) hA) (fun i _ => radii i)
    simpa only [prod_mul_distrib,prod_const,prod_pow_eq_pow_sum,Poly.toll,mass] using h
  have degree : 0 ≤ (mass k J:ℤ) + power C k e b := by
    have hr := b.2.2.isLt
    dsimp only [power,J]
    omega
  have hgpos : 0 ≤ g^(power C k e b) := (zpow_pos hg _).le
  have norm : ‖(g:ℂ)^(power C k e b)‖=g^(power C k e b) := by
    simp [norm_zpow,Real.norm_eq_abs,abs_of_nonneg hg.le]
  calc
    _ = (Poly.toll w b.1.val*A^J.card)*g^(power C k e b) := by rw [norm]; ring
    _ ≤ g^(mass k J)*g^(power C k e b) := mul_le_mul_of_nonneg_right costs hgpos
    _ = g^((mass k J:ℤ)+power C k e b) := by rw [zpow_add₀ hg.ne',zpow_natCast]
    _ ≤ 1 := zpow_le_one₀ hg hg1 degree

theorem numerical (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) (A : ℝ) (hA : 0≤A)
    (tickets : Insure v (mass k Finset.univ) Q Credit.leanC)
    (paid : ∀ b : St, Q.cash (credit C k O (G:=G) b) m ≤
      (admittedCost R.family.path.levels m)^((credit C k O (G:=G) b).d+1)) :
    ∀ (w : Fin v→ℝ), (∀ i,0≤w i) →
      budget C k O Q hm (A:=A) w 1 ≤
        ∑ b : St,Poly.toll w b.1.val * majorant C k O R (m:=m) b * A^b.1.val.val.card ∧
      ∀ g : ℝ, 0<g → g≤1 → (∀ i,w i*A≤g^(k i)) →
        budget C k O Q hm (A:=A) w g ≤ ∑ b : St,majorant C k O R (m:=m) b := by
  intro w hw
  constructor
  · unfold budget
    simp only [Complex.ofReal_one,one_zpow,norm_one,mul_one]
    apply sum_le_sum
    intro b _
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (row C k O R Q hm A hA tickets paid b)
      (Finset.prod_nonneg (fun i _ => hw i))
  · intro g hg hg1 radii
    unfold budget
    apply sum_le_sum
    intro b _
    have w₀ : 0≤Poly.toll w b.1.val := Finset.prod_nonneg (fun i _ => hw i)
    have h := mul_le_mul_of_nonneg_left (row C k O R Q hm A hA tickets paid b)
      (mul_nonneg w₀ (norm_nonneg ((g:ℂ)^(power C k e b))))
    calc
      _ ≤ _ := h
      _ = (Poly.toll w b.1.val * ‖(g:ℂ)^(power C k e b)‖ * A^b.1.val.val.card) *
          majorant C k O R (m:=m) b := by ring
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (cleared C k A hA w hw hg hg1 radii b) (nonnegative C k O R b)

/-- The original common model's native numerical price and the entire
spatial packet purchase after that original model has issued its licence. -/
def proceeds (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m) : Prop :=
      (∀ b : St, Q.cash (credit C k O (G:=G) b) m ≤
        (admittedCost R.family.path.levels m)^((credit C k O (G:=G) b).d+1)) ∧
      ∀ N : ℕ, m<N → ∀ (A : ℝ) (X : Input Q hm Finset.univ k (D) A), 0≤A →
        ∃ M : RootedMeasures C k O (e:=e) (G:=G),
          rootedSale C k O Q hm X (N:=N) M ∧
          (∀ (n : Side) (p : Fin v→Site n) (Y : Fin v→Dip), (∀ i,(Y i).Fits (O i).field) →
            let P := packets C k p O Y Q hm X (N:=N) (sampled C k p O M)
            ∀ (point : BudgetPoint) (w : Fin v→ℝ) (g s : ℝ), (∀ i,0<w i) →
              0<s → s≤width k Q hm → point.supportExponent / point.B ≤ s / 4 →
              P.Paid point (fun i => {p i}) (OriginalMeasuredSourceRows.region O Y (fun i => {p i}))
                w g s (budget C k O Q hm (A:=A) w g) (offset k (e:=e)) 1) ∧
          ∀ (w : Fin v→ℝ), (∀ i,0≤w i) →
            budget C k O Q hm (A:=A) w 1 ≤
              ∑ b : St,Poly.toll w b.1.val * majorant C k O R (m:=m) b * A^b.1.val.val.card ∧
            ∀ g : ℝ, 0 < g → g ≤ 1 → (∀ i, w i*A ≤ g^(k i)) →
              budget C k O Q hm (A:=A) w g ≤ ∑ b : St, majorant C k O R (m:=m) b

/-- The complete canonical packet sale on an already issued stage. Its common
cash account and rendering and support licences suffice for all later inputs. -/
theorem onRealm (hG : G.Simple) : ∀ᶠ m : ℕ in atTop,
    ∀ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
      Q.y=zz R.family.path.levels → Cloze (D) k Q Credit.leanC →
      Insure v (mass k univ) Q Credit.leanC → proceeds C k O R Q hm := by
  have money := eventually_all.mpr (fun b : St =>
    FundedMarkedWindingWindow.credit R.family.path.levels hG (credit C k O (G:=G) b))
  filter_upwards [money] with m covers
  intro Q hm hy cl insured
  have sale (b : St) : Q.cash (credit C k O (G:=G) b) m ≤
      (admittedCost R.family.path.levels m)^((credit C k O (G:=G) b).d+1) := by
    simpa only [Realm.cash,hy] using (covers b).2.2
  refine ⟨sale,?_⟩
  intro N hN A X hA
  have charged : Insure (Fintype.card (Fin v)) (mass k univ) Q Credit.leanC := by simpa using insured
  obtain ⟨M,raw,all⟩ := issued C k O Q hm X hA hN cl charged
  exact ⟨M,raw,all,numerical C k O R Q hm A hA insured sale⟩

/-- A complete issued selection, including the original operator rendering
licence on the very same realm used to construct the packet coefficients. -/
def issuedStage : Prop :=
  ∃ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
    Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧ Q.anchor=m ∧ Q.y=zz R.family.path.levels ∧
    Cloze (D) k Q Credit.leanC ∧ Insure (Fintype.card (Fin v)) (mass k univ) Q Credit.leanC ∧
    (∀ j,m≤j → ∀ hj : Q.anchor≤j, ∃ z : 5≤R.family.path.levels.clock.J (j+1),
      (Q.mint j hj).σ = crestM R.family.path.levels j z) ∧
    proceeds C k O R Q hm

theorem selected (hG : G.Simple) (income : ℕ→Gear G→ℝ)
    (donor : FundedMarkedCoverRows.prices income R.kit) (hk : ∀ i,k i<(D) i) :
    ∀ᶠ m : ℕ in atTop, issuedStage C k O R (m:=m) (e:=e) := by
  filter_upwards [FundedMarkedCoverRows.realm R hG income donor v k (D) hk e v (mass k univ),
    onRealm C k O R (e:=e) hG] with m witness spend
  obtain ⟨Q,hd,ho,hy,ha,cl,insured,_,pole⟩ := witness
  refine ⟨Q,ha.le,hd,ho,ha,hy,cl,by simpa using insured,?_,spend Q ha.le hy cl insured⟩
  intro j hj hq
  obtain ⟨z,hz,_⟩ := pole j hj hq
  exact ⟨z,hz⟩

/-- Fixed on the donor-selected Run, before the physical cutoff and all
later field and test data. The common root charge is polynomial in the
admitted scale. -/
theorem fromRun (hG : G.Simple) (income : ℕ→Gear G→ℝ)
    (donor : FundedMarkedCoverRows.prices income R.kit) (hk : ∀ i,k i<(D) i) :
    ∀ᶠ m : ℕ in atTop, ∃ (Q : Realm G (e+1) Credit.leanC) (hm : Q.anchor ≤ m),
      Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧ Q.anchor=m ∧
      (∀ b : St, Q.cash (credit C k O (G:=G) b) m ≤
        (admittedCost R.family.path.levels m)^((credit C k O (G:=G) b).d+1)) ∧
      ∀ N : ℕ, m<N → ∀ (A : ℝ) (X : Input Q hm Finset.univ k (D) A), 0≤A →
        ∃ M : RootedMeasures C k O (e:=e) (G:=G),
          rootedSale C k O Q hm X (N:=N) M ∧
          (∀ (n : Side) (p : Fin v→Site n) (Y : Fin v→Dip), (∀ i,(Y i).Fits (O i).field) →
            let P := packets C k p O Y Q hm X (N:=N) (sampled C k p O M)
            ∀ (point : BudgetPoint) (w : Fin v→ℝ) (g s : ℝ), (∀ i,0<w i) →
              0<s → s≤width k Q hm → point.supportExponent / point.B ≤ s / 4 →
              P.Paid point (fun i => {p i}) (OriginalMeasuredSourceRows.region O Y (fun i => {p i}))
                w g s (budget C k O Q hm (A:=A) w g) (offset k (e:=e)) 1) ∧
          ∀ (w : Fin v→ℝ), (∀ i,0≤w i) →
            budget C k O Q hm (A:=A) w 1 ≤
              ∑ b : St,Poly.toll w b.1.val * majorant C k O R (m:=m) b * A^b.1.val.val.card ∧
            ∀ g : ℝ, 0 < g → g ≤ 1 → (∀ i, w i*A ≤ g^(k i)) →
              budget C k O Q hm (A:=A) w g ≤ ∑ b : St, majorant C k O R (m:=m) b := by
  filter_upwards [selected C k O R hG income donor hk (e:=e)] with m data
  obtain ⟨Q,hm,levels,action,anchor,_,_,_,_,w⟩ := data
  exact ⟨Q,hm,levels,action,anchor,w⟩

universe u

/-- Both the native canonical operator and each finite coefficient bank
are produced on the original funded physical campaign. -/
theorem sponsored (hG : G.Simple) {ε : ℝ} (hε : 0<ε) (income : ℕ→Gear G→ℝ)
    (P : FundedCompanySelection.Prediction G) (hP : FundedPredictionSupply.AllPrices (@P)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      FundedMarkedCoverRows.prices income R.kit ∧ P R.kit ∧ NativeFVAPlateau.Correlations R ∧
      FundedOriginalProperties.{u} hG ε W ∧
      ∀ (d e : ℕ) (C : Census (Fin d)) (k : Fin d→ℕ) (O : Fin d→Orbit),
        (∀ i,k i<NativeMarkedAddressTokens.axes O i) →
        ∀ᶠ m : ℕ in atTop, issuedStage C k O R (e:=e) (m:=m) := by
  obtain ⟨R,T,W,paid,other,corr,facts⟩ := FundedMarkedCoverRows.original.{u} hG hε income P hP
  exact ⟨R,T,W,paid,other,corr,facts,fun _ _ C k O hk => selected C k O R hG income paid hk⟩

end YM.Integration.OriginalRunMarkedPacketPurchase
end
