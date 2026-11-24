import YM.Integration.WilsonTrueProjectedLocatedHistory

/-! At a fixed true cutoff the paid numerical source keeps its entire primary
chronology. Its two null accounts and the primary feeds issued at each date
are bounded by a summable wage, uniformly up the chosen digit itinerary. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedFunded
open Filter MeasureTheory Lattice RG Wilson Extra.Histories Source Labels
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open QuadraticLocal QuadraticLocal.Advent AllOrder AllOrder.Floe AllOrder.Transit WheelP WilsonOriginalNullCorridor
open scoped Classical Topology BigOperators

open FormalBulk08 City Pose RemainderComparison ConnectedActivityE6
open WilsonTrueProjectedPointProgram WilsonTrueProjectedPointInverse
open WilsonTrueProjectedLocatedBasis WilsonTrueProjectedLocatedHistory
open WilsonPinnedWidthTransport WilsonTrueProjectedNaturalFee WilsonTrueProjectedCourse
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G)
local notation "C₀" => R.family

def placed (d N p b : ℕ) (o : ∀ j,Site ((C₀).side j p)) (i : ℕ) (x : (C₀).label d) :=
  (calValues (C:=C₀) d N p (b+i) x) ∘ Lattice.translate (o (b+i))

structure Receipt (d N p b n : ℕ) (W : ∀ j,Rep G ((C₀).side j p))
    (o : ∀ j,Site ((C₀).side j p)) (F : ∀ j,Config G ((C₀).side (b+j) p) → ℂ)
    (price : ℕ → ℝ) (ε : ℝ) where
  primary : Fin n → (C₀).label d
  feed : Fin n → ℕ → (C₀).label d
  active : Fin n → store C₀ d p b
  canonical : Fin n → store C₀ d p b
  u : Fin n → ℝ
  e : Fin n → ℝ
  incoming : ∀ j, mCost C₀ d N p (b+j.val) (primary j) ≤ 2*price j.val
  retained : ∀ j,
    (active j).Format (o b) (C₀).params (W b) ∧
    (active j).remBound (o b) (W b) (safety C₀ b) (u j) ∧
    projection ((C₀).labels.level d) (C₀).params (W b).p.threshold (o b) (active j)=0
  measured : ∀ j, let P := (C₀).path.rep N p b
    (canonical j).Format (o b) (C₀).params P ∧ (canonical j).remBound (o b) P (safety C₀ b) (e j) ∧
    projection ((C₀).labels.level d) (C₀).params P.p.threshold (o b) (canonical j)=0
  nullCost : ∀ j, u j+e j ≤ gain C₀ b (b+j.val)*((2+4*stock C₀ (b+j.val))*price j.val)
  feedCost : ∀ j i, i<j.val → mCost C₀ d N p (b+i) (feed j i) ≤
    ε*gain C₀ (b+i) (b+j.val)*((2+4*stock C₀ (b+j.val))*price j.val)
  field : let S := (C₀).localSection d
    flow C₀ d N p b n (F n)=F 0+∑ j : Fin n,
      ((active j).density (o b) S (W b)+(canonical j).density (o b) S ((C₀).path.rep N p b)+
      (∑ i ∈ Finset.range j.val, flow C₀ d N p b i (placed R d N p b o i (feed j i)))+
      flow C₀ d N p b j.val (placed R d N p b o j.val (primary j)))

theorem original {d D : ℕ} (wood : Primer.Families R.family) (a : hue G) (depth : d<D)
    (simple : G.Simple) (loc : Stationary.Loc G 1) {U : ℕ → ℕ}
    (formal : WilsonWindowFormalPurchase.Canonical U R.kit)
    (point : WilsonNeutralPointForecast.Filed R.kit) (weakly : WilsonNeutralPointWeakForecast.Filed R.kit)
    (slow : ∀ i,(((C₀).S.block i).val:ℝ) ≤ Real.log (RG16.Lambda (C₀).path.levels i))
    (Q earned target : ℕ) (head : target+2≤earned+1) {δ ε : ℝ} (hp : 0<δ) (gap : δ<1/8) (ep : 0≤ε) :
    ∃ K : ℝ, ∃ V : ℕ, 0<K ∧ ∀ᶠ b : ℕ in Filter.atTop,
    ∀ m N p k n : ℕ, m≤b → b+n≤N → d≤(C₀).path.levels.clock.J (b+1) →
    ∀ (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (W : ∀ j,Rep G ((C₀).side j p)),
    Concourse R.alloy R.kit R.T π Γ m N p k W →
    ∀ (o : ∀ j,Site ((C₀).side j p)) (digit : ∀ j, Site ((C₀).S.block j)),
    (∀ j<n, o (b+j)=((C₀).path.levels.clock.op (b+j) p).ratio.parent (o (b+j+1))) →
    (∀ j<n, WilsonOriginalNullPlacedParallel.Joined C₀ d N p (b+j) W (o (b+j+1)) ε) →
    (∀ j<n, ((C₀).path.levels.budget (b+j)).supportExponent ≤ 100) →
    let axes := Letter ((C₀).labels.level d)
    ∀ (report : axes → ℂ) (origin fare : ℝ), 0≤origin → 0≤fare → (∀ t,‖report t‖≤origin) →
    ∀ (book : ∀ j, axes → Config G ((C₀).side j p) → ℂ)
      (prices : ℕ → Fin (Q+1) → axes → ℝ) (_anchor : axes),
    let g := fun j => Coat.gStep (((C₀).path.rep N p j).beta)
    let top := take R Q (lift R wood a depth digit N b g (fun l => PowerSeries.C (report l)) (b+n-b))
    let F := fun j => earnedValue R wood a depth digit N (b+n) Q g top W book (b+j)
    let bill := fun j => datedFee R wood a depth digit N (b+n) Q g top (b+j) (prices (b+j))
    let total := K*(RG16.Lambda (C₀).path.levels b)^V*origin*fare*power R target b
    (∀ j, b≤j → j≤b+n → ∀ l,Integrable (fun H=>((W j).eval H:ℂ)*book j l H) (prior G _)) →
    (∀ j, b≤j → j<b+n → ∀ t l, prices j t l ≤ fare*(g j)^(earned+1)) →
    (∀ j, b≤j → j<b+n → ∀ (t : Fin (Q+1)) (l : axes),
      ∃ z : store C₀ d p j, Paid R (W j) (o j) z (prices j t l) ∧
      transition (C:=C₀) d N p j (film (W (j+1)).eval (book (j+1) l) (g j) t.val)=
        film (W j).eval (nextWord R wood a depth digit N j Q (g j) (book j) t l) (g j) t.val+
        z.density (o j) ((C₀).localSection d) (W j)) →
    ∃ H : Receipt R d N p b n W o F bill ε, (∑ j : Fin n,(H.u j+H.e j)) ≤ total ∧
      ∀ i≤n, (∑ j ∈ Finset.range (n-i),gain C₀ (b+i) (b+i+j)*
        ((2+4*stock C₀ (b+i+j))*bill (i+j))) ≤ total*Real.exp (δ*elapsed (C₀).S b (b+i)) := by
  classical
  obtain ⟨K,V,hK,salary⟩ := WilsonTrueProjectedLocatedSalary.original R wood a depth simple loc formal
    point weakly slow Q earned target head hp gap
  refine ⟨K,V,hK,?_⟩
  filter_upwards [salary,WilsonTrueProjectedLocatedWord.original R d simple ep] with b quotes words
  intro m N p k n mb bn enrolled π Γ W course o digit route gates roof axes report origin fare ho hf originPaid book prices anchor g top F bill total intakePaid pricesPaid localPaid
  have rate (j : ℕ) (hj : j≤N) : 0<g j := inv_pos.mpr (Real.sqrt_pos.mpr
    ((half_pos (zero_lt_one.trans ((R.family).path.levels.fits.delayed j))).trans_le
      (R.makes.wilson.represents N p j hj).band.1))
  have receipts (j : Fin n) := WilsonTrueProjectedLocatedHistory.sale R (N:=N) (stop:=b+n)
    wood a depth digit W book g top (o (b+j)) (by omega)
    (rate _ (by omega)) (course.1.walk (b+j) (by omega) (by omega)).truep.valid anchor
    (prices (b+j)) (intakePaid _ (by omega) (by omega)) (localPaid _ (by omega) (by omega))
  choose z ps using receipts
  let q : ∀ j,store R.family d p (b+j) := fun j => if h : j<n then z ⟨j,h⟩ else ((R.family).factory d N p).entries (b+j) 0
  have price (j : ℕ) (hj : j<n) := ps (⟨j,hj⟩ : Fin n)
  have bought (j : ℕ) (hj : j<n) :
      (q j).Format (o (b+j)) (R.family).params (W (b+j)) ∧
      (q j).remBound (o (b+j)) (W (b+j)) (safety R.family (b+j)) (bill j) ∧
      ((R.family).labels.level d).coeffSize (q j).x ≤ bill j ∧
      transition (C:=R.family) d N p (b+j) (F (j+1))=F j+(q j).density (o (b+j)) ((R.family).localSection d) (W (b+j)) := by
    rw [show q j=z ⟨j,hj⟩ by simp [q,hj]]
    exact ⟨(price j hj).1.1,(price j hj).1.2.1,(price j hj).1.2.2,(price j hj).2⟩
  obtain ⟨A,H,Z,X,u,e,parts,field⟩ := words m N p k n mb bn π Γ W course o route gates roof F q bill
    (fun j hj => WilsonTrueProjectedLocatedHistory.intake R (W (b+j)) (book (b+j)) (intakePaid _ (by omega) (by omega)) _)
    bought
  let tab : Receipt R d N p b n W o F bill ε :=
    ⟨A,X,H,Z,u,e,fun j=>(parts j).1,
    fun j=>⟨(parts j).2.1,(parts j).2.2.1,(parts j).2.2.2.1⟩,
    fun j=>⟨(parts j).2.2.2.2.1,(parts j).2.2.2.2.2.1,(parts j).2.2.2.2.2.2.1⟩,
    fun j=>(parts j).2.2.2.2.2.2.2.1,fun j=>(parts j).2.2.2.2.2.2.2.2,field⟩
  have salaryAt (i : ℕ) (hi : i≤n) := quotes enrolled digit N p (b+n) i (n-i) (by omega) bn
    report origin fare ho hf originPaid prices (fun j lo up => pricesPaid j (by omega) (by omega))
  refine ⟨tab,?_,?_⟩
  · have paid := salaryAt 0 (Nat.zero_le n)
    simp only [Nat.add_zero,Nat.sub_zero,WilsonPinnedWidthTransport.elapsed,sub_self,mul_zero,Real.exp_zero,mul_one] at paid
    exact (Finset.sum_le_sum (fun j _ => tab.nullCost j)).trans
      ((Fin.sum_univ_eq_sum_range (fun j => gain R.family b (b+j)*((2+4*stock R.family (b+j))*bill j)) n).le.trans paid)
  · intro i hi
    calc
      _ = ∑ j ∈ Finset.range (n-i),gain R.family (b+i) (b+i+j)*((2+4*stock R.family (b+i+j))*
          datedFee R wood a depth digit N (b+n) Q g top (b+i+j) (prices (b+i+j))) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Nat.add_assoc b i j]
      _ ≤ _ := salaryAt i hi

end YM.Integration.WilsonTrueProjectedLocatedFunded
