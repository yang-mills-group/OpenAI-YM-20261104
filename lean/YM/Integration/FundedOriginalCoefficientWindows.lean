import YM.Integration.RootedVacuumWinding
import YM.Integration.FundedOriginalVacuumPaths
import YM.Integration.FundedMarkedPathSelection
import YM.Integration.OriginalIndependentForestLog

/-! On one donor-selected original Run, all finite recipes for vacuum and
independently marked coefficient windows are purchased before test vectors,
root positions, input kernels, coupling powers and physical periods are read. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FundedOriginalCoefficientWindows
open Filter Function Lattice RG RG.Supply Next.Foundations Wilson
open PhysicalNext PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Embroider
open WilsonLimitConstruction
open scoped Classical BigOperators Topology

universe u
variable {G : Gauge}

structure Quiet where
  cap : ℕ
  order : ℕ
  free : ℕ
  allowed : order ≤ cap

structure Named where
  size : ℕ
  names : Finset (Fin size)
  domain : Finset (Fin size)
  root : Fin size
  derivatives : Fin size → ℕ
  grade : Fin size → ℕ
  cap : ℕ
  order : ℕ
  free : ℕ
  address : ℕ
  included : names ⊆ domain
  anchored : root ∈ names
  graded : ∀ i, grade i < derivatives i
  allowed : order ≤ cap

private def quietKey (s : Quiet) := (s.cap,s.order,s.free)
private def namedKey (s : Named) : Σ n : ℕ,
    Finset (Fin n) × Finset (Fin n) × Fin n × (Fin n → ℕ) × (Fin n → ℕ) × ℕ × ℕ × ℕ × ℕ :=
  ⟨s.size,s.names,s.domain,s.root,s.derivatives,s.grade,s.cap,s.order,s.free,s.address⟩

instance : Countable Quiet :=
  (show Injective quietKey by rintro ⟨_,_,_,_⟩ ⟨_,_,_,_⟩ h; cases h; rfl).countable
instance : Countable Named :=
  (show Injective namedKey by
    rintro ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩ ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩ h
    cases h; rfl).countable

abbrev Shape := Quiet ⊕ Named

/-- Shape validity only bounds the nominal index of a finite coefficient.
The positive-power case `s.order > s.free` is included. -/
def Window (R : Run G) (w s : Gear G → ℝ) (c q : ℕ) (m : ℕ) : Shape → Prop
  | .inl z => RootedVacuumWinding.Window R z.cap z.order z.free c q s m
  | .inr z => FundedMarkedWindingWindow.Window R z.names z.domain z.root z.derivatives
      z.grade z.cap z.order z.free z.address c q w s m

/-- The original exponential dependency on the actual period survives the common calendar. -/
def Receipt (R : Run G) (w s : Gear G → ℝ) (c q a : ℕ) (m : ℕ) : Shape → Prop
  | .inl z => RootedVacuumWinding.Receipt R z.cap z.order z.free c q a s m
  | .inr z => FundedMarkedWindingWindow.Receipt R z.names z.domain z.root z.derivatives
      z.grade z.cap z.order z.free z.address c q a w s m

private theorem forget {R : Run G} {w s : Gear G → ℝ} {c q a m : ℕ} (z : Shape) :
    Receipt R w s c q a m z → Window R w s c q m z := by
  cases z with
  | inl t =>
    rintro ⟨Q,hm,draws,chart,h⟩
    refine ⟨Q,hm,draws,chart,?_⟩
    intro N p hN n g
    obtain ⟨B,b,_,roots⟩ := h N p hN
    exact ⟨B,b,roots⟩
  | inr t =>
    rintro ⟨Q,hm,draws,chart,hy,closed,tickets,h⟩
    refine ⟨Q,hm,draws,chart,hy,closed,tickets,?_⟩
    intro N p hN n g I K b A hA pre x F P
    obtain ⟨B,hB,_,roots⟩ := h N p hN K b A hA pre
    exact ⟨B,hB,roots⟩

private theorem purchase (w : Gear G → ℝ) (hw : ∀ I, 0 < w I) (z : Shape) :
    ∃ (v : ℕ → Gear G → ℝ) (s : Gear G → ℝ) (a : ℕ), (∀ I, 0 < s I) ∧
      ∀ (R : Run G) (_hG : G.Simple) (donor : ℕ → Gear G → ℝ),
      FundedMarkedCoverRows.prices donor R.kit →
      (∀ᶠ m : ℕ in atTop, ∀ I, v (R.family.path.levels.clock.J (m+1)) I ≤
        donor (R.family.path.levels.clock.J (m+1)) I) →
      RG05Preconstruction.ReadoutPurchase R.b → ∀ c q : ℕ,
      ∀ᶠ m : ℕ in atTop, Receipt R w s c q a m z := by
  cases z with
  | inl z => exact RootedVacuumWinding.priced z.cap z.order z.free z.allowed w hw
  | inr z =>
    obtain ⟨v,s,a,h,_,pick⟩ := FundedMarkedWindingWindow.priced z.included z.root z.anchored
      z.derivatives z.grade z.graded z.cap z.order z.free z.allowed w hw z.address
    exact ⟨v,s,a,h,pick⟩

/-- A single finite debit per profile index. Every requested shape receives
its very own quote at all sufficiently deep original donor indices. -/
private def diagonal [Encodable Shape] (v : Shape → ℕ → Gear G → ℝ) (j : ℕ) (I : Gear G) :=
  ∑ code ∈ Finset.range (j+1), |((Encodable.decode code : Option Shape)).elim 0 (fun z => v z j I)|

private theorem covers [Encodable Shape] (v : Shape → ℕ → Gear G → ℝ) (z : Shape)
    (A : Levels G) : ∀ᶠ m : ℕ in atTop, ∀ I, v z (A.clock.J (m+1)) I ≤
        diagonal v (A.clock.J (m+1)) I := by
  have depth : Tendsto (fun m => A.clock.J (m+1)) atTop atTop :=
    A.fits.deep.comp (tendsto_add_atTop_nat 1)
  filter_upwards [depth.eventually_ge_atTop (Encodable.encode z)] with m hm
  intro I
  let j := A.clock.J (m+1)
  have one := Finset.single_le_sum (s := Finset.range (j+1))
    (f := fun code => |((Encodable.decode code : Option Shape)).elim 0 (fun z => v z j I)|)
    (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
  exact (le_abs_self _).trans (by simpa [diagonal,j] using one)

/-- All spatial stocks precede the original Run. Its own `B.kin` supplies
the incoming quiet path, and the corrected m-th field and marker tensors are
paid for every finite shape on that Run. The caller's original prediction
is preserved by the same real construction. -/
theorem priced (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (w : Gear G → ℝ) (hw : ∀ I, 0 < w I)
    (P : FundedCompanySelection.Prediction G) (hP : FundedPredictionSupply.AllPrices (@P)) :
    ∃ (s : Shape → Gear G → ℝ) (a : Shape → ℕ) (donor : ℕ → Gear G → ℝ),
      (∀ z I, 0 < s z I) ∧ ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
        FundedMarkedCoverRows.prices donor R.kit ∧ FundedOriginalVacuumPaths.prices R.kit ∧
        P R.kit ∧ NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
          ∀ (z : Shape) (c q : ℕ), ∀ᶠ m : ℕ in atTop, Receipt R w (s z) c q (a z) m z := by
  letI : Encodable Shape := Encodable.ofCountable Shape
  choose v s a positive pick using purchase w hw
  let donor := diagonal v
  obtain ⟨R,T,W,hcover,hstock,hP',hcor,hfund⟩ :=
    FundedOriginalVacuumPaths.original.{u} hG hε donor (@P) hP
  have readout : RG05Preconstruction.ReadoutPurchase R.b := hfund.2.2.2.2.2.2.1
  refine ⟨s,a,donor,positive,R,T,W,hcover,hstock,hP',hcor,hfund,?_⟩
  intro z
  exact pick z R hG donor hcover (covers v z R.family.path.levels) readout


theorem original (hG : G.Simple) {ε : ℝ} (hε : 0 < ε)
    (w : Gear G → ℝ) (hw : ∀ I, 0 < w I)
    (P : FundedCompanySelection.Prediction G) (hP : FundedPredictionSupply.AllPrices (@P)) :
    ∃ (s : Shape → Gear G → ℝ) (donor : ℕ → Gear G → ℝ),
      (∀ z I, 0 < s z I) ∧ ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
        FundedMarkedCoverRows.prices donor R.kit ∧ FundedOriginalVacuumPaths.prices R.kit ∧
        P R.kit ∧ NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} hG ε W ∧
          ∀ (z : Shape) (c q : ℕ), ∀ᶠ m : ℕ in atTop, Window R w (s z) c q m z := by
  obtain ⟨s,a,donor,pos,R,T,W,hc,hs,hP,cor,funded,stock⟩ := priced.{u} hG hε w hw (@P) hP
  exact ⟨s,donor,pos,R,T,W,hc,hs,hP,cor,funded,fun z c q =>
    (stock z c q).mono (fun _ h => forget z h)⟩

/-- A bounded family of moving source types can be read at the same stage
on this already selected Run, in any order and at any admitted period. -/
theorem finiteStages (R : Run G) (w : Gear G → ℝ) (s : Shape → Gear G → ℝ) (a : Shape → ℕ)
    (stock : ∀ z c q, ∀ᶠ m : ℕ in atTop, Receipt R w (s z) c q (a z) m z)
    (S : Finset Shape) (c q : ℕ) : ∀ᶠ m : ℕ in atTop, ∀ z∈S, Receipt R w (s z) c q (a z) m z := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert z₀ S _ h =>
    filter_upwards [stock z₀ c q,h] with m hz hS
    simpa only [Finset.forall_mem_insert] using And.intro hz hS

end YM.Integration.FundedOriginalCoefficientWindows
end
