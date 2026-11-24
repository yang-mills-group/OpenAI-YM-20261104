import YM.Integration.FVA1Physical.Wilson.RawCoefficient

/-! The complete incoming RG02 vacuum bank is a polynomial ticket on coarse
fields. Carry it into both numerator and denominator of the next FVA2 step. -/
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson

open Lattice RG YM.Wilson Tree Precision Marker Comparison.RG02
open FVA2.CityHistory FormalOPE.RG10.MultiGauge FormalOPE.RG10.MultiGauge.Splice
open FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Router RGComparison.Core16
open scoped Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G}
    {O : ChartRatio G} (K : Bulk.Kernel S p P O) (F : Forest S.ratio) (t : S.Choices)
    {V : Type} [Fintype V] [DecidableEq V] {R : Census V} (W : Bulk.Colors R G f)

/-- Form the spatial polynomial ticket solely from the diagonal truncations
of the RG02 Gaussian/Wick construction. Uniqueness follows from evaluation
on every coarse field. -/
def rawTicket : Ticket (Pins G c) :=
  if h : ∃ A : Ticket (Pins G c), ∀ u i,
      PowerSeries.coeff i (Stack.read u A) = rawWilson K F t W u i i then h.choose else 0

variable (D : BudgetPoint) (hW : Bare.Witnessed W K) (Z : ChartRatio G)
    (hZ : LocalRatio Z) (h : Bid.Larger (G := G) S) (v : (Descent.nil (top := f)).Tags)
local notation "d₀" => Descent.nil (top := f)
local notation "d₁" => Descent.push S F d₀

include D hW hZ in
theorem rawTicket_eq : rawTicket K F t W = μLedger d₁ Z (t,v) (And.intro h True.intro) 1 := by
  let J := μLedger d₁ Z (t,v) (And.intro h True.intro) 1
  have ident (u i) : PowerSeries.coeff i (Stack.read u J) = rawWilson K F t W u i i :=
    (raw_ledger_coefficient K F t W D hW Z hZ h v u le_rfl).symm
  have ex : ∃ A : Ticket (Pins G c), ∀ u i,
      PowerSeries.coeff i (Stack.read u A) = rawWilson K F t W u i i := ⟨J,ident⟩
  rw [rawTicket,dif_pos ex]
  apply Stack.into
  intro u
  apply PowerSeries.ext
  intro i
  exact (ex.choose_spec u i).trans (ident u i).symm

/-- The first step and its Wilson bare input use precisely the first
temperature. The values assigned to unused entries in the clock are irrelevant. -/
private theorem first_clock (z : ℕ → PowerSeries ℝ) (hz : z 1 = 1) :
    μLedger d₁ Z (t,v) (And.intro h True.intro) z = μLedger d₁ Z (t,v) (And.intro h True.intro) 1 := by
  have supply : supplyZ (G:=G) d₁ Z (t,v) z = supplyZ d₁ Z (t,v) 1 := by
    simp only [supplyZ,parentZ,Pi.one_apply,hz]
  unfold μLedger
  rw [supply]

variable {a : Side} (T : StepData a c) (B : Forest T.ratio) (b : T.Choices)
    (hT : Bid.Larger (G := G) T) (z : ℕ → PowerSeries ℝ) (htop : z 2 = 1)
local notation "q₁" => gateQ T B b (retained d₁ (t,v) (And.intro h True.intro))
local notation "p₁" => useful T B d₁ (t,v) b hT (And.intro h True.intro)
local notation "U₁" => Quadratic.uptake q₁ (PertExtension.Chart.tangent G B.Free) p₁
local notation "W₁" => fire T B b (rawTicket K F t W) Z (z 1)

include D hW hZ htop in
/-- The second physical formal vacuum integrates the complete incoming RG02
ticket, new edge kernel, interaction charge and Haar density on one Gaussian. -/
theorem second_raw_ledger :
    μLedger (Descent.push T B d₁) Z (b,(t,v)) ⟨hT,(And.intro h True.intro)⟩ z = U₁ W₁ := by
  rw [judgment T B d₁ (t,v) b Z z hT (And.intro h True.intro),first_clock F t Z h v (parentZ z) htop,
    rawTicket_eq K F t W D hW Z hZ h v]

include D hW hZ htop in
/-- Any second-step insertion uses the same independent density in the
numerator and the full unmarked denominator. -/
theorem second_raw_conditional (A : Ticket (Future G T B × Pins G a)) :
    incline (U₁ W₁) ∧
    solenoid T B d₁ (t,v) b Z z hT (And.intro h True.intro) A = U₁ (W₁*A) * Return (U₁ W₁) ∧
    U₁ W₁ * solenoid T B d₁ (t,v) b Z z hT (And.intro h True.intro) A = U₁ (W₁*A) := by
  have hin : rawTicket K F t W = μLedger d₁ Z (t,v) (And.intro h True.intro) (parentZ z) :=
    (rawTicket_eq K F t W D hW Z hZ h v).trans (first_clock F t Z h v _ htop).symm
  rw [hin]
  have w := primeZ T B d₁ (t,v) b Z z hZ hT (And.intro h True.intro)
  exact ⟨Quadratic.upright _ _ _ w,rfl,Quadratic.fit_eq _ _ _ _ _ w⟩

end YM.Integration.FVA1Physical.Wilson
