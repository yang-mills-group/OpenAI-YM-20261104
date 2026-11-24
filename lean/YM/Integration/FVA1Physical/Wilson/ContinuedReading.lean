import YM.Integration.FVA1Physical.Wilson.ContinuedTicket
import YM.Integration.FVA1Physical.Wilson.RawTicket
import YM.Integration.FVA1Physical.Wilson.InheritedPrice

/-! Seed both entries of the finite conditional recursion directly from RG02.
The first forest is the actual purchased top block. Every subsequent block
integrates the complete preceding vacuum and the corresponding joint insertion. -/
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Lattice RG YM.Wilson Tree Precision Marker Comparison.RG02
open FVA2.CityHistory FVA2.CityHistory.Delay FormalOPE.RG10.MultiGauge
open FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.MarkovChain.Warp
open RGComparison.Core16 RGComparison.Core16.Descent
open FormalOPE.RG10.InversionTop RGComparison.Core16.WilsonXLocal PhysicalNext.Repeat.Legato
open scoped Classical

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] (R : Census V) (A : Run G)
    {j p l : ℕ} (U : V → Stamp.Reservation A.family (A.family.side (j+1) p) l)
    (F : Forest (A.family.path.levels.clock.op j p).ratio) (t : (A.family.path.levels.clock.op j p).Choices)
    (h : Bid.Larger (G:=G) (A.family.path.levels.clock.op j p))
local notation "L" => RunFormalChain.fromRun A
local notation "S" => A.family.path.levels.clock.op j p
local notation "d₁" => Descent.push S F Descent.nil
local notation "H₁" => And.intro h True.intro
local notation "η₁" => (t,())
local notation "D" => MSMatch.SourceTop.datum R j p U F t 0
variable {c : Side} (P : Descent (A.family.side j p) c) (τ : P.Tags) (H : P.Room G)

/-- A full pair of spatial polynomial tickets obtained by iterating the RG02
Wick bank at the top scale and normalized block integration afterwards. -/
def wilsonReading (z : ℕ → PowerSeries ℝ) (s : R.Mode) (q : Bool) :=
  Continuation.readings d₁ (L).O η₁ H₁ (rawTicket ((D).kernel L) F t (D).colors)
    (rawMarkedTicket R U F t L s q) P τ H z

/-- Every field, every order, every joint marker and every admitted sequence
of block choices. All input coefficient identifications are discharged. -/
theorem wilsonReading_eq (z : ℕ → PowerSeries ℝ) (hz : z (1+P.depth) = 1)
    (s : R.Mode) (q : Bool) :
    wilsonReading R A U F t h P τ H z s q =
      (μLedger (Continuation.extended d₁ P) (L).O (Continuation.tags d₁ η₁ P τ)
         (Continuation.room d₁ H₁ P H) z,
       skyread (L).O (Continuation.extended d₁ P) (Continuation.tags d₁ η₁ P τ)
         (Continuation.room d₁ H₁ P H) z
         (exPay (RGComparison.Core16.Spool.look q ∘ fullProduct (MSMatch.SourceTop.field U) s.val))) := by
  let v := fun i => z (i+P.depth)
  have hs : v 1 = 1 := hz
  have supply : supplyZ (G:=G) d₁ (L).O η₁ v = supplyZ d₁ (L).O η₁ 1 := by
    simp only [supplyZ,parentZ,Pi.one_apply,hs]
  have eqv : μLedger d₁ (L).O η₁ H₁ v = μLedger d₁ (L).O η₁ H₁ 1 := by
    unfold μLedger
    rw [supply]
  exact Continuation.readings_eq d₁ (L).O η₁ H₁ _ _ (L).receipt P τ H z _
    ((rawTicket_eq ((D).kernel L) F t (D).colors (A.family.path.levels.budget (j+1))
      (MSMatch.SourceTop.witnessed L R j p U A.makes (Next.Foundations.valuation G))
      (L).O (L).receipt h ()).trans eqv.symm)
    (rawMarkedTicket_eq R U F t L A.makes (Next.Foundations.valuation G) h (L).O (L).receipt
      () v hs s q)

/-- A scalar coefficient after evaluation at the retained flat link. -/
def wilsonCoefficient (a : ℕ → ℝ) (s : R.Mode) (k : ℕ) : ℂ :=
  let comp := fun q => PowerSeries.coeff (weight R (MSMatch.SourceTop.grade U) s+k)
    (Stack.read 0 (wilsonReading R A U F t h P τ H (stones a) s q).2)
  ⟨comp false,comp true⟩

theorem wilsonCoefficient_eq (a : ℕ → ℝ) (ha : a (1+P.depth) = 0) (s : R.Mode) :
    wilsonCoefficient R A U F t h P τ H a s =
      historyCoefficient R U (Continuation.extended d₁ P) (L).O
        (Continuation.room d₁ H₁ P H) (Continuation.tags d₁ η₁ P τ) a s := by
  have hi : stones a (1+P.depth) = 1 := by simp [stones,ha]
  funext k
  simp only [wilsonCoefficient,wilsonReading_eq R A U F t h P τ H (stones a) hi,
    historyCoefficient]

end YM.Integration.FVA1Physical.Wilson
