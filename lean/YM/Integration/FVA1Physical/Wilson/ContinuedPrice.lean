import YM.Integration.FVA1Physical.Wilson.ContinuedReading

/-! The actual measured finite trajectory can be split immediately below
its bare step for any number of further RG blocks. -/
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Lattice RG YM.Wilson Tree Precision Marker FVA2.CityHistory
open RGComparison.Core16 RGComparison.Core16.Descent RGComparison.Core16.WilsonXLocal
open PhysicalNext.Repeat.Legato PertExtension.Series.Tested FormalOPE.RG10.InversionTop
open scoped Classical

theorem traversal_extend {G : Gauge} {L : Levels G} {p j m : ℕ}
    (T : Slices L p) (hm : m ≤ j) :
    Continuation.extended (Descent.push (L.clock.op j p) (T j) Descent.nil)
      (traversal T hm) = traversal T (Nat.le_succ_of_le hm) := by
  induction hm using Nat.decreasingInduction with
  | self =>
    rw [traversal_self,traversal_push T (Nat.lt_succ_self j),traversal_self]
    rfl
  | of_succ m hm ih =>
    rw [traversal_push T hm,Continuation.extended,traversal_push T (show m < j+1 by omega),ih]

variable {G : Gauge} {V : Type} [Fintype V] [DecidableEq V] (R : Census V) (A : Run G)
    {j p m l : ℕ} (U : V → Stamp.Reservation A.family (A.family.side (j+1) p) l)
    (T : Slices A.family.path.levels p) (hm : m ≤ j)
    (b : (A.family.path.levels.clock.op j p).Choices)
    (h : Bid.Larger (G:=G) (A.family.path.levels.clock.op j p))
    (τ : (traversal T hm).Tags) (H : (traversal T hm).Room G)
local notation "S" => A.family.path.levels.clock.op j p
local notation "d₁" => Descent.push S (T j) Descent.nil
local notation "P" => traversal T hm
local notation "D" => Continuation.extended d₁ P
local notation "Z" => (RunFormalChain.fromRun A).O
local notation "F" => MSMatch.SourceTop.field U
local notation "w" => MSMatch.SourceTop.grade U

/-- The calibrated normalized physical moments at every finite depth and
order, evaluated at the identity, are priced by the explicit RG02-seeded
recursion. The constant is fixed per finite torus and independent of the
probing coupling and joint mode. -/
theorem continued_calibrated_price (r : ℕ) :
    let v := actualOffset A.family p (j+1) m
    let K := wilsonCoefficient R A U (T j) b h P τ H v
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ g : ℝ, 0 < g → ∀ s : R.Mode,
        ‖g⁻¹ ^ weight R w s • ((D).moments R (offset v g) F 1).part s -
          peval (K s) r g‖ ≤ B*g^(r+1)) ∧
      let g := Pert.Asymptotics.regulatorRun A.family (j+1) p (j+1)
      0 < g ∧ ∀ s : R.Mode,
        ‖g⁻¹ ^ weight R w s •
          ((((A.family.path.rep (j+1) p m).eval 1 : ℝ) : ℂ)⁻¹ *
          ((D).marks R (line A.family.path p m (j+1)) F 1).part s) -
          peval (K s) r g‖ ≤ B*g^(r+1) := by
  dsimp only
  let v := actualOffset A.family p (j+1) m
  have hv : v (1+(P).depth) = 0 := by
    dsimp only [v,actualOffset]
    rw [traversal_depth,show m+(1+(j-m))=j+1 by omega,sub_self]
  have hp := fun (H' : (traversal T (Nat.le_succ_of_le hm)).Room G)
      (t' : (traversal T (Nat.le_succ_of_le hm)).Tags) =>
    calibrated_history_price R A U T (Nat.le_succ_of_le hm) H' t' r
  rw [← traversal_extend T hm] at hp
  have e (s : R.Mode) := wilsonCoefficient_eq R A U (T j) b h P τ H v hv s
  dsimp only [v] at e
  simpa only [← e] using hp (Continuation.room d₁ ⟨h,True.intro⟩ P H) (Continuation.tags d₁ (b,()) P τ)

end YM.Integration.FVA1Physical.Wilson
