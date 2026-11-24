import YM.Integration.WilsonPositionProgramStageRows
import YM.Integration.WilsonPositionProgramNestedElection
import YM.RG16.Unmasked.Pace

/-! Atlas income on the common variable-block Wilson circuit, with the cutoff chosen after the stage purchases. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramInfraredAtlas
open Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Push.PriceCompiler RegulatorIR RegulatorIR.Atlas RegulatorIR.Epoch RegulatorIR.Oracle
open RegulatorIR.Ledger RegulatorIR.FVAAlt2 WilsonPositionProgramVariableCircuit
open scoped Classical Topology ENNReal
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {X : Type} (m j : X → ℕ) (w : X → ℕ → ℕ)
    (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k))
local notation "S" => WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
local notation "A" => C.family.path.levels
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
local notation "Lit" => RG16.Lambda (A)

def budget : Marked j where
  l := (S).l
  gap e := ((S).sizeL e).val
  Z x := Lit (m x+j x)
  cap _ := (RG16.Literal.lambda_pos C.family _).le
  live := (S).l_p
  steps := (S).width_s
  distant e := by exact_mod_cast (show 2 ≤ ((S).sizeL e).val from (by have := (S).holds e; omega))

local notation "B" => budget C D m j w blocks

private theorem wallet (t : Page j) : ENNReal.ofReal (Lit (m t.bindW+j t.bindW)) ≤ (B).age_t.val t := by
  apply ENNReal.ofReal_le_ofReal
  change _ ≤ 1+Lit (m t.bindW+j t.bindW)+|(B).peak t|
  linarith [abs_nonneg ((B).peak t)]

private theorem date_le (t : Page j) : date m j t ≤ m t.bindW+j t.bindW := Nat.add_le_add_left (Nat.sub_le ..) _

private theorem below (simple : G.Simple) (t : Page j) (k : ℕ) (hk : k ≤ m t.bindW+j t.bindW) :
    ENNReal.ofReal (Real.log (Lit k)) ≤ (B).age_t.val t := by
  refine (ENNReal.ofReal_le_ofReal (q:=Lit (m t.bindW+j t.bindW)) ?_).trans (wallet C D m j w blocks t)
  exact (Real.log_le_self (RG16.Literal.lambda_pos C.family k).le).trans ((RG16.Literal.lambda_mono C.family simple).monotone hk)

variable {simple : G.Simple} {a : Axis} {ε : ℝ}

/-- The threshold depends on the requested order and the original course, before any reporter and period. -/
theorem purchased (first : WilsonPositionProgramNestedElection.course simple a ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit) (slow : WilsonWindowReportingPace.Slow C.kit)
    (Z : ∀ P : RG.Patch, P.Branches (A).clock.kernel G) (p : ℕ) : ∃ start : ℕ, ∀ (m j : X → ℕ) (w : X → ℕ → ℕ)
    (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k)), (∀ x, start ≤ m x) →
    SatisfiesQ G Y (WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks) Z (budget C D m j w blocks) p (Lodge.through p) (1/2) := by
  obtain ⟨n,high⟩ := Filter.eventually_atTop.mp ((A).fits.deep.eventually_ge_atTop (Lodge.through p))
  refine ⟨n+1,?_⟩
  intro m j w blocks old
  let clocked := WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
  let walletBook := budget C D m j w blocks
  have older (t : Page j) : n+1 ≤ date m j t := (old _).trans (Nat.le_add_right ..)
  have booked (t : Page j) : Lodge.through p ≤ clocked.J t := high (date m j t) ((Nat.le_succ n).trans (older t))
  have through : p ≤ Lodge.through p := (Nat.le_add_right p 2).trans (le_max_right ..)
  have adj (e : Flap j) : date m j e.prev=date m j e.next+1 :=
    (WilsonPositionProgramInfraredCircuit.history C D m j w blocks).links e
  have measured (z : ℕ) (P : RG.Patch) (hL : P.L=C.family.S.block z) (hJ : P.J=(A).clock.J (z+1)) (hp : p ≤ P.J) :
      glowF G Y Z p (Lodge.through p) P + glowPage G Y (Lodge.through p) P.J ≤ ENNReal.ofReal (Real.log (Lit z)) := by
    have h := WilsonPositionProgramStageRows.actual C paid Z z P hL hJ p hp
    simpa only [ENNReal.ofReal_toReal (ENNReal.add_ne_top.mpr ⟨gf_f G Y Z _,gpage_f G Y _⟩)] using ENNReal.ofReal_le_ofReal h
  have earn (e : Flap j) : walletBook.day e ≤ ENNReal.ofReal (Real.log (Lit (date m j e.next))) :=
    ENNReal.ofReal_le_ofReal (slow.2 (date m j e.next))
  refine {
    shapeS := fun _ => rfl
    capital := ⟨(Uniform.Poly.roof walletBook.age_f).mono ?_, (Uniform.Poly.roof walletBook.age_c).mono ?_⟩
    depth := by dsimp [Lodge.through]; omega
    width := le_max_right ..
    paid := (Uniform.Poly.roof walletBook.age_f).mono ?_
    accountP := (Uniform.Poly.roof walletBook.age_t).mono ?_
    θ_pos := by norm_num
    θ_low := by norm_num
    smooths := fun e => ?_
    intake := fun e => ?_ }
  · intro e; exact (earn e).trans (below C D m j w blocks simple e.prev _ ((date_le m j e.next)))
  · intro e; exact (earn e).trans (below C D m j w blocks simple e.next _ (date_le m j e.next))
  · intro e
    have tip : (clocked.pactP e).J=(A).clock.J (date m j e.next+1) := congrArg (A).clock.J (adj e)
    apply (le_self_add : glowF G Y Z p (Lodge.through p) (clocked.pactP e) ≤ _).trans
    exact (measured _ _ rfl tip (through.trans (booked e.prev))).trans (below C D m j w blocks simple e.prev _ (date_le m j e.next))
  · intro t
    let k := date m j t-1
    have next : k+1=date m j t := by have := older t; dsimp [k]; omega
    let P := ((A).clock.op k 0).patch
    have atP : P.J=clocked.J t := congrArg (A).clock.J next
    change glowPage G Y (Lodge.through p) (clocked.J t) ≤ walletBook.age_t.val t
    rw [←atP]
    apply (le_add_self : glowPage G Y (Lodge.through p) P.J ≤ _).trans
    exact (measured k P rfl rfl (atP.symm ▸ through.trans (booked t))).trans
      (below C D m j w blocks simple t k ((Nat.sub_le ..).trans (date_le m j t)))
  · exact (show 5 ≤ Lodge.through p from (by dsimp [Lodge.through]; omega)).trans (booked e.prev)
  · have hk : (A).clock.kernel=C.metals.p.kernel := C.alloy.B.valid.kernel
    have h := WilsonPositionProgramNestedElection.sufficient (G:=G) (A).clock.kernel
      (through.trans (booked e.prev)) (booked e.prev)
    have grew := first.2.2 (clocked.J e.prev)
    rw [←hk] at grew
    refine h.trans ?_
    change _ ≤ (C.family.S.block (date m j e.next)).val
    rw [show C.family.S.block (date m j e.next)=C.rolls.L ((A).clock.J (date m j e.next+1)) from block_eq C.alloy.B.valid _ ,←adj e]
    exact grew

end YM.Integration.WilsonPositionProgramInfraredAtlas
end
