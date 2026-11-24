import YM.Integration.WilsonIndependentCapturedDates

/-! The original and prescribed infrared scalar may be tested at the
same weak physical stop, even though their final pages differ. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Integration.WilsonIndependentCapturedPages
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger
open WilsonPositionProgramCommonWindow WilsonPositionProgramReporterBand WilsonPositionProgramVariableCircuit
open WilsonPositionProgramInfraredCircuit Pert.Asymptotics
open scoped Classical Topology
variable {G : Gauge} (C : Run G) (D : XSpace.Run)
local notation "σ" => C.family.S.scale
local notation "a" => C.family.S.a
variable {X : Type} {m j : X → ℕ} (w : X → ℕ → ℕ)
  (blocks : ∀ x k, (C.family.S.block (m x+k)).val = D.ratio^(w x k))

private theorem logCount (p : Page j) :
    Real.log ((WilsonPositionProgramInfraredCircuit.count D j w p).val:ℝ) = Real.log D.finalSide.side.val +
      (elapsed (w p.bindW) (remaining j p):ℝ)*Real.log D.ratio := by
  have ratio : 0 < (D.ratio:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 3) D.large)
  change Real.log ((D.finalSide.side.val*D.ratio^elapsed (w p.bindW) (remaining j p):ℕ):ℝ) = _
  rw [Nat.cast_mul,Nat.cast_pow,Real.log_mul (by exact_mod_cast D.finalSide.side.property.ne') (pow_pos ratio _).ne',Real.log_pow]

theorem length (p : Page j) :
    Real.log ((WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks).l p) =
      σ (m p.bindW+j p.bindW) - σ (date m j p) := by
  let o := Page.opening j p.bindW
  change Real.log (((WilsonPositionProgramInfraredCircuit.count D j w o).val:ℝ) / (WilsonPositionProgramInfraredCircuit.count D j w p).val) = _
  rw [Real.log_div (by exact_mod_cast (WilsonPositionProgramInfraredCircuit.count D j w o).property.ne') (by exact_mod_cast (WilsonPositionProgramInfraredCircuit.count D j w p).property.ne'),
      logCount D w o,logCount D w p]
  change _ + (elapsed (w p.bindW) (j p.bindW-0):ℝ)*_ - _ = _
  rw [Nat.sub_zero]
  have peak := WilsonPositionProgramInversion.logged C D (m p.bindW) (w p.bindW) (blocks p.bindW) (j p.bindW)
  have step := WilsonPositionProgramInversion.logged C D (m p.bindW) (w p.bindW) (blocks p.bindW) (remaining j p)
  change _ = σ (m p.bindW+j p.bindW) - σ (m p.bindW+remaining j p)
  linarith only [peak,step]

def atDate (b : X → ℕ) (above : ∀ x, m x ≤ b x) : Choice j where
  age x := m x+j x-b x
  young x := by dsimp; have := above x; omega

theorem atDate_date (b : X → ℕ) (above : ∀ x, m x ≤ b x) (below : ∀ x, b x ≤ m x+j x) (x : X) :
    date m j ((atDate (j:=j) b above).choose x) = b x := by
  change m x+(j x-(m x+j x-b x))=b x
  have := above x
  have := below x
  omega

theorem ratio (b v : X → ℕ) (bp : ∀ x, m x ≤ b x) (bt : ∀ x, b x ≤ m x+j x)
    (vp : ∀ x, m x ≤ v x) (vt : ∀ x, v x ≤ m x+j x) (x : X) :
    let S := WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
    S.l ((atDate b bp).choose x) / S.l ((atDate v vp).choose x) = a (b x)/a (v x) := by
  intro S
  have lpos (p : Page j) : 0 < S.l p := div_pos
    (by exact_mod_cast (WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j p.bindW)).property)
    (by exact_mod_cast (WilsonPositionProgramInfraredCircuit.count D j w p).property)
  apply Real.log_injOn_pos (div_pos (lpos _) (lpos _)) (div_pos (C.family.S.a_pos _) (C.family.S.a_pos _))
  rw [Real.log_div (lpos _).ne' (lpos _).ne',length C D w blocks,length C D w blocks,
      atDate_date _ _ bt,atDate_date _ _ vt,WilsonIndependentCapturedDates.mesh]
  change σ (m x+j x) - σ (b x) - (σ (m x+j x)-σ (v x)) = _
  ring

/-- A single physical stop for all original periods, cutoffs and films.
Finite early entries use the reporting page itself. -/
structure Stop {stage : ℕ} (B : Band C D stage) (u d : ℕ) where
  date : ℕ → ℕ
  lower : ∀ t, B.lower t ≤ date t
  upper : ∀ t, date t ≤ B.reporter+t
  heard : ∀ᶠ t : ℕ in atTop, u ≤ date t ∧ ∀ N per : ℕ, B.reporter+t ≤ N →
    let g := regulatorRun C.family N per (B.reporter+t)
    0 < g ∧ g ≤ 1 ∧ a (B.reporter+t)/a (date t) ≤ (g^d)^2 ∧
    σ (B.reporter+t)-σ (date t) ≤ 4*(2*d+1)*Real.log g⁻¹

theorem original (simple : G.Simple) (slow : WilsonWindowReportingPace.Slow C.kit)
    {stage : ℕ} (B : Band C D stage) (u d : ℕ) : Nonempty (Stop C D B u d) := by
  classical
  let Good (t v : ℕ) := u ≤ v ∧ B.lower t ≤ v ∧ v ≤ B.reporter+t ∧
    ∀ N per : ℕ, B.reporter+t ≤ N →
      let g := regulatorRun C.family N per (B.reporter+t)
      0 < g ∧ g ≤ 1 ∧ a (B.reporter+t)/a v ≤ (g^d)^2 ∧
      σ (B.reporter+t)-σ v ≤ 4*(2*d+1)*Real.log g⁻¹
  let pick (t : ℕ) := if h : ∃ v, Good t v then h.choose else B.reporter+t
  have basic (t : ℕ) : B.lower t ≤ B.reporter+t := by
    apply (WilsonIndependentCapturedDates.increasing C).le_iff_le.mp
    apply sub_nonneg.mp
    rw [WilsonIndependentCapturedDates.gap C D B t]
    have lr := Real.log_nonneg (show (1:ℝ) ≤ D.ratio by exact_mod_cast ((by decide : 1 ≤ 3).trans D.large))
    positivity
  refine ⟨⟨pick,?_,?_,?_⟩⟩
  · intro t; dsimp [pick]; split
    next h => exact h.choose_spec.2.1
    next => exact basic t
  · intro t; dsimp [pick]; split
    next h => exact h.choose_spec.2.2.1
    next => exact le_rfl
  · filter_upwards [WilsonIndependentCapturedDates.original C D simple slow B u d] with t paid
    change ∃ v, Good t v at paid
    simp only [pick,dif_pos paid]
    exact ⟨paid.choose_spec.1,paid.choose_spec.2.2.2⟩

end YM.Integration.WilsonIndependentCapturedPages

