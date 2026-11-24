import YM.Integration.FVA1Physical.Marked.MicroscopicField
import YM.Qlocal.Dialect.Stack

/-! The genuine microscopic source uses a finite list of unit-priced real
code operands, with their exact external coefficients. All its operands fit
the actual short-path admission at sufficiently high ultraviolet cutoff. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Filter Lattice RG Wilson Source Marker Qlocal Quipu Quipu.Sonnet Dialect Extra.Trajectories Extra.Histories LocalLTE.Sail MergeProof
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Next.Foundations Pressure
open scoped Classical BigOperators

variable {I K : Type} [DecidableEq K] {B : Census K} {G : Gauge} {s : Senses B}

def FieldOperand.room (a : FieldOperand s G) (width : ℝ) : ℝ := 1 + a.code.fare width
def FieldOperand.unit (a : FieldOperand s G) (width : ℝ) : Vase s G a.order :=
  Stack.mark (a.room width)⁻¹ a.code

theorem FieldOperand.paid (a : FieldOperand s G) (width : ℝ) :
    (a.unit width).fare width ≤ 1 := by
  have hf : 0 ≤ a.code.fare width := mul_nonneg a.code.nn_size (Real.exp_pos _).le
  have hp : 0 < a.room width := by unfold room; linarith
  rw [unit,Stack.Workers.rooms,abs_of_pos (inv_pos.mpr hp),←div_eq_inv_mul,div_le_one hp]
  unfold room
  linarith

theorem FieldOperand.finances (a : FieldOperand s G) (width : ℝ) {c : Side} (x : Site c) (q : ℕ)
    (v : Config G c) :
    (a.factor * (a.room width : ℂ)) * ((a.unit width).read x q v : ℂ) =
      a.factor * (a.code.read x q v : ℂ) := by
  have hf : 0 ≤ a.code.fare width := mul_nonneg a.code.nn_size (Real.exp_pos _).le
  have hp : 0 < a.room width := by unfold room; linarith
  rw [unit,Stack.Workers.moves,Complex.ofReal_mul,Complex.ofReal_inv]
  field_simp [Complex.ofReal_ne_zero.mpr hp.ne']

theorem funded_microscopic (s : Senses B) (width : ℝ) (X : Run G) {N n : ℕ}
    (Y : Batch X.family.path N n I) (j : I) (q : ℕ) (v : Config G (X.family.side N n)) :
    let d := Y.demand j
    let a := (X.family.S.a N:ℂ)^d
    let w := ((Labels.frames G).level d).scaled (X.family.path.levels.clock.threshold N)⁻¹ (Y.voice j)
    let u := pull (Y.motion j).1 (Y.origin N j) v
    Y.wavelengths j v = a * Motion.scalar (Y.motion j) (a⁻¹ *
      ∑ i : ((Labels.frames G).level d).Index,
        w i * ((nativeBasis s d i).map (fun e =>
          (e.factor*(e.room width : ℂ))*((e.unit width).read 0 q u : ℂ))).sum) := by
  intro d a w u
  simp_rw [FieldOperand.finances]
  exact microscopic_source_album s X Y j q v

private theorem list_ceiling (A : List (FieldOperand s G)) :
    ∃ k : ℕ, ∀ e ∈ A, e.code.momentum ≤ k ∧ e.order ≤ k := by
  induction A with
  | nil => exact ⟨0,by simp⟩
  | cons e A ih =>
    obtain ⟨k,h⟩ := ih
    refine ⟨k+e.code.momentum+e.order,?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl|h'
    · constructor <;> omega
    · have hA := h a h'; constructor <;> omega

/-- Fix a finite field horizon. For every independent coefficient choice and
every period the very same native program has bounded perturbative rank and
eventually passes the true short cutoff at the physical running clock. -/
theorem physical_short_horizon (s : Senses B) (X : Run G) (simple : G.Simple) (D : ℕ) :
    ∃ qd : ℕ, ∀ᶠ N : ℕ in atTop, ∀ (d : ℕ) (_hd : d ≤ D) (i : ((Labels.frames G).level d).Index)
      (e : FieldOperand s G), e ∈ nativeBasis s d i → ∀ width : ℝ,
      e.order ≤ qd ∧ (e.unit width).momentum ≤ Stores.till (X.alloy.B.a.clock.hatBeta N) ∧
        (e.unit width).fare width ≤ 1 := by
  let height (d : ℕ) (i : ((Labels.frames G).level d).Index) := (list_ceiling (nativeBasis s d i)).choose
  let total (d : ℕ) := ∑ i : ((Labels.frames G).level d).Index, height d i
  let qd := ∑ j ∈ Finset.range (D+1), total j
  have hβ : Tendsto X.alloy.B.a.clock.hatBeta atTop atTop :=
    tendsto_atTop_add_const_left _ _ (X.alloy.B.a.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos simple))
  refine ⟨qd,?_⟩
  filter_upwards [(Work.E01.radiusB_tendsto.comp hβ).eventually_ge_atTop (100000*qd)] with N large
  intro d hd i e he width
  have hl := (list_ceiling (nativeBasis s d i)).choose_spec e he
  have h₁ : height d i ≤ total d := Finset.single_le_sum (f:=height d) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  have h₂ : total d ≤ qd := Finset.single_le_sum (f:=total) (fun _ _=>Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hd))
  have hcut : qd ≤ Stores.till (X.alloy.B.a.clock.hatBeta N) := by
    change 100000*qd ≤ radiusB (X.alloy.B.a.clock.hatBeta N) at large
    unfold Stores.till
    omega
  exact ⟨hl.2.trans (h₁.trans h₂),hl.1.trans (h₁.trans (h₂.trans hcut)),e.paid width⟩

end YM.Integration.FVA1Physical.Marked
