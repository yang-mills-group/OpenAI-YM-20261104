import YM.Integration.FVA1Physical.Marked.PhysicalEntry
import YM.Qlocal.Dialect.Masons

/-! Finite signed combinations of native field books are admitted in a
single program, with the full coefficient cost kept outside. The program
is selected before any period, cutoff, coupling, site or configuration. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Marker Qlocal Quipu Quipu.Sonnet Tern Dialect
open scoped Classical BigOperators

variable {I J : Type} [DecidableEq I] [Fintype J] [Nonempty J]
    {B : Census I} {G : Gauge} {ξ : I→ℕ} {qd q : ℕ}

def sourceRoom (a : J→Senses B→ℝ) (s : Senses B) : ℝ := 1+∑ i,|a i s|

/-- Every signed test on every marked column is combined at source level.
The same combined stencil works at every period, cutoff and field. -/
theorem combine_entries (A : J→Stanza B G ξ qd) (a : J→Senses B→ℝ)
    {w : ℝ} (hw : 0<w) (paid : ∀ i,(Stanza.son (A i) q).Allows w 1) :
    ∃ P : Stanza B G ξ qd, (Stanza.son P q).Allows w 1 ∧
      ∀ (s : Senses B) (cut : ℕ) {c : Side} (o : I→Site c) (g : ℝ) (v : Config G c),
      let W := Stanza.son P q
      sourceRoom a s * W.wake s (W.short (fun _ _ _ _=>True) cut) o g v =
        ∑ i, a i s * (let E := Stanza.son (A i) q
          E.wake s (E.short (fun _ _ _ _=>True) cut) o g v) := by
  let h (i : J) (s : Senses B) := (sourceRoom a s)⁻¹ * a i s
  have hp (s : Senses B) : 0<sourceRoom a s := by
    unfold sourceRoom
    positivity
  refine ⟨Stack.horizon A h,Stack.honors A h (fun _=>1) paid ?_,?_⟩
  · intro s
    simp only [h,abs_mul,abs_of_pos (inv_pos.mpr (hp s)),mul_one,← Finset.mul_sum]
    rw [← div_eq_inv_mul]
    exact (div_le_one (hp s)).2 (by unfold sourceRoom; linarith)
  intro s cut c o g v W
  rw [show W.wake s (W.short (fun _ _ _ _=>True) cut) o g v = _ from
    Stack.uncured A h (fun _=>1) paid s o v hw g cut, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _=>?_
  simp only [h]
  field_simp [ne_of_gt (hp s)]

end YM.Integration.FVA1Physical.Marked
