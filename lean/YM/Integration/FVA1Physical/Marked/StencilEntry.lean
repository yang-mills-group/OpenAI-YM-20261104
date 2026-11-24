import YM.Integration.FVA1Physical.Marked.PaidSource
import YM.Qlocal.Harmony.Snips

/-! Put a single genuine operand into a unit-admitted native stanza. Its
row is at its actual curvature rank, so the marked engineering power cancels
exactly. The three source tests, period choice and cutoff do not change the row. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Lattice RG Wilson Marker Multi Qlocal Quipu Quipu.Sonnet Tern Harmony
open scoped Classical BigOperators
variable {I : Type} [DecidableEq I] {B : Census I} {G : Gauge} {s : Senses B}
variable {ξ : I→ℕ} {qd : ℕ}

def fieldRow (p : Motif.Leaf s ξ qd) (a : Vase s G p.2.val) : Motif.Row s G ξ qd :=
  Function.update (Motif.vacant s G ξ qd) p.1
    (Function.update (Motif.vacant s G ξ qd p.1) p.2 (Motif.dot a 0))

theorem fieldRow_paid (p : Motif.Leaf s ξ qd) (a : Vase s G p.2.val) {w : ℝ}
    (ha : a.fare w ≤ 1) : Motif.Paid (fieldRow p a) w 1 := by
  constructor
  intro i j
  by_cases h:i=p.1
  · subst i
    unfold fieldRow
    rw [Function.update_self]
    by_cases h:j=p.2
    · subst j; rw [Function.update_self]; exact Motif.dormant a 0 ha
    rw [Function.update_of_ne h]
    exact (Motif.empty zero_le_one).bill .. 
  unfold fieldRow
  rw [Function.update_of_ne h]
  exact (Motif.empty zero_le_one).bill ..

private theorem selected_dot {k : ℕ} (a : Vase s G k) (Z : ℕ→Prop) (hz : Z 0)
    {c : Side} (o : I → Site c) (q : ℕ) (v : Config G c) :
    Album.picture Z (Motif.dot a 0) o q v = Conductor.solo a o q v := by
  unfold Album.picture Album.realize
  rw [tsum_eq_single 0]
  · rw [Conductor.utt,if_pos hz,Motif.dot,Function.update_self]
  intro i hi
  rw [Conductor.utt]
  by_cases h:Z i
  · rw [if_pos h,Motif.dot,Function.update_of_ne hi]; exact Motif.solo_z o q v
  rw [if_neg h]; rfl

private theorem fieldRow_read (p : Motif.Leaf s ξ qd) (a : Vase s G p.2.val)
    (Z : Motif.Play s ξ qd) (hz : Z p.1 p.2 0) {c : Side}
    (o : I→Site c) (q : ℕ) (g : ℝ) (v : Config G c) :
    Motif.lyric (fieldRow p a) Z o q g v = g^Motif.power p * Conductor.solo a o q v := by
  unfold Motif.lyric
  rw [Finset.sum_eq_single p.1]
  · rw [Finset.sum_eq_single p.2]
    · unfold fieldRow; rw [Function.update_self,Function.update_self,selected_dot a _ hz]
    · intro j _ hj
      unfold fieldRow; rw [Function.update_self,Function.update_of_ne hj]
      exact mul_eq_zero_of_right _ (Motif.nulled o q _ v)
    simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _=>?_
    unfold fieldRow; rw [Function.update_of_ne hi]
    exact mul_eq_zero_of_right _ (Motif.nulled o q _ v)
  simp

def fieldGrade (s : Senses B) (ξ : I→ℕ) (k qd : ℕ) (h : k ≤ qd) : Motif.Leaf s ξ qd :=
  ⟨⟨k,Nat.lt_succ_of_le h⟩,⟨k,by change k < k + Lagger.dues ξ s.val + 1; omega⟩⟩

def fieldBook (ξ : I→ℕ) (a : FieldOperand s G) {qd : ℕ} (h : a.order ≤ qd) (w : ℝ) : Stanza B G ξ qd :=
  Function.update (fun u => Motif.vacant u G ξ qd) s (fieldRow (fieldGrade s ξ a.order qd h) (a.unit w))

theorem fieldBook_paid (ξ : I→ℕ) (a : FieldOperand s G) (qd : ℕ) (h : a.order ≤ qd) (w : ℝ) (q : ℕ) :
    (Stanza.son (fieldBook ξ a h w) q).Allows w 1 := by
  apply (Motif.chapters ..).2
  intro u
  by_cases hu:u=s
  · subst u; unfold fieldBook; rw [Function.update_self]; exact fieldRow_paid _ _ (a.paid w)
  unfold fieldBook; rw [Function.update_of_ne hu]; exact Motif.empty zero_le_one

/-- The wallet's honest short selector reads this physical operand, with its
whole fine map and field. It pays no residual power of the coupling. -/
theorem fieldBook_read (ξ : I→ℕ) (a : FieldOperand s G) (qd : ℕ) (h : a.order ≤ qd)
    (w : ℝ) (N q : ℕ) (hn : a.code.momentum ≤ N) {c : Side} (o : I→Site c)
    (g : ℝ) (hg : 0 < g) (v : Config G c) :
    let A := Stanza.son (fieldBook ξ a h w) q
    A.wake s (A.short (fun _ _ _ _=>True) N) o g v = Conductor.solo (a.unit w) o q v := by
  intro A
  let p := fieldGrade s ξ a.order qd h
  let Z := A.short (fun _ _ _ _=>True) N
  have row : fieldBook ξ a h w s = fieldRow p (a.unit w) := Function.update_self ..
  have hz : Z s p.1 p.2 0 := by
    refine ⟨trivial,?_⟩
    change (((fieldBook ξ a h w) s p.1 p.2 0).momentum ≤ N)
    rw [row,fieldRow,Function.update_self,Function.update_self,Motif.dot,Function.update_self]
    exact hn
  have power : Motif.power p = A.boom s := by
    change a.order + Lagger.dues ξ s.val - a.order = Lagger.dues ξ s.val
    omega
  rw [Tale.notationW,Motif.story,row,fieldRow_read p _ (Z s) hz,power]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hg.ne')

end YM.Integration.FVA1Physical.Marked
