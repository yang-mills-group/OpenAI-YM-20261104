import YM.Integration.FVA1Physical.Marked.CombinedEntry

/-! Each prescribed complex microscopic field, after any real-linear test,
is represented on its original input and site by one paid native program.
The signed coefficient price is kept external to the unit source. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Filter Lattice RG Wilson Source Marker Multi Qlocal Quipu Quipu.Sonnet Tern Harmony
open Extra.Histories Extra.Trajectories LocalLTE.Sail MergeProof Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pressure
open scoped Classical BigOperators
variable {I : Type} [DecidableEq I] {B : Census I} {G : Gauge}

private def silent (ξ : I→ℕ) (qd : ℕ) : Stanza B G ξ qd := fun s=>Motif.vacant s G ξ qd

private theorem silent_paid (ξ : I→ℕ) (qd q : ℕ) (w : ℝ) :
    (Stanza.son (silent (B:=B) (G:=G) ξ qd) q).Allows w 1 :=
  (Motif.chapters ..).2 (fun _=>Motif.empty zero_le_one)

private def usable (i : I) (e : FieldOperand (Hot.one B i) G) (ξ : I→ℕ) (qd : ℕ) (w : ℝ) :
    Stanza B G ξ qd := if he:e.order ≤ qd then fieldBook ξ e he w else silent ξ qd

private theorem usable_paid (i : I) (e : FieldOperand (Hot.one B i) G) (ξ : I→ℕ) (qd q : ℕ) (w : ℝ) :
    (Stanza.son (usable i e ξ qd w) q).Allows w 1 := by
  unfold usable
  split <;> first | apply fieldBook_paid | apply silent_paid

private theorem usable_read (i : I) (e : FieldOperand (Hot.one B i) G) (ξ : I→ℕ) (qd cut q : ℕ)
    (w g : ℝ) {c : Side} (o : I→Site c) (v : Config G c) :
    let A := Stanza.son (usable i e ξ qd w) q
    A.wake (Hot.one B i) (A.short (fun _ _ _ _=>True) cut) o g v = entryReading i e ξ qd cut q w g o v := by
  intro A
  by_cases he:e.order ≤ qd
  · have eq : usable i e ξ qd w = fieldBook ξ e he w := dif_pos he
    dsimp only [A]
    rw [eq,entryReading,dif_pos he]
  have eq : usable i e ξ qd w = silent ξ qd := dif_neg he
  dsimp only [A]
  rw [eq,entryReading,dif_neg he,Tale.notationW,Motif.story]
  simp only [silent,Motif.empty_lyric]
  exact zero_div _

private theorem list_sum {X : Type} (xs : List X) (f : X→ℂ) :
    (xs.map f).sum = ∑ i : Fin xs.length,f (xs.get i) := by
  calc
    _ = ((List.ofFn xs.get).map f).sum := by rw [List.ofFn_get]
    _ = _ := by rw [List.map_ofFn,List.sum_ofFn]; rfl

def movingProbe (a : ℂ) (m : Motion) (L : ℂ →ₗ[ℝ] ℝ) : ℂ →ₗ[ℝ] ℝ where
  toFun z := L (a * Motion.scalar m (a⁻¹*z))
  map_add' x y := by simp only [mul_add,Motion.scalar_add,map_add]
  map_smul' r x := by
    simp only [RingHom.id_apply,Complex.real_smul]
    rw [mul_left_comm a⁻¹ (r:ℂ),Motion.scalar_mul,Motion.scalar_real,mul_left_comm a]
    exact L.map_smul r _

theorem collect_channel {F : Type} [Fintype F] (j : I)
    (rows : F→List (FieldOperand (Hot.one B j) G)) (z : F→ℂ) (L : ℂ →ₗ[ℝ] ℝ)
    (ξ : I→ℕ) (qd q : ℕ) (w : ℝ) (hw : 0<w) :
    ∃ (P : Stanza B G ξ qd) (C : ℝ), 1 ≤ C ∧ (Stanza.son P q).Allows w 1 ∧
      ∀ (cut : ℕ) {c : Side} (o : I→Site c) (g : ℝ) (v : Config G c),
      let A := Stanza.son P q
      L (∑ i,z i * ((rows i).map (fun e=>(e.factor*(e.room w:ℂ)) *
        (entryReading j e ξ qd cut q w g o v:ℂ))).sum) =
        C * A.wake (Hot.one B j) (A.short (fun _ _ _ _=>True) cut) o g v := by
  let J := (i : F) × Fin (rows i).length
  let entry (k : J) := (rows k.1).get k.2
  let factor (k : J) := z k.1 * ((entry k).factor * ((entry k).room w:ℂ))
  let book : Option J→Stanza B G ξ qd
    | none => silent ξ qd
    | some k => usable j (entry k) ξ qd w
  let a : Option J→Senses B→ℝ
    | none, _ => 0
    | some k, _ => L (factor k)
  have paid (k : Option J) : (Stanza.son (book k) q).Allows w 1 := by
    cases k with
    | none => exact silent_paid ..
    | some k => exact usable_paid ..
  obtain ⟨P,hP,hval⟩ := combine_entries book a hw paid
  refine ⟨P,sourceRoom a (Hot.one B j),?_ ,hP,?_⟩
  · unfold sourceRoom; exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _=>abs_nonneg _))
  intro cut c o g v A
  have lin (x : ℂ) (y : ℝ) : L (x*(y:ℂ)) = L x*y := by
    rw [mul_comm,← Complex.real_smul,map_smul,smul_eq_mul,mul_comm]
  rw [hval (Hot.one B j) cut o g v,Fintype.sum_option]
  simp only [a,book,zero_mul,zero_add]
  rw [Fintype.sum_sigma]
  simp only [list_sum,Finset.mul_sum,map_sum]
  refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun e _=>?_
  rw [usable_read,← mul_assoc,lin]

/-- One genuine signed, displaced microscopic physical field on the
purchased trajectory. Every real-linear projection (including real or
imaginary part) is a single unit-admitted native wallet source multiplied
by its finite external coefficient cost; the program precedes all fields
and all positive input couplings. -/
theorem physical_channel_program (X : Run G) (simple : G.Simple) (D : ℕ) (j : I) :
    ∃ qd : ℕ, ∀ᶠ N : ℕ in atTop, ∀ (n : ℕ) (Y : Batch X.family.path N n I),
    Y.demand j ≤ D → ∀ (ξ : I→ℕ) (q : ℕ) (width : ℝ), 0<width → ∀ L : ℂ →ₗ[ℝ] ℝ,
    ∃ (P : Stanza B G ξ qd) (C : ℝ), 1 ≤ C ∧ (Stanza.son P q).Allows width 1 ∧
      ∀ (g : ℝ), 0<g → ∀ v : Config G (X.family.side N n),
      let A := Stanza.son P q
      L (Y.wavelengths j v) = C * A.wake (Hot.one B j)
        (A.short (fun _ _ _ _=>True) (Stores.till (X.alloy.B.a.clock.hatBeta N))) (Y.origin N) g v := by
  obtain ⟨qd,hr⟩ := physical_entry_program (B:=B) X simple D j
  refine ⟨qd,?_⟩
  filter_upwards [hr] with N hN
  intro n Y hd ξ q width hw L
  let d := Y.demand j
  let a := (X.family.S.a N:ℂ)^d
  let F := (Labels.frames G).level d
  let z := F.act (Y.motion j).1.ortho (F.scaled (X.family.path.levels.clock.threshold N)⁻¹ (Y.voice j))
  obtain ⟨P,C,hC,hP,read⟩ := collect_channel j (nativeBasis (Hot.one B j) d) z
    (movingProbe a (Y.motion j) L) ξ qd q width hw
  refine ⟨P,C,hC,hP,?_⟩
  intro g hg v A
  rw [hN n Y hd ξ q width g hg v]
  exact read _ (Y.origin N) g v

end YM.Integration.FVA1Physical.Marked
