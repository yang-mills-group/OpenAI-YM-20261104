import YM.Integration.FVA1Physical.Marked.PhysicalChannels

/-! All sources in an actual batch share one honest wallet program and one
UV threshold. Their real tests are independent and may be selected after
the cutoff, period, placements, motion and engineering scales. -/
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Filter Lattice RG Wilson Source Marker Multi Qlocal Quipu Quipu.Sonnet Tern Harmony
open Extra.Histories Extra.Trajectories LocalLTE.Sail MergeProof Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pressure
open scoped Classical BigOperators
variable {I : Type} [DecidableEq I] {B : Census I} {G : Gauge}

private theorem entry_at (X : Run G) {N n qd q : ℕ} (Y : Batch X.family.path N n I) (j : I)
    (ξ : I→ℕ) (w : ℝ) (hw : 0 < w) (L : ℂ →ₗ[ℝ] ℝ)
    (room : ∀ (i : ((Labels.frames G).level (Y.demand j)).Index) (e : FieldOperand (Hot.one B j) G),
      e ∈ nativeBasis (Hot.one B j) (Y.demand j) i → e.order ≤ qd ∧
        e.code.momentum ≤ Stores.till (X.alloy.B.a.clock.hatBeta N)) :
    ∃ (P : Stanza B G ξ qd) (C : ℝ), 1 ≤ C ∧ (Stanza.son P q).Allows w 1 ∧
      ∀ g, 0 < g → ∀ v : Config G (X.family.side N n), let A := Stanza.son P q
        L (Y.wavelengths j v) = C * A.wake (Hot.one B j)
          (A.short (fun _ _ _ _=>True) (Stores.till (X.alloy.B.a.clock.hatBeta N))) (Y.origin N) g v := by
  let d := Y.demand j
  let a := (X.family.S.a N:ℂ)^d
  let F := (Labels.frames G).level d
  let t := F.scaled (X.family.path.levels.clock.threshold N)⁻¹ (Y.voice j)
  let z := F.act (Y.motion j).1.ortho t
  let cut := Stores.till (X.alloy.B.a.clock.hatBeta N)
  obtain ⟨P,C,hC,hP,read⟩ := collect_channel j (nativeBasis (Hot.one B j) d) z
    (movingProbe a (Y.motion j) L) ξ qd q w hw
  refine ⟨P,C,hC,hP,?_⟩
  intro g hg v A
  rw [← read cut (Y.origin N) g v]
  change L (a * Motion.scalar _ (a⁻¹ * (localSection G d).places t 0
    (pull (Y.motion j).1 (Y.origin N j) v))) = L (a * Motion.scalar _ (a⁻¹ * _))
  rw [(localSection G d).placed_signed (sound G d)]
  simp only [affine,Signed.act_zero,zero_add]
  congr 4
  calc
    _ = ∑ i : F.Index,z i * (localSection G d).places (Pi.single i 1) (Y.origin N j) v :=
      (congrFun (places_combined X.family z (Y.origin N j)) v).trans (by rw [Finset.sum_apply]; rfl)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      rw [(basis_album (Hot.one B j) d i).choose_spec _ (Y.origin N j) q v]
      apply congrArg List.sum
      apply List.map_congr_left
      intro e he
      obtain ⟨hr,hs⟩ := room i e he
      rw [entryReading_eq _ _ _ _ _ _ _ _ _ _ hr hs hg]
      exact (e.finances w _ _ _).symm

private theorem row_read {ξ : I→ℕ} {qd q : ℕ} (A P : Stanza B G ξ qd) (s : Senses B)
    (h : A s = P s) (cut : ℕ) {c : Side} (o : I→Site c) (g : ℝ) (v : Config G c) :
    let a := Stanza.son A q
    let p := Stanza.son P q
    a.wake s (a.short (fun _ _ _ _=>True) cut) o g v = p.wake s (p.short (fun _ _ _ _=>True) cut) o g v := by
  intro a p
  simp only [Tale.notationW,Motif.story,a,p]
  let select (r : Motif.Row s G ξ qd) : Motif.Play s ξ qd := fun i e n=>True ∧ (r i e n).momentum ≤ cut
  change Motif.lyric (A s) (select (A s)) o q g v / g^(Lagger.dues ξ s.val) =
    Motif.lyric (P s) (select (P s)) o q g v / g^(Lagger.dues ξ s.val)
  rw [h]

/-- A single native unit-admitted program realizes all marked rows of an
actual physical batch under independently chosen real tests. -/
theorem joint_source_program [Fintype I] (X : Run G) (simple : G.Simple) (D : ℕ) :
    ∃ qd : ℕ, ∀ᶠ N : ℕ in atTop, ∀ (n : ℕ) (Y : Batch X.family.path N n I),
    (∀ j,Y.demand j ≤ D) → ∀ (ξ : I→ℕ) (q : ℕ) (width : ℝ), 0 < width →
    ∀ L : I→(ℂ →ₗ[ℝ] ℝ), ∃ (P : Stanza B G ξ qd) (C : I→ℝ),
      (∀ j,1 ≤ C j) ∧ (Stanza.son P q).Allows width 1 ∧
      ∀ j g, 0 < g → ∀ v : Config G (X.family.side N n), let A := Stanza.son P q
        L j (Y.wavelengths j v) = C j * A.wake (Hot.one B j)
          (A.short (fun _ _ _ _=>True) (Stores.till (X.alloy.B.a.clock.hatBeta N))) (Y.origin N) g v := by
  choose top settled using fun j : I=>physical_short_horizon (Hot.one B j) X simple D
  let qd := ∑ j,top j
  refine ⟨qd,?_⟩
  filter_upwards [eventually_all.mpr settled] with N hN
  intro n Y hd ξ q width hw L
  have fits (j : I) (i : ((Labels.frames G).level (Y.demand j)).Index) (e : FieldOperand (Hot.one B j) G)
      (he:e∈nativeBasis (Hot.one B j) (Y.demand j) i) : e.order ≤ qd ∧
      e.code.momentum ≤ Stores.till (X.alloy.B.a.clock.hatBeta N) := by
    have ok := hN j _ (hd j) i e he width
    exact ⟨ok.1.trans (Finset.single_le_sum (f:=top) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)),ok.2.1⟩
  choose each cost low pay val using fun j=>entry_at (q:=q) X Y j ξ width hw (L j) (fits j)
  let P : Stanza B G ξ qd := fun s=>each (Sonnet.root s) s
  refine ⟨P,cost,low,(Motif.chapters P q).2 (fun s=>(Motif.chapters ..).1 (pay (Sonnet.root s)) s),?_⟩
  intro j g hg v A
  rw [val j g hg v]
  congr 1
  have hr : Sonnet.root (Hot.one B j)=j := Finset.mem_singleton.mp (Classical.choose_spec (Hot.one B j).property)
  exact row_read _ _ _ (by simp only [P,hr]) _ _ _ _

end YM.Integration.FVA1Physical.Marked
