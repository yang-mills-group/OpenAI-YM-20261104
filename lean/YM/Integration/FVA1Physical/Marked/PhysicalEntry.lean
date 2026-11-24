import YM.Integration.FVA1Physical.Marked.StencilEntry

/-! Exact expansion of the actual bare field into admitted native wallet
readings at its actual marked site. Signed lattice reorientation is absorbed
into the prescribed action on field columns, before any field is read. -/
set_option autoImplicit false
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.FVA1Physical.Marked
open Filter Lattice RG Wilson Source Marker Multi Qlocal Quipu Quipu.Sonnet Tern Harmony
open Extra.Histories Extra.Trajectories LocalLTE.Sail MergeProof Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pressure
open scoped Classical BigOperators
variable {I : Type} [DecidableEq I] {B : Census I} {G : Gauge}

private theorem solo_single (i : I) {k : ℕ} (a : Vase (Hot.one B i) G k)
    {c : Side} (o : I→Site c) (q : ℕ) (v : Config G c) :
    Conductor.solo a o q v = a.read (o i) q v := by
  let s := Hot.one B i
  have root : Sonnet.root s=i := Finset.mem_singleton.mp (Classical.choose_spec s.property)
  have hear : a.stage.Hears o := by
    intro j hj
    have hj' : j=i := Finset.mem_singleton.mp hj
    have st := a.stage.starts
    change a.stage.pursue (Sonnet.root s)=0 at st
    rw [root] at st
    rw [hj',root,st]
    simp [Lasso.bent]
  rw [Conductor.solo,if_pos hear,root]

def entryReading (i : I) (e : FieldOperand (Hot.one B i) G) (ξ : I→ℕ)
    (qd cut q : ℕ) (w g : ℝ) {c : Side} (o : I→Site c) (v : Config G c) : ℝ :=
  if he:e.order≤qd then
    let A := Stanza.son (fieldBook ξ e he w) q
    A.wake (Hot.one B i) (A.short (fun _ _ _ _=>True) cut) o g v
  else 0

theorem entryReading_eq (i : I) (e : FieldOperand (Hot.one B i) G) (ξ : I→ℕ)
    (qd cut q : ℕ) (w g : ℝ) {c : Side} (o : I→Site c) (v : Config G c)
    (he : e.order≤qd) (hc : e.code.momentum≤cut) (hg : 0<g) :
    entryReading i e ξ qd cut q w g o v = (e.unit w).read (o i) q v := by
  rw [entryReading,dif_pos he,fieldBook_read ξ e qd he w cut q hc o g hg v,solo_single]

omit [DecidableEq I] in
private theorem real_location (X : Run G) {N n : ℕ} (Y : Batch X.family.path N n I) (j : I)
    (v : Config G (X.family.side N n)) :
    let d := Y.demand j
    let a := (X.family.S.a N:ℂ)^d
    let F := (Labels.frames G).level d
    let z := F.act (Y.motion j).1.ortho (F.scaled (X.family.path.levels.clock.threshold N)⁻¹ (Y.voice j))
    Y.wavelengths j v = a * Motion.scalar (Y.motion j) (a⁻¹ *
      ∑ i : F.Index,z i * (localSection G d).places (Pi.single i 1) (Y.origin N j) v) := by
  intro d a F z
  let w := F.scaled (X.family.path.levels.clock.threshold N)⁻¹ (Y.voice j)
  change a * Motion.scalar _ (a⁻¹ * (localSection G d).places w 0
    (pull (Y.motion j).1 (Y.origin N j) v)) = _
  rw [(localSection G d).placed_signed (sound G d)]
  simp only [affine,Signed.act_zero,zero_add]
  congr 3
  exact (congrFun (places_combined X.family z (Y.origin N j)) v).trans (by rw [Finset.sum_apply]; rfl)

/-- A finite field horizon admits a single rank and true UV cutoff. Every
rotated or translated independently chosen physical source of that horizon
then reads exactly as a finite sum of native short, unit-admitted stanza
outputs evaluated on the *original configuration* at the source site. -/
theorem physical_entry_program (X : Run G) (simple : G.Simple) (D : ℕ) (j : I) :
    ∃ qd : ℕ, ∀ᶠ N : ℕ in atTop, ∀ (n : ℕ) (Y : Batch X.family.path N n I),
      Y.demand j ≤ D → ∀ (ξ : I→ℕ) (q : ℕ) (width g : ℝ), 0<g →
      ∀ v : Config G (X.family.side N n),
      let d := Y.demand j
      let a := (X.family.S.a N:ℂ)^d
      let F := (Labels.frames G).level d
      let z := F.act (Y.motion j).1.ortho (F.scaled (X.family.path.levels.clock.threshold N)⁻¹ (Y.voice j))
      let cut := Stores.till (X.alloy.B.a.clock.hatBeta N)
      Y.wavelengths j v = a * Motion.scalar (Y.motion j) (a⁻¹ *
        ∑ i : F.Index,z i * ((nativeBasis (Hot.one B j) d i).map
          (fun e=>(e.factor * (e.room width:ℂ)) * (entryReading j e ξ qd cut q width g (Y.origin N) v : ℂ))).sum) := by
  obtain ⟨qd,hq⟩ := physical_short_horizon (Hot.one B j) X simple D
  refine ⟨qd,?_⟩
  filter_upwards [hq] with N hh
  intro n Y hd ξ q width g hg v d a F z cut
  rw [real_location X Y j v]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [(basis_album (Hot.one B j) d i).choose_spec _ (Y.origin N j) q v]
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  have ok := hh d hd i e he width
  rw [entryReading_eq _ _ _ _ _ _ _ _ _ _ ok.1 ok.2.1 hg]
  exact (e.finances width _ _ _).symm
end YM.Integration.FVA1Physical.Marked
