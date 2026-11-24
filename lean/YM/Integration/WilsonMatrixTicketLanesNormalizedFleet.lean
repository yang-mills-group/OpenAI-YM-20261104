import YM.Agora26.Marks.Tail

/-! The complete marked density of the upper Wilson fields on the intermediate lattice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesNormalizedFleet

open OPE Strobe Yarn Vista26 Function Filter Set MeasureTheory Finset Lattice Wilson RG Push
open Marker Source Extra.Histories Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi
open Motion Local Bid Cells Overlay MergeProof Accent Ribbons ManyCopies MergeProof.Float
open PhysicalNext.Repeat Lotus Legato Mallow Bandage Patrol Loom Vitrines GridApprox
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {I : Type} [Fintype I] [DecidableEq I] {G : Gauge} {C : Family G}
variable {k m N p : ℕ} {W r D} {σ χ : ℕ → ℝ} (H : Tune C W r D σ χ)

def density (C : Family G) (m N p k : ℕ) (hk : k ≤ N)
    (F : I → Config G (C.side N p) → ℂ) :=
  gust C.path N p N (birth (Names (Site (C.side m p)) I) (C.path.rep N p N)
    ((royal C m p N).calls F)) k hk

def Measured (C : Family G) (m N p k : ℕ) (hk : k ≤ N)
    (d : I → ℕ) (v : (i : I) → C.label (d i))
    (o : I → ∀ j : ℕ, Site (C.side j p)) (y : I → ℝ) : Prop :=
  ∃ S : I → Lamp G (C.side k p),
    Fleet (royal C m p k) (C.path.rep N p k)
      (density C m N p k hk (fun i => C.O N p (v i) (o i N)))
      (fun i => o i k) S y ∧
    ∀ i, (S i).watch = indexX C (d i) N p (v i) (o i) (1,false) k ∧
      (S i).rays (C.path.rep N p k) = Ktone C (d i) N p (v i) (o i) (1,false) k

include H
theorem registered (d : I → ℕ) (v : (i : I) → C.label (d i))
    (o : I → ∀ j : ℕ, Site (C.side j p)) (band : Band C o r k N m)
    (lower : m ≤ k) (live : k < N) (zero : C.ref 0 < k) (refs : ∀ i, C.ref (d i) ≤ k)
    (crowd : Occupancy ((royal C m p N).place (fun i => o i N)) (r N))
    (along : ∀ a i, k ≤ i → i < N → o a (i+1) = (C.path.levels.clock.op i p).ratio.embed (o a i))
    {ρ : ℝ} (fee : ∀ i, Spindle.paid C (d i) k N p (v i) ≤ ρ)
    {w y : I → ℝ} (wp : ∀ i, 0 < w i) (initial : ∀ i, w i * ρ ≤ fly C.path.levels (d i) k)
    (yp : ∀ i, 0 < y i)
    (lift : Repegs ((royal C m p k).place (fun i => o i k)) (C.path.levels.budget k).B
      (fun j => renal C.path.levels k * (near C.path.levels k * w j.snd)) (y ∘ Prod.snd)
      (1/2) 1 (Names (Site (C.side m p)) I)) :
    Measured C m N p k live.le d v o y := by
  choose M lyrics using fun i => Yarn.curtain H (p := p) (refs i) live.le
  let u i := (C.factory (d i) N p).terminal.symm (v i)
  let march i := stair (near C.path.levels) (w i) k
  choose S drive outer parts using fun i => Yarn.first_wish H (o i) (along i)
    (lyrics i) (refs i) live.le (wp i) (show w i * bond C.path N p (M i) k (u i) ≤ _ by
      unfold u
      rw [Yarn.bond_paid (refs i) live.le (lyrics i)]
      exact (mul_le_mul_of_nonneg_left (fee i) (wp i).le).trans (initial i))
  let F i := C.O N p (v i) (o i N)
  have patent i : Patent C N p (o i N) (S i N) (F i) (march i N) := by
    have h := outer i
    rw [show (C.factory _ N p).terminal (u i) = v i from LinearEquiv.apply_symm_apply _ _] at h
    exact h
  let Q := birth (Names (Site (C.side m p)) I) (C.path.rep N p N) ((royal C m p N).calls F)
  have born := Yarn.rosate (x := F) H (lower.trans live.le) crowd
    (fun i => H.protectors _ (wp i) k N) patent
  have upper := run_car H band lower zero live (le_refl N) born drive
    (fun a i _ _ => H.protectors _ (wp a) k i)
    (fun i hi _ _ => (H.fall_march hi.le).symm.le) k.lt_succ_self live
  let parent := (C.path.levels.clock.op k p).ratio.parent
  have clock : parent ∘ (fun i => o i (k+1)) = (fun i => o i k) :=
    funext fun i => band.clock k le_rfl live i
  have pegged : Repegs ((royal C m p k).place (fun i => o i k)) (C.path.levels.budget k).B
      (fun j : Site (C.side m p) × I => renal C.path.levels k * march j.2 (k+1))
      (y ∘ Prod.snd) (1/2) 1 (Names (Site (C.side m p)) I) := by
    unfold march
    simp_rw [H.fall_march (Nat.le_refl k), H.anchor_march (wp _)]
    exact lift
  refine ⟨fun i => S i k, ?_, ?_⟩
  · change Fleet _ _ (gust C.path N p N Q k live.le) _ _ _
    rw [gust_step C.path N p N Q live, ← clock]
    exact Fleet.steady (w := fun i => march i (k+1)) _ H.seed.wilson live H.thor zero.le
      ((climbR (C := C) (p := p) lower).symm ▸ upper.fleet)
      (clock.symm ▸ band.crowd k le_rfl live) (fun i => (drive i).drives k le_rfl live)
      yp (clock.symm ▸ pegged)
  · intro i
    have entry : ((M i).tone k).plays (u i) = parcel C (d i) k N p (v i) := by
      unfold parcel
      rw [(lyrics i).entries]
      rfl
    obtain ⟨regular,hard⟩ := parts i k le_rfl live.le
    constructor
    · rw [regular]
      unfold soarF indexX
      rw [entry]
    · rw [hard]
      unfold soarK Ktone
      rw [entry]


end YM.Integration.WilsonMatrixTicketLanesNormalizedFleet
end
