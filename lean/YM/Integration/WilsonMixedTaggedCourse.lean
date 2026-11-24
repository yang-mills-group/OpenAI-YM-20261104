import YM.Integration.WilsonMixedTaggedRoster
import YM.Integration.WilsonMixedTaggedNaturality
import YM.RG05Readout.Many.Film

/-! Fund the doubled roster and commute both actual coalescing replays with
the same originals. No count of the alternative fine roots is used. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedCourse
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker RG05Readout
open RG05Readout.Many Address Native View Bid Pressure Copper
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open WilsonMixedTaggedRoster
open scoped BigOperators Classical

variable {G : Gauge} {C : Family G} {n p b m N k d : ℕ}
variable {W : Type} [Fintype W] [DecidableEq W]
variable (o : W → Site (C.side n p)) (g : W → Motion)
section funding
set_option quotPrecheck false
local notation "Z" => C.path.levels
local notation "P" => planner (Mine.tree o g)

theorem toured (H : ∀ i,Census (ManyStem C o i)) {f : ℕ → ℝ} (hb : n ≤ b)
    (room : Fintype.card W*2 ≤ (Z).clock.J n)
    (loss : ∀ i,b ≤ i → i < m → f i ≤ f (i+1)*(((Z).clock.hatBeta i)^(3*k+4))⁻¹) :
    Toured P (fun i=>census (H i)) hb m f k := by
  have base : Occupancy o (Fintype.card W) := fun _=>Finset.card_le_univ _
  have today i (hi : n ≤ i) : Occupancy ((P).supportX i) (Fintype.card W*2) :=
    occupancy (keep_occ o g hi base)
  have levels i (hi : n ≤ i) : Fintype.card W*2 ≤ (Z).clock.J (i+1)+2 :=
    (room.trans ((Z).fits.mono (hi.trans i.le_succ))).trans (Nat.le_add_right _ _)
  refine ⟨fun i hi _ y=>?_,fun i hi _ y=>?_,fun i hi hm=>.straight (loss i hi hm)⟩
  · exact (Planner.pays P (today i (hb.trans hi)) (hb.trans hi) y).trans
      (Nat.mul_le_mul_right _ (levels i (hb.trans hi)))
  · exact (today (i+1) ((hb.trans hi).trans i.le_succ) y).trans
      ((levels i (hb.trans hi)).trans
        (Nat.le_mul_of_pos_right _ (pow_pos (C.S.block i).property _)))

omit [DecidableEq W] in
theorem room_eventually {ι : Type*} {l : Filter ι} {j : ι → ℕ} (hj : Tendsto j l atTop) :
    ∀ᶠ a in l, Fintype.card W*2 ≤ C.path.levels.clock.J (j a) :=
  (C.path.levels.fits.deep.comp hj).eventually_ge_atTop _

end funding

section replay
set_option quotPrecheck false
variable {V : ℕ → Type} [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)] {W' : Type*}
variable (A : Planner C p n V W') {H : ∀ i,Census (V i)} (s : W' → ℕ)
variable (z : ℂ)
local notation "π" => fun i=>feed (fun v:V i × Bool=>if v.2 then z else 1) (project (H i))
local notation "Aₜ" => planner A
local notation "Hₜ" => fun i=>census (H i)

theorem downhill {i : ℕ} (hi : n ≤ i) (hL : License (H i) (H (i+1)) (Prod.fst ∘ A.narrows i hi))
    (F : Config G (C.side (i+1) p) → Poly (census (H (i+1))))
    (hF : Integrable F (prior G _)) (U : Config G (C.side i p)) :
    (π i) (downdraft (N:=N) Aₜ Hₜ s i hi (step_license A hL) F U) =
      downdraft (N:=N) A H s i hi hL (fun X=>(π (i+1)) (F X)) U := by
  let K:=C.path.levels.clock.op i p
  let β:=(C.path.rep N p (i+1)).beta
  have hp : K.push β (fun X=>(π (i+1)) (F X)) U = (π (i+1)) (K.push β F U) :=
    congrFun (amp_live (π (i+1)).toLinearMap K hF (C.path.levels.transition_mass i p β)) U
  unfold downdraft
  rw [hp]
  apply WilsonMixedTaggedNaturality.square
  · intro x
    rfl
  · intro x
    exact mul_comm _ _

theorem replay {hb : n ≤ b} (hm : m ≤ N)
    (license : ∀ i,∀ hi:b ≤ i,i < m → License (H i) (H (i+1)) (Prod.fst ∘ A.narrows i (hb.trans hi)))
    {F : ∀ i, Config G (C.side i p) → Poly (census (H i))}
    (r : Replay Aₜ s hb m F N) (hF : Integrable (F m) (prior G _)) :
    Replay A s hb m (fun i U=>(π i) (F i U)) N := by
  constructor
  intro i hi hmi _
  obtain ⟨_,hr⟩ := r.downhill (V:=fun i=>V i × Bool) i hi hmi
  let hl:=license i hi hmi
  refine ⟨hl,?_⟩
  funext U
  rw [hr]
  exact downhill A s z (hb.trans hi) hl _ (r.live Aₜ s hb hF hm (hi.trans i.le_succ) hmi) U

end replay
end YM.Integration.WilsonMixedTaggedCourse
