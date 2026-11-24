import YM.Integration.WilsonMixedTaggedFields

/-! Rebook the genuinely filed finite palette at a later date. Its complete
physical column at every date and its singleton rows are unchanged. The
larger wallet comes from the original inverse spine cost. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestRebook
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Many RG05Readout.Address RG05Readout.Native RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Next.Rank.Station
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat Lotus Legato Bandage
open scoped BigOperators Classical

variable {G : Gauge} {C : Family G} {d n m t per N : ℕ}
  {D : Address.Rail C} {h : C.Makes} {B : ℕ → ℕ → ℝ}

theorem pointAt (S : Emblems C d) (x : Palette C d) (m t i : ℕ) :
    point S (point S x m t) t i = point S x m i := by
  by_cases it : i ≤ t
  · induction it using Nat.decreasingInduction with
    | self => exact point_here
    | of_succ j jt ih =>
      exact (nearpoints (m:=t) S (point S x m t) j).symm.trans
        ((congrArg (S j) ih).trans (nearpoints (m:=m) S x j))
  · have ti : t ≤ i := by omega
    clear it
    induction i,ti using Nat.le_induction with
    | base => exact point_here
    | succ j tj ih =>
      apply (S j).injective
      exact (nearpoints (m:=t) S (point S x m t) j).trans (ih.trans (nearpoints (m:=m) S x j).symm)

private theorem string (mt : m ≤ t) : stringCost C mt ≤ C.S.a m/C.S.a t := by
  induction t,mt using Nat.le_induction with
  | base => rw [string_base,div_self (C.S.a_pos _).ne']
  | succ j mj ih =>
    rw [string_next mj]
    calc _ ≤ ((C.S.block j).val:ℝ)*(C.S.a m/C.S.a j) :=
            mul_le_mul (lamp_head (C:=C) j) ih (zero_le_one.trans (stampCosts mj)) (by positivity)
         _ = _ := by rw [Schedule.a_step];field_simp

theorem sizeAt {S : Emblems C d} {P : Sight C d per} (spine : Spine D B h n per d N P S)
    (nm : n ≤ m) (mt : m ≤ t) (tN : t ≤ N) {x : Palette C d} {Q : ℝ} (old : size x ≤ Q) :
    size (point S x m t) ≤ Q*(C.S.a m/C.S.a t) := by
  rw [weave_fine mt]
  have sizePos : 0 ≤ size x := Finset.sum_nonneg fun _ _ => norm_nonneg _
  exact (spine.inverse_cost nm mt tN x).trans ((mul_le_mul (string (C:=C) mt) old sizePos
    (div_nonneg (C.S.a_pos m).le (C.S.a_pos t).le)).trans_eq (mul_comm _ _))

variable {W : Type} (s : W → ℕ)
  (S : (v:W) → Emblems C (s v)) (x : (v:W) → Palette C (s v))

def raised (m t : ℕ) (v : W) : Palette C (s v) := point (S v) (x v) m t

theorem launch (m t : ℕ) :
    Launch (m:=t) s S (raised s S x m t) = Launch (m:=m) s S x := by
  funext v j
  exact pointAt _ _ _ _ _

theorem singleton (P : (v:W) → Sight C (s v) per) (m t : ℕ) :
    plants (m:=t) s P S (raised s S x m t) = plants (m:=m) s P S x := by
  unfold plants
  rw [launch]

theorem columns (o : W → Site (C.side n per)) (E : W → Motion) (q : ManyStem C o n → Body)
    (m t N : ℕ) :
    WilsonMixedTaggedFields.columns o E s q S (raised s S x m t) t N =
      WilsonMixedTaggedFields.columns o E s q S x m N := by
  unfold WilsonMixedTaggedFields.columns
  rw [launch]

end YM.Integration.WilsonAllDateHarvestRebook

