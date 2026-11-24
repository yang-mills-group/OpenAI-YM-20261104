import YM.WiderProfiles.Reversion
import YM.FVA2.Scale.N
/-!
# WiderProfiles, C1.w

An estimate for the whole widening family on the original Front. Includes
ALL Sized layouts with the stated sep and extent; constants and onsets may
depend on the clearance, polynomial extent data, finite field horizon, arity,
order, labels and fixed prescription inputs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.WiderProfiles
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.Land MS.Menus MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus
open scoped Topology BigOperators

variable {n a d k : ℕ} {G : Gauge} {c D : ℝ}
open Real

lemma absorb {E : Type*} [NormedAddCommGroup E]
    {x : Domain n a c D → E}
    (h : Price (along n a c D) (fun i => Arrival.Schedule.theta (grab i.val)) mildG x) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ i in along n a c D,
      ‖x i‖ ≤ C * i.val.F.spacing^(mildG/2) := by
  obtain ⟨C, hC, j, hj⟩ := h
  let T := fun i : Domain n a c D => Arrival.Schedule.theta i.val.F
  let r := mildG/2
  have hr : 0 < r := half_pos mild_p
  have ht : Tendsto T (along n a c D) atTop := trial_vanish 0 n a c D
  have he : ∀ᶠ i in along n a c D, (1+T i)^j * exp (-r * T i) ≤ 1 :=
    ((exp_keep _ hr j 1).comp ht).eventually (ge_mem_nhds zero_lt_one)
  refine ⟨C, hC, ?_⟩; filter_upwards [hj, he] with i hi hi'
  apply hi.trans; rw [← height_cost i.val i.property.sized]
  change C * (1 + T i)^j * exp (-mildG*T i) ≤ C * exp (-r*T i)
  calc
    _ = C * (((1 + T i)^j * exp (-r*T i)) * exp (-r*T i)) := by
      rw [show -mildG*T i = -r*T i + -r*T i by unfold r; ring, Real.exp_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_of_le_one_left (Real.exp_pos _).le hi') hC.le

variable (ν : ℝ) (Y : XSpace.Initialize G) {V : Normalize.Store G} (K : Rose.Pick V)
    (A : Prescription (Press.portDeck G)) {O : Booked (Press.portDeck G)} (S : MS_Data G O)
    (h : G.Simple) (hs : TaylorOKF S (Press.wickInput Y) A)
    (hr : Position.Favors.Horder A) (hu : Position.Ace.UnitP A)
include ν h hs hr hu

theorem start_bond (a : ℕ) (hc : 0 < c) (hD : 1 ≤ D) (k : ℕ) (p : Tags G d n) :
    Costing (fun i : Domain n a c D => Rose.measureₓ Y K d i.val k p)
      (fun i => Scale.Measure.start Y K d n ⟨familiar i.val, i.property.conf hc⟩ k p) := by
  rw [← Scale.Measure.together Y K ν S A h hs hr hu]
  exact rate_bond ν Y K A S h hs hr hu a hc hD k p

/-- Section F, C1.w. The configuration inhabits `Scale.Stage n` by the actual separation.
On `Sized`, `Arrival.Schedule.theta m = - log m.spacing`. The RHS book is `G^P`
of §B, not `G^X` (obtained after homogeneous adjustment). The rate costs
`MS.Tide.mildG/2`. No fixed compact in the hypotheses. -/
theorem widerProfiles (d n k a : ℕ) (c D : ℝ) (hc : 0 < c) (hD : 1 ≤ D)
    (p : Tags G d n) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m in Front, ∀ s : Sample n, grab s=m → ∀ hy : Admits a c D s,
      ‖Rose.measureₓ Y K d s k p - Scale.Measure.start Y K d n ⟨familiar s, hy.conf hc⟩ k p‖ ≤
        C * m.spacing^(mildG/2) := by
  obtain ⟨C,hC,hq⟩ := absorb (start_bond ν Y K A S h hs hr hu a hc hD k p).delta
  refine ⟨C,hC,?_⟩
  rw [along,eventually_comap] at hq
  filter_upwards [hq] with m hm s he hy
  subst m; exact hm ⟨s,hy⟩ rfl
end YM.FVA2.WiderProfiles
