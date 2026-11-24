import YM.Integration.WilsonOriginalNullPlacedFiling
import YM.Integration.WilsonOriginalNullPlacedRough
import YM.Integration.WilsonCapturedWindingCharge
import YM.Integration.WilsonOriginalNullPrimaryFees

/-! At a general fine site the same Wilson fare applies. Its primary input
in a zero-germ source is a genuine wrapped tail, even after the real
engineering and loan multipliers have been paid. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalNullPlacedReserve
open Function Filter Lattice RG Wilson Extra.Histories Source Labels Bid
open Extra.Histories.Relay Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Address
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G)
local notation "C₀" => R.family

theorem currency (i:ℕ) : 0 ≤  R.y (R.alloy.B.a.clock.J (i+1)) ∧
    R.y (R.alloy.B.a.clock.J (i+1)) ≤  stock C₀ (i+1) := by
  let j:=R.alloy.B.a.clock.J (i+1)
  let c:=R.y j
  let σ:=stock C₀ (i+1)
  let k:=R.w.K (j+1)
  have book:=R.b.clock.fits (C₀).path rfl i 0 (Nat.zero_le _)
  have c0:0 ≤ c:=zero_le_one.trans book.cost
  have s0:0 ≤ σ:=zero_le_one.trans ((C₀).path.levels.params (i+1)).columns_ge
  have η0:0 ≤ Doors.rate (R.alloy.B.a.S.block i):=(Doors.rate_pos _).le
  have bound:c ≤ R.w.K j:= (le_add_of_nonneg_right (mul_nonneg η0 s0)).trans
    ((le_mul_of_one_le_right (add_nonneg c0 (mul_nonneg η0 s0)) (Motion.orbitCost_one_le _)).trans book.funds)
  have increment:R.w.K j ≤ k:=R.w.growth (Nat.le_succ j)
  have room:64*k^2  ≤  σ:= R.b.clock.room (i+1)
  have floor:1 ≤ k:=R.w.prices _
  exact ⟨c0,(bound.trans increment).trans (by nlinarith only [room,floor,sq_nonneg (k-1)])⟩

variable (d:ℕ)
theorem wrapped (simple:G.Simple) : ∀ᶠ i:ℕ in atTop, ∀ p:ℕ,
    (factor C₀ i)^d*R.y (R.alloy.B.a.clock.J (i+1))*invoice (C:=C₀) d (i+1) p  ≤ 
      Doors.rate (R.alloy.B.a.S.block i) := by
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (WilsonCapturedWindingCharge.tariff R d simple ((d:ℝ)+1))] with i issued
  intro p
  let l:=factor C₀ i
  let c:=R.y (R.alloy.B.a.clock.J (i+1))
  let s:=(C₀).S.scale (i+1)
  let inv:=invoice (C:=C₀) d (i+1) p
  have lp:0<l:=zero_lt_one.trans (factor_positive C₀ i)
  have one:1 ≤ l:=(factor_positive C₀ i).le
  have inv0:0 ≤ inv:=invoice_nn (C:=C₀) d p (i+1)
  have cap:c ≤ 1+4*stock C₀ (i+1):=by
    have limits:=currency R i;have paid:0 ≤ stock C₀ (i+1):=limits.1.trans limits.2
    change R.y (R.alloy.B.a.clock.J (i+1))  ≤  _;linarith only [limits.2,paid]
  have paid:c*inv ≤ Real.exp (-((d:ℝ)+1)*s):=by
    calc
      _ ≤ (1+4*stock C₀ (i+1))*inv := mul_le_mul_of_nonneg_right cap inv0
      _ = inv*(1+4*stock C₀ (i+1)) := mul_comm _ _
      _ ≤ _ := issued p
  have clock:Real.log l  ≤ s:=(Real.log_le_iff_le_exp lp).mpr (WilsonOriginalNullPrimaryFees.forecast R i).2
  have tiny:Real.exp (-((d:ℝ)+1)*s)  ≤  l^(-((d:ℝ)+1)):=by
    rw [Real.rpow_def_of_pos lp]
    apply Real.exp_monotone
    simpa only [mul_comm (Real.log l)] using
      mul_le_mul_of_nonpos_left clock (neg_nonpos.mpr (add_nonneg (Nat.cast_nonneg d) zero_le_one))
  calc
    _ = (l^d)*(c*inv) := by ring
    _  ≤  l^(d:ℝ)*l^(-((d:ℝ)+1)) := by rw [Real.rpow_natCast];exact mul_le_mul_of_nonneg_left (paid.trans tiny) (pow_nonneg lp.le _)
    _ = l^(-(1:ℝ)) := by rw [←Real.rpow_add lp];congr 1;ring
    _  ≤  l^(-(2/5:ℝ)) := Real.rpow_le_rpow_of_exponent_le one (by norm_num)
    _ = _ := rfl

theorem original (simple:G.Simple) : ∀ᶠ i:ℕ in atTop, ∀ N p, ∀ _:i<N, ∀ _:Opened C₀ d (i+1) p,
      ∀ (y:Site ((C₀).side (i+1) p)) (q:Coefficient ((C₀).labels.level d) ((C₀).side (i+1) p))
        (B:ℝ), let U:=(C₀).path.rep N p (i+1)
      q.Format y (C₀).params U → q.remBound y U (safety C₀ (i+1)) B →
      projection ((C₀).labels.level d) (C₀).params U.p.threshold y q=0 →
      WilsonOriginalNullPlacedRough.fare R d i (((C₀).labels.level d).coeffSize q.x) B ≤ 
        2*Doors.rate (R.alloy.B.a.S.block i)*B := by
  filter_upwards [wrapped R d simple] with i paid
  intro N p live home y q B U form fund null
  let move:=Tour.placard C₀ R.makes N p live (-y)
  let z:=Drift.stamp (-y) move q
  have rz:reads (C:=C₀) d N p (i+1) z B:=by
    refine ⟨?_,?_⟩
    · simpa only [add_neg_cancel] using Drift.stamp_format (-y) move q form
    · have f:=Drift.stamp_rem (-y) move q fund;rw [add_neg_cancel] at f;exact f
  have vac:U.p=(C₀).path.levels.budget (i+1):= (R.makes.wilson.represents N p (i+1) live).vac
  have pz:page (C:=C₀) d p (i+1) z=0:=by
    change projection ((C₀).labels.level d) (C₀).params ((C₀).path.levels.budget (i+1)).threshold 0 z=0
    rw [←vac]
    have rel:=WilsonOriginalNullRelocation.page ((C₀).labels.level d) (C₀).params U.p.threshold y (-y) move q
    rw [add_neg_cancel] at rel
    exact rel.trans null
  have localbill:=measured_diff (C:=C₀) d N p (i+1) R.makes home.post live rz
  rw [pz,zero_sub,count_neg] at localbill
  have B0:0 ≤ B:=by obtain ⟨a,b,ha,hb,h0,-⟩:=fund;linarith only [ha,hb,h0]
  have c0:0 ≤ (factor C₀ i)^d*R.y (R.alloy.B.a.clock.J (i+1)):=
    mul_nonneg (pow_nonneg (zero_lt_one.trans (factor_positive C₀ i)).le _) (currency R i).1
  have h:=mul_le_mul_of_nonneg_left localbill c0
  rw [←mul_assoc] at h
  have h':=(h.trans (mul_le_mul_of_nonneg_right (paid p) B0))
  calc
    _  ≤  Doors.rate (R.alloy.B.a.S.block i)*B+Doors.rate (R.alloy.B.a.S.block i)*B := add_le_add h' le_rfl
    _ = _ := by ring

end YM.Integration.WilsonOriginalNullPlacedReserve
