import YM.Integration.WilsonMatrixTicketLengths

/-! Elect the manuscript's eventually divisible powers of three on the original sheet,
with every prior floor and field-frame purchase. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramLengths
open OPE OPE.Owl
open Function Filter Lattice Laurent RG Pressure Tree Precision Wilson Org RG.Supply Input
open PhysicalNext PhysicalNext.Repeat Legato Graces Roost PhysicalNext.Repeat.Aroma
open ConnectedActivityE6 Shell Channel Push.PriceCompiler Lass Zest
open Next.Free Woody Votive CardinalQ Stroke Stroke.MatchZ
open PhysicalNext.ThroughLaunch Next.Foundations
open scoped BigOperators Classical Topology
variable {G : Gauge} {S : Sheet G} {C : ChartRatio G} {H : Sponsor G} {T : Seasons H}
    {ratio : LocalRatio C} {book : PriceBook ratio T} {a : Axis} {simple : G.Simple}

/-- At every stage the chosen exponent is a multiple of the previous factorial. -/
def Divisible (P : Rolls S) : Prop := ∀ n : ℕ, ∃ e : ℕ,
  P.L n = (3 : Side)^((n+1).factorial * e)

private theorem side (D : Desk S book a simple) (n j : ℕ) : ∃ L : Side, j ≤ L.val ∧
    Large S n L ∧ (∃ e : ℕ, L = (3 : Side)^((n+1).factorial * e)) ∧
    ∀ i ≤ n, ∃ m : ℕ, L = (D.stream i).pay.st.S.L ^ m := by
  let frames := ∏ i ∈ Finset.range (n+1), (D.stream i).pay.st.J
  have pos (i : ℕ) : 0 < (D.stream i).pay.st.J := by
    have h := (D.stream i).pay.st.S.coarse
    rw [(D.stream i).pay.st.crisp] at h
    by_contra! zero
    rw [Nat.le_zero.mp zero,pow_zero] at h
    exact (by decide : ¬ 3 ≤ (1 : Side).val) h
  let e := (n+1).factorial * frames
  have pe : 0 < e := Nat.mul_pos (Nat.factorial_pos _) (Finset.prod_pos fun i _ => pos i)
  let base : Side := (3 : Side)^e
  have legal : 3 ≤ base.val := by
    change 3 ≤ ((3:Side)^e).val
    rw [PNat.pow_coe,show (3:Side).val=3 by rfl]
    exact le_self_pow₀ (by decide) (Nat.ne_zero_of_lt pe)
  have odd : Odd base.val := by
    change Odd (((3:Side)^e).val)
    rw [PNat.pow_coe,show (3:Side).val=3 by rfl]
    exact Odd.pow (by decide : Odd (3:ℕ))
  let B : Patch := ⟨base,5,by decide,legal,odd⟩
  obtain ⟨floor,large⟩ := Supply.Rolls.eventually_large S simple n
  obtain ⟨k,hk,hodd,_⟩ := widens B (max j floor)
  refine ⟨base^k,(le_max_left ..).trans hk,large _ ((le_max_right ..).trans hk) hodd,
    ⟨frames*k,?_⟩,fun i hi => ?_⟩
  · change ((3:Side)^((n+1).factorial*frames))^k=_
    rw [←pow_mul,Nat.mul_assoc]
  · obtain ⟨t,ht⟩ := Finset.dvd_prod_of_mem (fun i => (D.stream i).pay.st.J)
      (Finset.mem_range.mpr (show i < n+1 by omega))
    change frames = _ at ht
    refine ⟨(n+1).factorial*t*k,?_⟩
    change ((3:Side)^((n+1).factorial*frames))^k=_
    rw [ht,(D.stream i).pay.st.crisp,←pow_mul,←pow_mul]
    congr 1
    ring

theorem elect (D : Desk S book a simple) : ∃ P : Rolls S, FrameBill D P ∧ Divisible P := by
  choose u grows paid powers enrolled using side D
  let A : ℕ → Side := fun i => Nat.rec (u 0 0) (fun j (v:Side) => u (j+1) v.val) i
  have monotone : Monotone fun i => (A i).val := monotone_nat_of_le_succ (fun _ => grows ..)
  have accepted (n : ℕ) : Large S n (A n) := by cases n <;> apply paid
  refine ⟨⟨A,accepted,monotone⟩,⟨fun n i h => ?_⟩,fun n => ?_⟩
  · have hi := (D.stretch i).trans h
    cases n <;> apply enrolled _ _ i hi
  · cases n <;> apply powers

theorem eventual {P : Rolls S} (h : Divisible P) {d : ℕ} (hd : 0 < d) :
    ∀ᶠ n in atTop, ∃ e : ℕ, P.L n = ((3:Side)^d)^e := by
  filter_upwards [eventually_ge_atTop d] with n hn
  obtain ⟨e,he⟩ := h n
  obtain ⟨m,hm⟩ := Nat.dvd_factorial hd (Nat.le_succ_of_le hn)
  exact ⟨m*e,by rw [he,hm,pow_mul,pow_mul,pow_mul]⟩

end YM.Integration.WilsonPositionProgramLengths
end
