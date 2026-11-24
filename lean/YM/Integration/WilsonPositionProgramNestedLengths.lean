import YM.Integration.WilsonPositionProgramLengths

/-! A single choice of original Wilson lengths permits exact finite infrared closure. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramNestedLengths
open OPE OPE.Owl
open Function Filter Lattice Laurent RG Pressure Tree Precision Wilson Org RG.Supply Input
open PhysicalNext PhysicalNext.Repeat Legato Graces Roost PhysicalNext.Repeat.Aroma
open ConnectedActivityE6 Shell Channel Push.PriceCompiler Lass Zest
open Next.Free Woody Votive CardinalQ Stroke Stroke.MatchZ
open PhysicalNext.ThroughLaunch Next.Foundations
open scoped BigOperators Classical Topology
variable {G : Gauge} {S : Sheet G} {C : ChartRatio G} {H : Sponsor G} {T : Seasons H}
    {ratio : LocalRatio C} {book : PriceBook ratio T} {a : Axis} {simple : G.Simple}

def Nested (P : Rolls S) : Prop := ∃ h : ℕ → ℕ, Monotone h ∧
  ∀ n, n+1 ≤ h n ∧ P.L n=(3:Side)^(h n).factorial

private theorem power_large (s : ℕ) (hs : 0 < s) : s ≤ ((3:Side)^s.factorial).val := by
  have h₁ := Nat.le_of_dvd (Nat.factorial_pos s) (Nat.dvd_factorial hs (le_rfl (a:=s)))
  change s ≤ (3:ℕ)^s.factorial
  exact (h₁.trans (show s.factorial < 2^s.factorial from Nat.lt_two_pow_self).le).trans
    (Nat.pow_le_pow_left (by decide : 2 ≤ 3) _)

private theorem stage (D : Desk S book a simple) (n : ℕ) : ∃ b : ℕ, n+1 ≤ b ∧
    ∀ h ≥ b, Large S n ((3:Side)^h.factorial) ∧
      ∀ i ≤ n, ∃ m : ℕ, (3:Side)^h.factorial=(D.stream i).pay.st.S.L^m := by
  let f := fun i => (D.stream i).pay.st.J
  obtain ⟨b,large⟩ := Supply.Rolls.eventually_large S simple n
  let b' := max (n+1) (max b (∑ i ∈ Finset.range (n+1), f i))
  refine ⟨b',le_max_left ..,fun h hh => ⟨?_,?_⟩⟩
  · apply large
    · exact (le_trans (le_max_left ..) (le_max_right ..)).trans
        (hh.trans (power_large h (Nat.zero_lt_succ n |>.trans_le ((le_max_left ..).trans hh))))
    · change Odd ((3:ℕ)^h.factorial)
      exact Odd.pow (by decide : Odd (3:ℕ))
  · intro i hi
    have hf : 0 < f i := by
      have hc := (D.stream i).pay.st.S.coarse
      rw [(D.stream i).pay.st.crisp] at hc
      by_contra! hz
      rw [show (D.stream i).pay.st.J=0 from Nat.le_zero.mp hz,pow_zero] at hc
      exact (by decide : ¬ 3 ≤ (1:Side).val) hc
    have hsum := Finset.single_le_sum (f:=f) (fun t _ => Nat.zero_le (f t))
      (Finset.mem_range.mpr (show i < n+1 by omega))
    obtain ⟨q,hq⟩ := Nat.dvd_factorial hf (hsum.trans
      ((le_trans (le_max_right ..) (le_max_right ..)).trans hh))
    exact ⟨q,by rw [hq,(D.stream i).pay.st.crisp,pow_mul]⟩

theorem elect (D : Desk S book a simple) : ∃ P : Rolls S, FrameBill D P ∧ Nested P := by
  choose b above accepted using stage D
  let h := fun n => ∑ k ∈ Finset.range (n+1), b k
  have mh : Monotone h := monotone_nat_of_le_succ fun n => by
    simp only [h,Finset.sum_range_succ]
    omega
  have enough (n : ℕ) : b n ≤ h n := by
    exact Finset.single_le_sum (f:=b) (fun k _ => Nat.zero_le (b k)) (Finset.mem_range.mpr (Nat.lt_succ_self n))
  let P : Rolls S := ⟨fun n => (3:Side)^(h n).factorial,fun n => (accepted n _ (enough n)).1,
    fun i j hij => Nat.pow_le_pow_right (by decide : 0 < 3)
      (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_dvd_factorial (mh hij)))⟩
  exact ⟨P,⟨fun n i hi => (accepted n _ (enough n)).2 i ((D.stretch i).trans hi)⟩,
    h,mh,fun n => ⟨(above n).trans (enough n),rfl⟩⟩

theorem divides {P : Rolls S} (paid : Nested P) : WilsonPositionProgramLengths.Divisible P := by
  obtain ⟨h,_,hf⟩ := paid
  intro n
  obtain ⟨e,he⟩ := Nat.factorial_dvd_factorial (hf n).1
  exact ⟨e,by rw [(hf n).2,he]⟩

end YM.Integration.WilsonPositionProgramNestedLengths
end
