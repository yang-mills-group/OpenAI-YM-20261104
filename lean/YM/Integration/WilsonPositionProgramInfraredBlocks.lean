import YM.Integration.WilsonPositionProgramNestedElection
import YM.Integration.WilsonPositionProgramCommonWindow

/-! Spend the common fixed-period infrared exponent on complete original Wilson blocks. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramInfraredBlocks
open Filter Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Push.PriceCompiler WilsonPositionProgramCommonWindow
open scoped BigOperators Classical Topology
variable {G : Gauge} (C : Run G) (D : XSpace.Run) {simple : G.Simple} {a : Axis} {ε : ℝ}

/-- Above one finite date every consecutive authentic exponent divides all its successors. -/
theorem nested (purchase : WilsonPositionProgramNestedElection.course simple a ε C.kit) {d : ℕ}
    (hd : 0 < d) (ratio : D.ratio=(3:ℕ)^d) : ∃ start : ℕ, ∃ w : ℕ → ℕ,
      (∀ k, (C.family.S.block (start+k)).val=D.ratio^(w k)) ∧ ∀ k l, k ≤ l → w k ∣ w l := by
  obtain ⟨h,mono,lengths⟩ := purchase.2.1
  obtain ⟨start,active⟩ := eventually_atTop.mp (C.alloy.B.a.fits.deep.eventually (eventually_ge_atTop d))
  let index := fun k => C.alloy.B.a.clock.J (start+k+1)
  have divid (k : ℕ) : d ∣ (h (index k)).factorial := Nat.dvd_factorial hd
    ((active _ (by change start ≤ start+k+1; omega)).trans
      ((Nat.le_succ (index k)).trans (lengths _).1))
  choose w hw using divid
  refine ⟨start,w,fun k => ?_,fun k l hkl => ?_⟩
  · have step : C.family.S.block (start+k)=(3:Side)^(h (index k)).factorial :=
      (block_eq C.alloy.B.valid _).trans (lengths _).2
    rw [step,PNat.pow_coe,show (3:Side).val=3 from rfl,hw,ratio,pow_mul]
  · have hle : index k ≤ index l := C.alloy.B.a.fits.mono (by omega)
    obtain ⟨q,hq⟩ := Nat.factorial_dvd_factorial (mono hle)
    rw [hw,hw,Nat.mul_assoc] at hq
    exact ⟨q,Nat.eq_of_mul_eq_mul_left hd hq⟩

/-- If the remaining exponent fits below this date, the backwards crossing is exact. -/
theorem close (w : ℕ → ℕ) (chain : ∀ k l, k ≤ l → w k ∣ w l) (m R : ℕ)
    (room : R ≤ elapsed w m) (portion : ∀ k < m, w k ∣ R) :
    ∃ b ≤ m, elapsed w b+R=elapsed w m := by
  induction m generalizing R with
  | zero =>
    have h : elapsed w 0=0 := Finset.sum_range_zero _
    exact ⟨0,le_rfl,by omega⟩
  | succ m ih =>
    by_cases h : R=0
    · exact ⟨m+1,le_rfl,by simp [h]⟩
    have endow := Nat.le_of_dvd (Nat.pos_of_ne_zero h) (portion m (Nat.lt_succ_self m))
    have row : elapsed w (m+1)=elapsed w m+w m := Finset.sum_range_succ _ _
    have old (k : ℕ) (hk : k < m) : w k ∣ R-w m := Nat.dvd_sub
      (portion k (Nat.lt_succ_of_lt hk)) (chain k m hk.le)
    obtain ⟨b,hb,paid⟩ := ih (R-w m) (by omega) old
    exact ⟨b,hb.trans (Nat.le_succ m),by omega⟩

end YM.Integration.WilsonPositionProgramInfraredBlocks
end
