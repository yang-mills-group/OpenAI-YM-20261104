import YM.Integration.WilsonOriginalStationaryLightStep

set_option autoImplicit false
noncomputable section
namespace YM.Stationary
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open scoped Topology ContDiff BigOperators
variable {G: Gauge} {s: Sheet G}{L : Rolls s} {Θ : Protection L}{a:Levels G}{Z: ChartRatio G}
variable {w: Delays Θ} {y: Bar w}{v:Wait y}{V: Horizon a}{Q:PostCost L}
theorem settledWithLight (cap : ℝ → ℝ) (T':ℕ→ Reel G) (h : Paid v a) (hl : ∀ i, 1 ≤ a.clock.loopCap i) (hp : ∀ N,∃ R : PathData G,BranchRow V N R ∧ Light cap a N R)
    (hr : ∀ m N,m<N →∀ R, (SatPath V N (m+1) R ∧ Light cap a (m+1) R) → ∃ D α ρ,Light cap a m D ∧ Bubble V Q Z N m R D α ρ ∧ Skies (a:=a) T' m D) : ∃ T : Kin V Z, Inspected T Q T' ∧ LightPath T cap := by
  classical
  have he (N n) (hN : n≤N) :
      ∃ Y : ℕ→PathData G,∃ α : ℕ→ℝ,∃ ρ : ∀ i,GainWire a i,BranchRow V N (Y N) ∧
        (∀ i,n ≤ i → i≤N → SatPath V N i (Y i) ∧ Light cap a i (Y i)) ∧ ∀ i, n ≤ i → i < N → Bubble V Q Z N i (Y (i+1)) (Y i) (α i) (ρ i) ∧ Skies (a:=a) T' i (Y i) := by
    induction hN using Nat.decreasingInduction with
    | self =>
      obtain ⟨R,H,hLight⟩ := hp N
      refine ⟨fun _=> R,0,fun _ _ _ _=>0,H,fun i hi hu=> ?_,by intros; omega⟩
      rw [le_antisymm hu hi]; exact ⟨H.1,hLight⟩
    | of_succ i hi I =>
      obtain ⟨Y,α,ρ,hY,he,H⟩ := I
      obtain ⟨D,w,θ,hLight,hD,h'⟩ := hr i N hi _ (he (i+1) le_rfl hi)
      refine ⟨update Y i D,update α i w,update ρ i θ,?_,?_,?_⟩
      · rw [update_of_ne hi.ne']; exact hY
      · intro m hm hv; rcases eq_or_lt_of_le hm with heq|heq
        · subst m; rw [update_self]; exact ⟨hD.lives,hLight⟩
        rw [update_of_ne heq.ne']; exact he m (Nat.succ_le_of_lt heq) hv
      intro m hv hx; rcases eq_or_lt_of_le hv with heq|heq
      · subst m; rw [update_self,update_self,update_self,update_of_ne (by omega)]; exact ⟨hD,h'⟩
      rw [update_of_ne (by omega : m+1 ≠ i),update_of_ne (by omega : m≠i),update_of_ne (by omega : m ≠ i),update_of_ne (by omega : m≠i)]; exact H m heq hx
  choose Y α ρ H H' HI using fun N=> he N 0 (Nat.zero_le _)
  let V0 : Kin V Z := ⟨α,Y,ρ⟩; refine ⟨V0,⟨⟨?_,fun N m h=> (H' N m (by omega) h).1.row,fun N m p F hm=> (HI N m (by omega) hm|>.1.steps p F).2.2.2.2⟩,fun m N h=> HI N m (Nat.zero_le _) h⟩,fun N m h => (H' N m (Nat.zero_le _) h).2⟩
  refine ⟨h.stage.symm,h.lengths.symm,fun N m hm=> (H' N m (by omega) hm).1.ties,fun N m hm => (H' N m (by omega) hm).1.bound,
    fun N i=>(H N).2.1 i,fun N i=> (H N).2.2 i,fun N m p hm F=>(HI N m (by omega) hm|>.1.steps p F).1,
    fun N m p hm F=>?_,fun N m p hm F=> (HI N m (by omega) hm|>.1.steps p F).2.2.2.1,fun N m hm=> (HI N m (by omega) hm).1.earns,fun N m p hm F=> ?_⟩
  · exact ⟨(HI N m (by omega) hm|>.1.steps p F).2.1,(HI N m (by omega) hm|>.1.steps p F).2.2.1⟩
  exact higher_bill ((HI N m (by omega) hm|>.1.steps p F).2.2.2.2) (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hl _) (Q.pos _).le) (Real.exp_pos _).le)

end YM.Stationary
end
