import YangMills.WilsonProof.NativeSupport.JointDatedOpening
import YangMills.WilsonProof.NativeSupport.CalibratedTerminal

/-! The ultraviolet initial ledger is the exact original vacuum at every
field. At the frozen terminal identity, every physical dirty entry
vanishes and the surviving connected logarithm obeys the rooted budget. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.InletSusceptibility.JointShadow
open Function Finset Lattice RG Wilson Marker MergeProof MergeProof.Accent Extra.Multi Extra.Trajectories
open Push.GridApprox.Nil RGGapR2 Packet
open scoped Classical BigOperators
variable {V I:Type} [Fintype V] [DecidableEq V] {G:Gauge} {n:Side}
local notation "B" => Stock.census V
variable (R:Rep G n) (o:V → Site n)
theorem empty_ledger : Rough.Ledger o (fun _ : Support n=>fun _:Config G n=>(0:Marker.Poly (Stock.census V)))
    (fun _ : Box n=>fun _=>(0:Marker.Poly (Stock.census V))) R.p.threshold := by
  have z (X:Support n):Borne o X (fun _:Config G n=>(0:Poly B)) R.p.threshold :=
    ⟨fun _ _ _ _=>rfl,fun _ _=>rfl,fun _=>measurable_const,fun _ _ _=>rfl⟩
  exact ⟨fun i=>⟨z i,fun _ no=>False.elim (no rfl),fun _=>rfl⟩,
    fun i=>⟨⟨z i.1,fun _ no=>False.elim (no rfl)⟩,fun _=>rfl⟩⟩

theorem empty_root [Fintype I] (X:I → Support n) (w:V → ℝ):RootedSheet R.p X (fun _ (_:Config G n)=>(0:Poly B)) w 0 := by
  refine ⟨fun _ _=>0,fun _ _=>le_rfl,fun _ _ _=>by simp,fun _=>by simp⟩

theorem empty_density {a c:ℝ} (vac:R.activities.Valid R.p a c) (Z:Config G n):
    play R B (exclaim R.activities B) (fun _=>0) Z=Poly.bead B (R.eval Z:ℂ) := by
  rw [play,Extra.Trajectories.pass_zero,one_mul,hawk R.activities R.p B vac Z]
  ext q
  change _=(Poly.send (Stock.census V).quiet (R.eval Z:ℂ)).part q
  rw [Poly.part_smul]
  change _*(Poly.send (Stock.census V).quiet _).part q=_
  rw [Poly.part_send,Poly.part_send]
  split
  · rw [Rep.eval,Complex.ofReal_mul]
  · rw [mul_zero]

private theorem field_zero : field (fun _ : Box n=>(0:Poly B)) ∅=1 := by
  unfold field
  rw [sum_eq_single ∅]
  · simp [grid,Pattern]
  · intro s _ h
    unfold grid
    split
    · obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr h
      exact prod_eq_zero hi rfl
    · rfl
  · simp

private theorem flow_one {i:Box n} {K:Config G n → Poly B} (h:Flow o i K R.p.threshold):K 1=0 := by
  by_contra no
  obtain ⟨he,⟨x,hx⟩,_⟩:=h.permits 1 no
  rw [UVNext.CouplingReset.flags_one R.p,inter_empty] at he
  exact notMem_empty x (he ▸ hx)

variable (E:Support n → Config G n → Marker.Poly (Stock.census V)) (K:Box n → Config G n → Marker.Poly (Stock.census V))
theorem frozen_outlet {a c u:ℝ} (vac:R.activities.Valid R.p a c) (proper:Rough.Ledger o E K R.p.threshold)
    (reg:RootedSheet R.p id E (fun _:V=>2) u) :
    let H:=∑ X,E X (1:Config G n)
    H.part (tag ∅)=0 ∧ play R B (exclaim R.activities B+K) (fun Z=>∑ i,E i Z) 1=(Real.exp (R.exponent 1):ℂ) • Poly.pass H ∧
      ∀ root:V,(∑ s:Finset V with root∈s,‖H.part (tag s)‖*2^(s.card-1)) ≤ u := by
  intro H
  have flag (i:Box n):exclaim R.activities B i 1+K i 1=0 := by
    rw [flow_one R o (granular R.activities R.p B (o:=o) vac i),flow_one R o (proper.flag i).1,add_zero]
  refine ⟨?_,?_,?_⟩
  · change (∑ X,E X 1).part (tag ∅)=0
    rw [Poly.part_sum];exact sum_eq_zero fun i _=>(proper.exp i).sil 1
  · rw [play,UVNext.CouplingReset.flags_one R.p]
    change _ • (_*field (fun i=>exclaim R.activities B i 1+K i 1) ∅)=_
    simp only [flag,field_zero,mul_one,H]
  · obtain ⟨m,m0,bound,bill⟩:=reg
    intro root
    have toll (s:Finset V):Poly.toll (fun _:V=>(2:ℝ)) (tag s)=2^s.card := by simp [Poly.toll]
    have mass (X:Support n):1 ≤ Real.exp (R.p.supportExponent*coverNumber R.p.B X):=
      Real.one_le_exp (mul_nonneg R.p.exponent_pos.le (Nat.cast_nonneg _))
    calc
      _ ≤ ∑ s:Finset V with root∈s,∑ X:Support n,2^s.card*m X s := by
        apply sum_le_sum
        intro s _
        change ‖(∑ X,E X 1).part (tag s)‖*2^(s.card-1) ≤ _
        rw [Poly.part_sum]
        calc
          _ ≤ (∑ X,m X s)*2^s.card := mul_le_mul
            ((norm_sum_le ..).trans (sum_le_sum (fun i _=>bound i 1 s)))
            (pow_le_pow_right₀ (by norm_num) (Nat.sub_le ..)) (by positivity) (sum_nonneg fun i _=>m0 i s)
          _ = _ := by rw [mul_comm,mul_sum]
      _ = ∑ X:Support n,∑ s:Finset V with root∈s,2^s.card*m X s := sum_comm
      _ ≤ ∑ X:Support n,Real.exp (R.p.supportExponent*coverNumber R.p.B X)*(∑ s:Finset V with root∈s,2^s.card*m X s) := by
        apply sum_le_sum
        intro i _
        exact le_mul_of_one_le_left (sum_nonneg fun s _=>mul_nonneg (by positivity) (m0 ..)) (mass i)
      _ ≤ u := by simpa only [toll,id_eq] using bill root

end YM.Integration.InletSusceptibility.JointShadow
