import YM.Integration.WilsonThermometerWeakOriginalReclosure

/-! The physical forced components of every displaced singleton and the same original
quiet gas meet the smaller weak-course support price simultaneously. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakOriginalHardCopy
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open Next.Rank Next.Rank.Edition Next.Rank.Spindle Configuration Rise
open Thirst Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Cells Atlas Baler EntryWord Exponential
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {n:Side} {V:Type} [Fintype V] [DecidableEq V] {ζ:V→Site n}
variable {d:V→ℕ} {F:(i:V)→Frame G (d i)} {η:Hol G} {P:Rep G n}

theorem original (X:(i:V) → Coefficient (F i) n) (form:∀ i,(X i).Format 0 η P)
    (s:V→Signed) (a:V→Prop) (vac:Neat n→Burst G n P.p.threshold) (u:ℝ) (quiet:IsoVac P vac u)
    (cash:V→ℝ) (intake:∀ i,(X i).remBound 0 P (Real.sqrt u) (cash i))
    (q:BudgetPoint) (w:V→ℝ) (hw:∀ i,0≤w i) {z y:ℝ} (hz:0≤z) (hy:0≤y)
    (rates:∀ i,w i*cash i≤z) (low:Lower P.p q) (sep:Spaced P.p.B ζ) (wide:scalesExp P.p q (y+1)) :
    Burden (elderX ζ X form s a vac (fun _=>1)) q w y
      (83521*(Real.exp (100000*y)*u)+wilt q.B*(Real.exp (100000*(y+1))*(z*Real.sqrt u))) := by
  let S:=fun j:V×Rootage n=>bitsX ζ X form s a (fun _=>1) j.1 j.2
  have inj:=injected P.p.B ζ P.p.B_pos sep
  apply sum_token (enroll ζ ∘ vac) S
  · obtain ⟨c,H,hQ⟩:=quiet.smooth
    refine ⟨c,fun i=>⟨(H i).1,fun U=>?_⟩,
      ShiftUp (E:=enroll ζ ∘ vac) _ _ low y hy ?_ (fun i=>(H i).1) _ hQ⟩
    · dsimp only [Function.comp_apply,enroll];simp_rw [Poly.quiet_toll,Complex.norm_real,one_mul];exact (H _).2 _
    apply le_trans _ wide;gcongr;linarith only
  choose m hm hz' using fun i:V=>show ∃ m:Rootage n→ℝ,(∀ j,heavy (S (i,j)) w (m j)) ∧
      (∑ j,m j*Value.charge P.p P.p.supportExponent (S (i,j)).extent)≤z*Real.sqrt u from by
    obtain ⟨α,b,hα,_,total,_,_,e,hq,hs⟩:=intake i
    have hb:b≤cash i:=(le_add_of_nonneg_left hα).trans total
    obtain ⟨m,paid,bill⟩:=root_budget (F:=X i) (s i) (form i) (a i) (1:ℂ) hs hq i w (hw i) (ζ:=ζ)
    refine ⟨m,paid,bill.trans ?_⟩
    rw [norm_one,mul_one,mul_left_comm (w i),mul_comm (Real.sqrt u)]
    exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left hb (hw i)).trans (rates i)) (Real.sqrt_nonneg _)
  let W (j:V×Rootage n):=m j.1 j.2
  have ht j:heavy (S j) w (W j):=hm j.1 j.2
  let Z i:=halo 8 (S i).extent
  let A i:=(S i).fires
  have key i:(S i).fires=slot i.1:=rfl
  refine ⟨W,ht,roots_hits Z A ζ inj (fun i=>by unfold A;rw [key];exact Finset.singleton_nonempty _)
    (fun i j hj=>halo_subset _ _ ((S i).remembers j hj)) (fun j=>(ht j).1)
    (mul_nonneg (Real.exp_pos _).le (mul_nonneg hz (Real.sqrt_nonneg _))) ?_⟩
  intro x
  let f j:=W j*debt q.B (y+1) (Z j)
  apply (sum_pay _ (fun i=>x∈(A i).val) f (fun j=>mul_nonneg (ht j).1 (Real.exp_pos _).le)).2
  rw [Fintype.sum_prod_type,Finset.sum_eq_single x]
  · apply le_trans _ (mul_le_mul_of_nonneg_left (hz' x) (Real.exp_pos _).le)
    rw [Finset.mul_sum];apply Finset.sum_le_sum;intro i _
    rw [if_pos (show x∈(A (x,i)).val from Finset.mem_singleton_self _)]
    apply (mul_le_mul_of_nonneg_left (scaler P.p q low wide (add_nonneg hy zero_le_one) (S (x,i)).extent) (hm x i).1).trans_eq
    exact mul_left_comm ..
  · intro i _ nEq;apply Finset.sum_eq_zero;intro j _;exact if_neg (fun h=>nEq (Finset.mem_singleton.mp h).symm)
  simp

end YM.Integration.WilsonThermometerWeakOriginalHardCopy
end
