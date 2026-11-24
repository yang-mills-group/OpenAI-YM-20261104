import YM.FormalOPE.RG10.Join.Output

/-!
# The log weight of the stipulated interaction germs

Allows performance proof where `V` is known (Haar log etc) and no additional Jacobian. Use when
this convention agrees with the producer's with-Jacobian rows. No analytic exponential used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Route
open Marker Extra.Trajectories FlatFeed Word Polar PowerSeries Finset
open scoped BigOperators Classical
variable {V I : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (R : Census V) {a : Series} (h : PowerSeries.coeff 0 a = 0)

-- no marks

def Ex : Series →+* Word R where
  toFun := sing R.quiet
  map_add' x y := by apply observe_ext; intro s; rw [see_add]; by_cases hs : s=R.quiet <;> simp [hs]
  map_zero' := by apply observe_ext; simp
  map_one':= by apply observe_ext; simp
  map_mul' x y:= by apply observe_ext; intro s; rw [spike_mul]; by_cases hs:s=R.quiet <;> simp [hs]
omit [Fintype V] in
lemma plain (x : Series) (s : R.Mode) : see s (Ex R x)= if s=R.quiet then x else 0 := see_sing ..
include h
private lemma little {i j : ℕ} (hx : i<j) : coeff i (a^j) = 0 := by
  obtain ⟨g,hg⟩:= X_dvd_iff.mpr ((PowerSeries.coeff_zero_eq_constantCoeff_apply _).symm.trans h)
  rw [hg,mul_pow,coeff_X_pow_mul', if_neg (not_le_of_gt hx)]

lemma ticketed : certify I (Ex R (expTaylor a))=Poly.pass (certify I (Ex R a)) := by
  ext s; rw [← pay_sep s,Poly.pass, Poly.part_sum]
  generalize mark s = w
  generalize tickets s = i
  rw [certify_present, present_pay, ← unfold_see, plain]
  simp_rw [Poly.part_smul,← map_pow,certify_present, present_pay, ← unfold_see,plain]
  by_cases he : w=R.quiet
  · simp_rw [if_pos he]; rw [expTaylor,coeff_mk,Finset.mul_sum]
    have ht : i.card ≤ Fintype.card (V ⊕ I) := (Finset.card_le_univ _).trans (by simp)
    rw [← Finset.sum_subset (range_mono (a:=i.card+1) (b:=Fintype.card (V ⊕ I)+1) (by omega)) (fun x _ hx => ?_)] -- may apply to lhs?
    · apply sum_congr rfl; intro x _; ring
    rw [little h (by simp only [mem_range,not_lt] at hx; omega),mul_zero,mul_zero]
  simp [he]
lemma log_weight : logWord (Ex R (expTaylor a)) = Ex R a := by
  have hb : boot (Ex R (expTaylor a))=1 := by rw [boot,vac_eq,plain,if_pos rfl]; simp [expTaylor]
  apply detects; intro k; rw [consistent _ hb,ticketed R h]; apply PolyUtil.conn_pass; exact (present_quiet (Ex R a)).trans (by rw [vac_eq,plain,if_pos rfl,h])
end YM.FormalOPE.RG10.Route
