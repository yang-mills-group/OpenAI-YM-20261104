import YM.Integration.FVA1Physical.Wilson.MarkedEngineering

/-! Re-embed the independently emitted field polynomials in the *joint*
physical clock-field chart at their original engineering grades. The finite
packet recovers every coefficient on the published unit-clock slice. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Comparison.RG02 Assembly Valence Adjacent Moving.Path
open PertExtension.Series PertExtension.Series.Tested FVA1Physical.Round2
open scoped Topology Classical ContDiff BigOperators
variable {X:Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def clockForm (k:ℕ) (f:X→ℂ) (v:ℝ×X):ℂ:=∑j∈range (k+1), v.1^(k-j) • jet f j v.2

theorem clockForm_one {f:X→ℂ} {k:ℕ} (degree:Level (k:ℤ) f) (x:X):
    clockForm k f (1,x)=f x:=by
  simp only [clockForm,one_pow,one_smul]
  exact (degree.posted x).symm

theorem clockForm_analytic {f:X→ℂ} (smooth:ContDiffAt ℝ ω f 0) (k:ℕ):
    ContDiff ℝ ω (clockForm k f) := by
  apply ContDiff.sum
  intro j _
  exact (contDiff_fst.pow _).smul ((levelJet smooth j).smooth.comp contDiff_snd)

theorem clockForm_homogeneous (f:X→ℂ) (k:ℕ) (t:ℝ) (v:ℝ×X):
    clockForm k f (t • v)=t^k • clockForm k f v:=by
  rw [clockForm,clockForm,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have jk:=mem_range_succ_iff.mp hj
  change (t*v.1)^(k-j) • jet f j (t • v.2)=t^k • (v.1^(k-j) • jet f j v.2)
  have combine:(t*v.1)^(k-j)*t^j=t^k*v.1^(k-j):=by
    calc _=(t^(k-j)*t^j)*v.1^(k-j):=by rw [mul_pow];ring
         _=_:=by rw [←pow_add,Nat.sub_add_cancel jk]
  rw [Clipper.weight v.2 t j f]
  exact (smul_smul _ _ (jet f j v.2)).trans ((congrArg (fun a:ℝ=>a • jet f j v.2) combine).trans
    (smul_smul _ _ (jet f j v.2)).symm)

theorem clockForm_jet {f:X→ℂ} (hf:ContDiffAt ℝ ω f 0) (k j:ℕ) (v:ℝ×X):
    jet (clockForm k f) j v=if j=k then clockForm k f v else 0 := by
  have h:=Ranking.impression (clockForm_analytic hf k).contDiffAt v
  have a:Aspiration (fun t:ℝ=>clockForm k f (t • v)) (fun i=>if i=k then clockForm k f v else 0):=by
    simp_rw [clockForm_homogeneous];exact Aspiration.single (clockForm k f v) k
  exact congrFun (h.unique a) j

def clockPacket (e r:ℕ) (U:ℕ→X→ℂ) (v:ℝ×X):ℂ:=∑j∈range (r+1),clockForm (e+j) (U j) v

theorem clockPacket_jet {e r:ℕ} {U:ℕ→X→ℂ} (degree:∀j≤r,Level ((e+j:ℕ):ℤ) (U j)) {p:ℕ} (hp:p≤r)
    (v:ℝ×X):jet (clockPacket e r U) (e+p) v=clockForm (e+p) (U p) v := by
  have de:clockPacket e r U=∑j∈range (r+1),clockForm (e+j) (U j):=funext fun _=>(Finset.sum_apply ..).symm
  rw [de,Assembly.jet,iteratedFDeriv_sum_apply, _root_.sum_apply,Finset.smul_sum]
  · change (∑j∈range (r+1),jet (clockForm (e+j) (U j)) (e+p) v)=_
    rw [Finset.sum_eq_single p]
    · rw [clockForm_jet (degree p hp).smooth.contDiffAt,if_pos rfl]
    · intro j hj hne
      rw [clockForm_jet (degree j (mem_range_succ_iff.mp hj)).smooth.contDiffAt,if_neg (by omega)]
    · intro out;exact False.elim (out (mem_range_succ_iff.mpr hp))
  · intro j hj;exact (clockForm_analytic (degree j (mem_range_succ_iff.mp hj)).smooth.contDiffAt _).contDiffAt.of_le le_top

theorem clockPacket_read {e r:ℕ} {U:ℕ→X→ℂ} (degree:∀j≤r,Level ((e+j:ℕ):ℤ) (U j)) {p:ℕ}
    (hp:p≤r) (x:X):jet (clockPacket e r U) (e+p) (1,x)=U p x:=by
  rw [clockPacket_jet degree hp,clockForm_one (degree p hp)]

end YM.Integration.FVA1Physical.Wilson
