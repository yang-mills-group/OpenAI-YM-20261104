import YM.Integration.WilsonPositionProgramGaussianCofactor

/-! One changed finite driver under the whole connected conditional logarithm. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramGaussianDriver
open Function Finset Marker Multi Primitives.GCC.Anchor Comparison.RG02.Cumulants
open Extra.Trajectories (connected)
open MeasureTheory Next.Rank Next.SectorChange.Gaussian
open scoped BigOperators Classical
variable {I V:Type} [DecidableEq V] [Fintype V] [DecidableEq I] [Fintype I] {R:Census V}
  (Q:Matrix I I ℝ)(hQ:Q.IsSymm)(m:I→ℂ)
  (p:Hot R→Normal.poly I)(s:R.Mode)(i:Hot R)

def hearing : Normal.poly I :=
  ∑ u∈shards R s, if i∈u.val then
    WilsonPositionProgramGaussianCofactor.companion (Cloud.wick Q hQ m) p u i else 0

omit [DecidableEq I] [Fintype I] in
theorem changed (delta:Normal.poly I):
    (connected (Cloud.prescription Q hQ m (update p i (p i+delta)))).part s -
      (connected (Cloud.prescription Q hQ m p)).part s=
        Cloud.wick Q hQ m (delta * hearing Q hQ m p s i):=by
  classical
  let F:=Cloud.wick Q hQ m
  have unit:F 1=1:=Cloud.wick_one ..
  rw [Cloud.prescribed_log,Cloud.prescribed_log,←sum_sub_distrib]
  simp only [hearing,mul_sum,map_sum]
  apply sum_congr rfl
  intro u _
  by_cases hi:i∈u.val
  · rw [if_pos hi]
    have first:=WilsonPositionProgramGaussianCofactor.probed F p u i unit hi (p i+delta)
    have base:=WilsonPositionProgramGaussianCofactor.probed F p u i unit hi (p i)
    rw [update_eq_self] at base
    rw [first,base,add_mul,map_add]
    ring
  · rw [if_neg hi,mul_zero,map_zero,sub_eq_zero]
    exact equal_occurrences (⇑F) (update p i (p i+delta)) p u fun j hj=>
      update_of_ne (fun (eq:j=i)=>hi (eq ▸ hj)) .. 

omit [Fintype V] [DecidableEq I] [Fintype I] in
theorem mean_zero (different:i.val≠s):Cloud.wick Q hQ m (hearing Q hQ m p s i)=0:=by
  classical
  simp only [hearing,map_sum]
  apply sum_eq_zero
  intro u hu
  by_cases hi:i∈u.val
  · rw [if_pos hi]
    apply WilsonPositionProgramGaussianCofactor.centered _ p u i (Cloud.wick_one ..) hi
    by_contra! empty
    have lone:u.val={i}:=by
      ext j
      exact ⟨fun hj=>mem_singleton.mpr (empty j hj),fun hj=>mem_singleton.mp hj ▸ hi⟩
    apply different
    have sh:unionOf u=s:=(mem_filter.mp hu).2
    rw [←sh]
    apply Subtype.ext
    change i.val.val = u.val.biUnion Hot.sites
    simp [lone,Hot.sites]
  · simp [hi]

theorem integrated (h:Q.PosSemidef)(real:I→ℝ)(different:i.val≠s)(delta:Normal.poly I)(flat:ℂ):
    (connected (Cloud.prescription Q hQ (Cloud.shift real) (update p i (p i+delta)))).part s -
      (connected (Cloud.prescription Q hQ (Cloud.shift real) p)).part s =
    ∫z,(Cloud.paint (real+z) delta-flat)*Cloud.paint (real+z) (hearing Q hQ (Cloud.shift real) p s i)
      ∂cloud Q:=by
  let F:=Cloud.wick Q hQ (Cloud.shift real)
  let co:=hearing Q hQ (Cloud.shift real) p s i
  have e:F co=0:=mean_zero Q hQ _ p s i different
  rw [changed]
  change F (delta*co)=_
  calc
    _=F ((delta-MvPolynomial.C flat)*co):=by
      rw [sub_mul,map_sub,MvPolynomial.C_mul',map_smul,e,smul_zero,sub_zero]
    _=_:=by
      have hz:=(Cloud.paid Q hQ h real ((delta-MvPolynomial.C flat)*co)).2.symm
      simpa [Cloud.paint] using hz

end YM.Integration.WilsonPositionProgramGaussianDriver
end
