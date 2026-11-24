import YM.Integration.WilsonThermometerWeakCompactRoom
import YM.Integration.WilsonThermometerWeakCornerWatch

/-! Near coordinates have radius r while the stationary exterior has radius
one. The common disjointness constant is fixed on the physical compactum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakCornerGeometry
open Function Filter Set Extraction Lattice Next.UVStress Trace.Pilot
open WilsonThermometerWeakCornerJets
open scoped Topology Classical

private lemma below (x y:E4)(i:Axis): |x i-y i|≤‖x-y‖:=by
  simpa only [Real.norm_eq_abs,PiLp.sub_apply] using PiLp.norm_apply_le (x-y) i

theorem original {G:Gauge}{C:Family G}{n:ℕ}(W:Watch C)(K:Set (Points n))
    (compact:IsCompact K)(cleared:K⊆conf n):
    ∃s:ℝ,0<s ∧ ∀ᶠ r in 𝓝[>] (0:ℝ),∀x∈K,Pairwise (fun i j=>
      s*Sum.elim (fun _:Fin n=>r) (fun _:Fin W.n=>(1:ℝ)) i ≤
      ‖sites r x (fun j:Fin W.n=>W.held j.succ) i-sites r x (fun j:Fin W.n=>W.held j.succ) j‖):=by
  obtain ⟨c,cp,M,pM,whole⟩:=WilsonThermometerWeakCompactRoom.roster C.S K compact cleared W.held W.origin W.distinct
  obtain ⟨t,tp,far⟩:=WilsonThermometerWeakShapeRoster.clearance C.S (isCompact_singleton (x:=W.held))
     (Set.singleton_subset_iff.mpr W.distinct)
  have apart (i j:Fin (W.n+1))(diff:i≠j): t≤‖W.held i-W.held j‖:=by
    obtain ⟨a,ha⟩:=far W.held (mem_singleton _) i j diff
    exact ha.trans (below ..)
  obtain ⟨L,hL⟩:=compact.isBounded.exists_norm_le
  let B:=max 1 L
  have bp:0<B:=lt_of_lt_of_le zero_lt_one (le_max_left ..)
  let s:=min c (t/2)
  have sc:s≤c:=min_le_left ..
  have st:s≤t/2:=min_le_right ..
  refine ⟨s,lt_min cp (half_pos tp),?_⟩
  have low:∀ᶠ r in 𝓝[>] (0:ℝ),r<t/(2*B):=
    (eventually_lt_nhds (div_pos tp (by positivity))).filter_mono nhdsWithin_le_nhds
  filter_upwards [whole,low,self_mem_nhdsWithin] with r wh lim rp
  have hr:0<r:=rp
  intro x hx i j diff
  cases i with
  | inl i=>
    obtain ⟨a,ha⟩:=(wh x hx).1 (.inl i) j diff
    exact (mul_le_mul_of_nonneg_right sc hr.le).trans ((mul_comm c r).le.trans (ha.trans (below ..)))
  | inr i=>
    cases j with
    | inr j=>
      have neq:i.succ≠j.succ:=fun e=>diff (congrArg Sum.inr (Fin.succ_injective _ e))
      change s*1≤‖W.held i.succ-W.held j.succ‖
      rw [mul_one]
      exact st.trans ((half_le_self tp.le).trans (apart _ _ neq))
    | inl j=>
      have h0:t≤‖W.held i.succ‖:=by simpa only [W.origin,sub_zero] using apart i.succ 0 (Fin.succ_ne_zero i)
      have xj:‖x j‖≤B:=(PiLp.norm_apply_le x j).trans ((hL x hx).trans (le_max_right ..))
      have shift:‖r • x j‖<t/2:=by
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
        apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left xj hr.le)
        have := (lt_div_iff₀ (show 0<2*B by positivity)).mp lim
        linarith only [this]
      change s*1≤‖W.held i.succ-r • x j‖
      rw [mul_one]
      linarith only [st,h0,shift,norm_sub_norm_le (W.held i.succ) (r • x j)]

end YM.Integration.WilsonThermometerWeakCornerGeometry
end
