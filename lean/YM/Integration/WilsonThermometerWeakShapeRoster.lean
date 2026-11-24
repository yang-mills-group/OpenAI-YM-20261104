import YM.Integration.WilsonOriginalThermometerFineCells

/-! Fixed compact shape and genuinely separated stationary exterior before the two limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakShapeRoster
open Function Set Filter Lattice Wilson Extraction
open scoped Classical Topology

theorem clearance {n:ℕ}(S:Schedule){K:Set (Points n)}(compact:IsCompact K)(clear:K⊆conf n):
    ∃c:ℝ,0<c ∧ ∀x∈K,∀i j:Fin n,i≠j → ∃a:Axis,c≤|x i a-x j a|:=by
  obtain ⟨c,pos,sale⟩:=Gaps.someGrows S compact clear
  obtain ⟨p,atp⟩:=sale.exists
  refine ⟨c,pos,?_⟩
  intro x hx i j diff
  obtain ⟨a,h⟩:=atp x hx i j diff
  exact ⟨a,by simpa only [Gaps.distances,Int.cast_zero,zero_mul,Real.dist_eq,sub_zero,abs_sub_comm (x j a) (x i a)] using h 0⟩

private theorem component {n:ℕ}(x:Points n)(i:Fin n)(a:Axis):|x i a|≤‖x‖:=
  (show |x i a|≤‖x i‖ by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x i) a).trans (PiLp.norm_apply_le x i)

/-- Every original scaler is kept at its own physical displacement. At small r their
joint clearance is at least c r and their whole extent is bounded before the cutoffs. -/
theorem original {n l:ℕ}(S:Schedule)(φ:Test n)(h:Points (l+1))(zero:h 0=0)(distinct:h∈conf _):
    ∃c:ℝ,0<c ∧ ∃B:ℝ,0≤B ∧ ∀ᶠ r:ℝ in 𝓝[>] 0,∀x∈tsupport (φ:Points n→ℂ),
      let q:Fin n ⊕ Fin l→E4:=Sum.elim (fun i=>(r • x) i) (fun i=>h i.succ)
      (∀i j,i≠j → ∃a:Axis,r*c≤|q i a-q j a|) ∧ ∀i j (a:Axis),|q i a-q j a|≤B:=by
  obtain ⟨γ,yp,near⟩:=clearance S φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨t,tp,far⟩:=clearance S (isCompact_singleton (x:=h)) (Set.singleton_subset_iff.mpr distinct)
  obtain ⟨M,bound⟩:=φ.hasCompactSupport.isBounded.exists_norm_le
  let C:=max 1 M
  have cp:0<C:=by dsimp only [C];positivity
  let g:=min γ (t/2)
  have gp:0<g:=lt_min yp (half_pos tp)
  have g₁:g≤γ:=min_le_left ..;have g₂:g≤t/2:=min_le_right ..
  refine ⟨g,gp,2*(C+‖h‖),by positivity,?_⟩
  have low:∀ᶠr:ℝ in 𝓝[>] 0,r<t/(2*C):=(eventually_lt_nhds (div_pos tp (by positivity))).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,low,(eventually_lt_nhds (zero_lt_one:0<(1:ℝ))).filter_mono nhdsWithin_le_nhds]
    with r rp small r1
  intro x hx q
  have upper (i:Fin n)(a:Axis):|x i a|≤C:=(component x i a).trans ((bound x hx).trans (le_max_right ..))
  have held (i:Fin n)(a:Axis):|(r • x) i a|≤r*C:=by
    change |r*x i a|≤_;rw [abs_mul,abs_of_pos rp];exact mul_le_mul_of_nonneg_left (upper i a) rp.le
  have rc:r*C<t/2:=by have:= (lt_div_iff₀ (by positivity:0<2*C)).mp small;linarith
  have alone (j:Fin l):∃a:Axis,t≤|h j.succ a|:=by
    obtain ⟨a,z⟩:=far h (mem_singleton h) j.succ 0 (Fin.succ_ne_zero j)
    exact ⟨a,by simpa only [zero,PiLp.zero_apply,sub_zero] using z⟩
  have mixed (i:Fin n)(j:Fin l):∃a:Axis,g≤|(r • x) i a-h j.succ a|:=by
    obtain ⟨a,post⟩:=alone j
    have u:|h j.succ a-0|≤|h j.succ a-(r • x) i a|+|(r • x) i a-0|:=abs_sub_le .. 
    rw [sub_zero,sub_zero,abs_sub_comm (h j.succ a)] at u
    exact ⟨a,by linarith only [post,u,held i a,rc,g₂]⟩
  have rg:r*g≤g:=mul_le_of_le_one_left gp.le r1.le
  constructor
  · intro i j diff
    cases i with
    | inl i=>
      cases j with
      | inl j=>
        obtain ⟨a,h⟩:=near x hx i j (by simpa only [ne_eq,Sum.inl.injEq] using diff)
        refine ⟨a,?_⟩
        change r*g≤|r*x i a-r*x j a|
        rw [←mul_sub,abs_mul,abs_of_pos rp]
        exact mul_le_mul_of_nonneg_left (g₁.trans h) rp.le
      | inr j=>
        obtain ⟨a,h⟩:=mixed i j; exact ⟨a,rg.trans h⟩
    | inr i=>
      cases j with
      | inl j=>
        obtain ⟨a,z⟩:=mixed j i
        exact ⟨a,(rg.trans z).trans_eq (abs_sub_comm ..)⟩
      | inr j=>
        obtain ⟨a,z⟩:=far h (mem_singleton h) i.succ j.succ (by
          intro eq;exact diff (congrArg Sum.inr (Fin.succ_injective l eq)))
        exact ⟨a,rg.trans (g₂.trans ((half_le_self tp.le).trans z))⟩
  · have size (i:Fin n ⊕ Fin l)(a:Axis): |q i a| ≤ C+‖h‖:=by
      cases i with
      | inl i=>exact (held i a).trans ((mul_le_of_le_one_left cp.le r1.le).trans (le_add_of_nonneg_right (norm_nonneg _)))
      | inr i=>exact (component h i.succ a).trans (le_add_of_nonneg_left cp.le)
    intro i j a;exact (abs_sub ..).trans (by linarith only [size i a,size j a])

end YM.Integration.WilsonThermometerWeakShapeRoster
end
