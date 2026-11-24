import YM.Integration.WilsonCenteredAlignedTensor
import YM.PhysMS.Frame.Measured
import YM.Work.A05

/-! Real directional derivatives of the true measured position field at its
fixed leading axes, uniformly on an enlarged separated compact. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredAlignedPhysicalRegularity
open Function Filter Set Spec Extraction Table Trace.Pilot PhysMS OPE OPE.Orbits
open scoped Topology Classical ContDiff

theorem line {V:Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {O:Set V} (op:IsOpen O) {f:V→ℂ} (j:ℕ) (smooth:ContDiffOn ℝ j f O)
    (x w:V) (T:ℝ) (tp:0<T) (inside:∀t∈Icc 0 T,x+t•w∈O) :
    ContDiffOn ℝ j (fun t:ℝ=>f (x+t•w)) (Icc 0 T) ∧
      ∀ t∈Icc 0 T,iteratedDerivWithin j (fun t:ℝ=>f (x+t•w)) (Icc 0 T) t =
        iteratedFDeriv ℝ j f (x+t•w) (fun _=>w) :=by
  let g:ℝ→L[ℝ] V:=(ContinuousLinearMap.id ℝ ℝ).smulRight w
  let U:=(fun z:V=>x+z) ⁻¹' O
  let h:=fun z:V=>f (x+z)
  have uopen:IsOpen U:=op.preimage (continuous_const.add continuous_id)
  have hopen:IsOpen (g ⁻¹' U):=uopen.preimage g.continuous
  have hdiff:ContDiffOn ℝ j h U:=smooth.comp (contDiff_const.add contDiff_id).contDiffOn (fun _ h=>h)
  have composition:ContDiffOn ℝ j (h ∘ g) (g ⁻¹' U):=hdiff.comp g.contDiff.contDiffOn (fun _ ht=>ht)
  have gate: MapsTo id (Icc 0 T) (g ⁻¹' U):=inside
  refine ⟨composition.mono gate,?_⟩
  intro t ht
  have gn:g t∈U:=inside t ht
  have gt:t∈g ⁻¹' U:=gn
  have d:=g.iteratedFDerivWithin_comp_right hdiff uopen.uniqueDiffOn hopen.uniqueDiffOn gt (i:=j) le_rfl
  rw [iteratedFDerivWithin_of_isOpen j hopen gt,iteratedFDerivWithin_of_isOpen j uopen gn] at d
  rw [iteratedDerivWithin_eq_iteratedFDerivWithin]
  change (iteratedFDerivWithin ℝ j (h ∘ g) (Icc 0 T) t) (fun _=>1) = _
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc tp)
      (composition.contDiffAt (hopen.mem_nhds gt)) ht]
  change (iteratedFDeriv ℝ j (h ∘ g) t) (fun _=>1) = _
  rw [d,ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change iteratedFDeriv ℝ j (fun z:V=>f (x+z)) (t•w) (fun _=>(1:ℝ)•w) = _
  rw [iteratedFDeriv_comp_add_left]
  simp only [one_smul]

variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
theorem original (F:Final C f S) {J:ℝ→tower S} (lead:Leading F J)
    {n:ℕ} {d:Caps n} (v:MaxwellSlots C d) (j:ℕ)
    {K:Set (Points n)} (compact:IsCompact K) (sep:K⊆conf n):
    ∃ B:ℝ,0≤B ∧ ∀ᶠ r:ℝ in trail,∀ (x w:Points n) (T:ℝ),0<T →
      (∀t∈Icc 0 T,x+t•w∈K) →
      let D:=fun t:ℝ=> measured F none (J r) v r (x+t•w)
      ContDiffOn ℝ j D (Icc 0 T) ∧
      ∀ t∈Icc 0 T,‖iteratedDerivWithin j D (Icc 0 T) t‖≤B*‖w‖^j :=by
  have physical (r:ℝ) (rp:0<r):ContDiffOn ℝ j (measured F none (J r) v r) (conf n):=by
    let V (i:Fin n):S.Tag:=⟨d i,J r (d i) (v i)⟩
    apply ((S.class_smooth (spectator F none) (spectate F none).smooth V).of_le (show (j:WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).comp
    · change ContDiffOn ℝ j (fun z:Points n=>r•z) (conf n)
      fun_prop
    · intro x ok;exact Work.A05.smul_conf rp ok
  obtain ⟨B,ceiling⟩:=compact.exists_bound_of_continuousOn (f:=iteratedFDeriv ℝ j (WickGoal v)) (fun x hx=>
    ((WickGoal_tied v (sep hx)).continuousAt_iteratedFDeriv (show (j:WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)).continuousWithinAt)
  refine ⟨max 0 B+1,by positivity,?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (lead.lead n d v j K compact sep) 1 zero_lt_one,
    (self_mem_nhdsWithin : ∀ᶠ r:ℝ in trail,0<r)] with r paid rp x w T tp path
  obtain ⟨smooth,jet⟩:=line (conf_open n) j (physical r rp) x w T tp (fun t ht=>sep (path t ht))
  refine ⟨smooth,?_⟩
  intro t ht
  rw [jet t ht]
  have z:=paid (x+t•w) (path t ht)
  rw [dist_comm,dist_eq_norm] at z
  have bill:‖iteratedFDeriv ℝ j (measured F none (J r) v r) (x+t•w)‖ ≤ max 0 B+1:=by
    exact (norm_le_insert' _ _).trans (add_le_add (le_trans (ceiling _ (path t ht)) (le_max_right 0 B)) z.le)
  let H:=iteratedFDeriv ℝ j (measured F none (J r) v r) (x+t•w)
  have paidLine:‖H (fun _=>w)‖≤‖H‖*‖w‖^j:=by
    simpa using H.le_opNorm (fun _=>w)
  exact paidLine.trans (mul_le_mul_of_nonneg_right bill (pow_nonneg (norm_nonneg w) j))

end YM.Integration.WilsonCenteredAlignedPhysicalRegularity
