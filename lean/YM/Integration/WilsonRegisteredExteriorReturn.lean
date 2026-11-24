import YM.Integration.WilsonRegisteredExteriorPatch
import YM.Integration.WilsonRegisteredExteriorNormalization

/-! The earlier local Gibbs read is taken over its original exterior marginal.
The interpolation keeps its full Wilson kernel on every fixed lower field. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredExteriorReturn
open Function Set MeasureTheory Lattice RG Wilson WilsonHeldExteriorLaw
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato OriginalMarkedRowCovariance
open WilsonHeldRetainedAction
open private kernel_env kernel_floor weighted from YM.Integration.WilsonHeldExteriorLaw
open scoped Classical
variable {G:Gauge}(R:Run G)(N per m:ℕ)
local notation "fine" => Config G (R.family.side (m+1) per)
local notation "coarse" => Config G (R.family.side m per)
local notation "step" => R.family.path.levels.clock.op m per
local notation "β" => R.family.path.β N per (m+1)

set_option backward.isDefEq.respectTransparency false in
theorem sampled (live:m+1≤N)(S:Support (R.family.side (m+1) per))(ext:fine)(V:coarse)
    (p:fine→ℝ)(f:fine→ℂ)(ep:Envelope p)(ef:Envelope f):
    let ξ:=OriginalMarkedConditionalAction.patch S ext
    let k (U:fine):=(step).density β U V
    let d:=(R.family.path.rep N per m).eval V
    let w (U:fine):=k U*p U/d
    read (reference R N per m S ext V) (fun u=>p (ξ u)) (fun u=>f (ξ u))=
      projected (exterior S) w (fun U=>w U•f U) ext:=by
  intro ξ k d w
  have den:0<d:=Multi.AxisShift.chosen_positive R.makes.wilson ((Nat.le_succ m).trans live) V
  have ek:Envelope k:=kernel_env (step) β (R.family.path.levels.blocks m per).branches V
  obtain ⟨t,tp,floor⟩:=kernel_floor R N per m live
  have ex:Envelope (fun u=>k (ξ u)):=by
    obtain ⟨c,pay⟩:=ek.cost
    exact ⟨ek.meas.comp (OriginalMarkedConditionalAction.measurable_patch S ext),c,fun u=>pay _⟩
  have mass:0<∫u,k (ξ u) ∂prior G (R.family.side (m+1) per):=by
    have le:=integral_mono (integrable_const (μ:=prior G _) t) (ex.integrable _) (fun u=>floor (ξ u) V)
    exact tp.trans_le (by simpa using le)
  have ew:Envelope w:=by
    dsimp only [w]
    simp only [div_eq_mul_inv]
    exact (ek.mul ep).mul (Envelope.const d⁻¹)
  have first:=WilsonRegisteredExteriorNormalization.weighted (prior G (R.family.side (m+1) per))
    (fun u=>k (ξ u)) (fun u=>p (ξ u)) (fun u=>f (ξ u)) ex.meas
    (fun u=>(step).density_positive β (ξ u) V) mass
  have ratio:(fun u=>w (ξ u))=(fun u=>d⁻¹*(k (ξ u)*p (ξ u))):=by
    funext u;dsimp only [w];rw [div_eq_inv_mul]
  have scaled:
      read (prior G _) (fun u=>w (ξ u)) (fun u=>f (ξ u))=
        read (prior G _) (fun u=>k (ξ u)*p (ξ u)) (fun u=>f (ξ u)):=by
    rw [ratio]
    exact WilsonRegisteredExteriorNormalization.scaled (prior G _) (fun u=>k (ξ u)*p (ξ u)) (fun u=>f (ξ u)) (inv_ne_zero den.ne')
  refine first.trans (scaled.symm.trans ?_)
  have z:=WilsonRegisteredExteriorPatch.measured S ext w ew
  have num:=WilsonRegisteredExteriorPatch.measured S ext (fun U=>w U•f U) (weighted ew ef)
  unfold OriginalMarkedRowCovariance.read projected
  simp only [Complex.real_smul,Complex.ofReal_inv] at num ⊢
  rw [←num,←z]

theorem original (live:m+1≤N)(S:Support (R.family.side (m+1) per))(V:coarse)(f:fine→ℂ)(ef:Envelope f):
    actualAverage R.family (N:=N)
      (fun ext=>reading R N per m S ext V (R.family.path.rep N per (m+1)) f) V=
      actualAverage R.family (N:=N) f V:=by
  have ep:=(R.family.path.rep N per (m+1)).envelope (R.makes.wilson.represents N per (m+1) live).good
  have same (u:fine):reading R N per m S u V (R.family.path.rep N per (m+1)) f=
      row R N per m S V (R.family.path.rep N per (m+1)) f u:=
    sampled R N per m live S u V _ f ep ef
  simp_rw [same]
  exact WilsonHeldExteriorLaw.all_cutoffs R N per m live S V ef
end YM.Integration.WilsonRegisteredExteriorReturn
