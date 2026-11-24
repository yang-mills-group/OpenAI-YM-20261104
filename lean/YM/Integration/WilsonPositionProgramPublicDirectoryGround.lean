import YM.Integration.WilsonPositionProgramPublicDirectoryCoin

/-! The bare directory's zero coefficient uses the same measured public
coupling and the same inverse field columns that enter Galop on this tree. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicDirectoryGround
open Set Finset Filter PowerSeries XSpace XSpace.Normalize XSpace.Cirrus XSpace.Structure1 FVA2 MS MS.Land
open Lattice Maxwell FVA2.Register
open scoped Topology BigOperators Classical
variable {G:Gauge} (Z:WilsonPrescription G) {n d:ℕ}

theorem adjustment : constantCoeff (Scale.Measure.adjust Z.scheme Z.criterion d)=1 := by
  unfold Scale.Measure.adjust
  split
  next h => exact h.choose_spec.scale.lead
  next => simp

theorem point {i B:ℕ}(P:Handoff.Directory Z i B)(s:Sample n)(hs:s.F=Z.run.step i)
    (use:Rose.Use Z.scheme Z.criterion (Z.run.step i)) (cover:Handoff.Directory.budget G n d+0≤B)
    (v:Tags G d n):
    WilsonPositionOriginalEpochQuadrature.point P d v s.layout 0 = Rose.cooked Z.scheme Z.store d s 0 v := by
  rw [WilsonPositionBarePointCoefficient.read P d v s hs use 0 cover,
    FPS.coeff_substituted _ (Rose.zero_choice ..)]
  have coef : coeff 0 (1:ℂ⟦X⟧)=1:=by simp
  rw [show (0:ℕ)+1=1 from rfl,range_one,sum_singleton,pow_zero,coef,smul_eq_mul,mul_one]
  change coeff 0 (Reg.Point.story (Speed.forms_t Z.scheme Z.criterion s d) v) = _
  rw [Reg.Point.story,coeff_mk,Speed.forms_t,Dframe.seen,tally,finsuppAntidiag_zero,sum_singleton]
  have idv:pulseU (0:Days n) (Scale.Measure.adjust Z.scheme Z.criterion d) v=v:=by
    funext i
    rw [pulseU,Finsupp.zero_apply,coeff_zero_eq_constantCoeff_apply,adjustment]
    rfl
  rw [idv]
  change (Rose.turn Z.scheme Z.criterion s.F (Rose.cooked Z.scheme Z.store d s) 0) v = _
  rw [Rose.turn_rest]

theorem inversion {i B:ℕ}(P:Handoff.Directory Z i B)(s:Sample n)(hs:s.F=Z.run.step i)
    (use:Rose.Use Z.scheme Z.criterion (Z.run.step i)) (cover:Handoff.Directory.budget G n d+0≤B)
    (v:Tags G d n):
    WilsonPositionOriginalEpochQuadrature.point P d v s.layout 0 =
    coeff 0 (Rose.numberA Z.scheme d s (Retirement.visor Z.scheme Z.store s.F d ∘ v) Finset.univ) := by
  rw [point Z P s hs use cover, Rose.plate0, Rose.lit_up]

variable {g:G.Simple} {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {T:Prescription (Press.portDeck G)}
    {dial:Bool} (H:Main.Match Z g M T dial) (v:Tags G d n) (q:ℕ) {K:Set (Points n)}
    (compact:IsCompact K) (sep:K⊆conf n)

include H compact sep in
theorem original (l:Filter ℝ) {t:ℝ→ℝ} (pos:∀ᶠ r in l,0<t r)
    (small:Tendsto t l (𝓝 0)) (D:ℕ)(J:ℝ) {δ:ℝ}(hδ:0<δ) :
    ∀ᶠ r in l, ∀ i≥WilsonPositionAuxiliaryMesh.floor Z.run q (t r),
      (i:ℝ)≤J*(-Real.log (t r))^D → ∀ {B} (P:Handoff.Directory Z i B),
      Handoff.Directory.budget G n d+q≤B → ∀ s:Sample n,s.F=Z.run.step i →
      welcome s → familiar s∈K → ∀u:ℝ, |u|≤8*t r →
      ‖WilsonPositionProgramPublicDirectoryCoin.drawValue Z v q P u s.layout -
       Rose.cooked Z.scheme Z.store d s 0 v‖ ≤ δ := by
  obtain ⟨i₀,hi⟩:=eventually_atTop.mp ((goesFront (Expense.Stretched.runs Z.run)).eventually
    (Rose.usable Z.scheme Z.criterion g))
  filter_upwards [WilsonPositionProgramPublicDirectoryCoin.original Z H v q compact sep l pos small D J hδ,
    (WilsonPositionAuxiliaryMesh.grows Z.run q l pos small).eventually_ge_atTop i₀] with
    r sal base i ge le B P cover s hs hc hK u hu
  rw [←point Z P s hs (hi i (base.trans ge)) (by omega) v]
  exact sal i ge le P cover s hs hc hK u hu
end YM.Integration.WilsonPositionProgramPublicDirectoryGround
