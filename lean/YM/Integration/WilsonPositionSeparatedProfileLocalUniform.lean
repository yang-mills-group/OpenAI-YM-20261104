import YM.Integration.WilsonPositionSeparatedProfileLocalAssay

/-! An absolute spatial price before either upper regulator for every genuine
field of a compact joint reporting test, on all configurations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPositionSeparatedProfileLocalUniform
open Function Set Finset MeasureTheory Lattice RG Wilson Source
open PhysicalNext.Repeat.Legato RG05Readout RG05Readout.Pulse
open ConnectedActivityE6.Blaze.Thermal1020 ConnectedActivityE6.Blaze.Thermal1020.Shared
open WilsonCoherentMeasuredStencil WilsonIncidentRegisteredMass WilsonReportingPlaquetteWindows
open WilsonPositionSeparatedProfileLocalWave
open private roster from YM.Integration.WilsonPositionSeparatedProfileLocalIncome
open private census from YM.Integration.WilsonReportingPlaquetteWindows
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge} {I:Type} [Fintype I] (R:Run G)

theorem original (d:I→ℕ) (φ:Wave I) (compact:HasCompactSupport φ.val) (s:ℕ) :
    ∃K:ℝ,0<K ∧ ∀k N per,k≤N→∀t:ℕ,(t:ℝ)≤R.family.path.levels.clock.hatBeta k^s→
    ∀(y:∀i,R.family.label (d i)) (r:ℝ) (ξ:Cloud I) (χ:ℂ→L[ℝ]ℝ)
      (H:Config G (R.family.side k per)→ℝ) (M:ℝ),(∀U,‖H U‖≤M) →
      let S:=placements (V:=I) R.family k per t
      ∃A:ℝ,0≤A ∧ (∀(z:S) U,‖H U*mark R d z.val (R.family.path.rep N per k).p.threshold y
          (φ.val (fun i=>r⁻¹ • (R.family.S.place (z.val i)-ξ i))) χ U‖≤A) ∧
        (Fintype.card S:ℝ)*A≤K*R.family.path.levels.clock.hatBeta k^(s*(4*Fintype.card I)+reserve R d)*
          (‖χ‖*originalMass R d y)*M := by
  obtain ⟨B,bp,full⟩:=roster R d
  obtain ⟨A,hA⟩:=compact.exists_bound_of_continuousOn ((show ContDiff ℝ ∞ φ.val from φ.property).continuous.continuousOn)
  let D:=max 1 A
  have dp:0<D:=zero_lt_one.trans_le (le_max_left ..)
  have wave (x:Cloud I):‖φ.val x‖≤D:=by
    by_cases hx:x∈tsupport φ.val
    · exact (hA x hx).trans (le_max_right ..)
    · rw [image_eq_zero_of_notMem_tsupport hx,norm_zero];exact dp.le
  let C:=(3:ℝ)^(4*Fintype.card I)
  have cp:0<C:=pow_pos (by norm_num) _
  refine ⟨C*(B+1)*D,mul_pos (mul_pos cp (by linarith)) dp,?_⟩
  intro k N per live t width y r ξ χ H M hM S
  let b:=R.family.path.levels.clock.hatBeta k
  let X:=originalMass R d y
  have b1:1≤b:=(R.family.path.levels.fits.delayed k).le
  have xp:0≤X:=prod_nonneg fun _ _=>sum_nonneg fun _ _=>norm_nonneg _
  have mp:0≤M:=(norm_nonneg (H 1)).trans (hM _)
  let W:=M*‖χ‖*D*(B*(b^(reserve R d)*X))
  have wp:0≤W:=by dsimp only [W];positivity
  refine ⟨W,wp,?_,?_⟩
  · intro z U
    let c:=φ.val (fun i=>r⁻¹ • (R.family.S.place (z.val i)-ξ i))
    let v:=∏i,Push.Local.presented (R.family.localSection (d i)) (z.val i) (R.family.path.rep N per k).p.threshold (y i) U
    have ck:‖c‖≤D:=wave _
    have vk:‖v‖≤B*(b^(reserve R d)*X):=full k N per live y z.val U
    change ‖H U*χ (c*v)‖≤W
    rw [norm_mul]
    calc
      _ ≤ M*(‖χ‖*‖c*v‖):=mul_le_mul (hM U) (χ.le_opNorm _) (norm_nonneg _) mp
      _ ≤ M*(‖χ‖*(D*(B*(b^(reserve R d)*X)))):=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by rw [norm_mul];exact mul_le_mul ck vk (norm_nonneg _) dp.le) (norm_nonneg _)) mp
      _ = W:=by ring
  · calc
      _ ≤ (C*b^(s*(4*Fintype.card I)))*W:=mul_le_mul_of_nonneg_right (census (V:=I) R.family k per t s b1 width) wp
      _ = C*B*D*b^(s*(4*Fintype.card I)+reserve R d)*(‖χ‖*X)*M:=by dsimp only [W];rw [pow_add];ring
      _ ≤ _:=by gcongr;linarith

end YM.Integration.WilsonPositionSeparatedProfileLocalUniform
