import YM.Integration.WilsonPhysicalPositionChangeCancellation
import YM.Integration.WilsonPositionPrescribedStability

/-! Evaluate the position equations at the second physical home with one common
family of dilated configurations. All inputs, the unit and all proper faces
are acted upon by the same true field transport before the field fit. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalPositionHomeDilation
open Function Set Filter Spec Table Extraction Trace.Pilot PhysMS Maxwell Maxwell.Free XSpace XSpace.Normalize
open scoped Topology Classical
variable {G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→tower S)

def arm (r ρ:ℝ)(d:ℕ):Sec G d ≃ₗ[ℂ] Sec G d:=
  ((fields C.labels d).symm.trans (J ρ d)).trans ((J r d).symm.trans (fields C.labels d))

theorem paid_at_home (r ρ:ℝ)(d:ℕ)(v:Sec G d):
    J r d ((fields C.labels d).symm (arm J r ρ d v))=
      J ρ d ((fields C.labels d).symm v):=by simp [arm]

def samples (r τ:ℝ)(d:ℕ):Prediction G d:=
  WilsonPositionPrescribedScreen.hierarchy F (fun _=>J r) d (r*τ)

theorem points (r τ:ℝ)(d n:ℕ)(x:Points n)(v:Fin n→Sec G d):
    WilsonPositionPrescribedScreen.point F J (r*τ) d n x v=
      WilsonPositionPrescribedScreen.point F J r d n (τ • x) (fun j=>arm J r (r*τ) d (v j)):=by
  change S.classMoment _ _ ((r*τ) • x) _=S.classMoment _ _ (r • τ • x) _
  rw [mul_smul]
  congr 1
  funext j
  exact (paid_at_home J ..).symm

theorem full {r τ:ℝ}(hr:0<r)(ht:0<τ)(d:ℕ):
    WilsonPositionPrescribedScreen.hierarchy F J d (r*τ)=
      recruit (arm J r (r*τ) d).toLinearMap (samples F J r τ d):=by
  funext n
  apply LinearMap.ext
  intro t
  apply MultilinearMap.ext
  intro v
  change WilsonPositionPrescribedScreen.hierarchy F J d (r*τ) n t v=
    WilsonPositionPrescribedScreen.hierarchy F (fun _=>J r) d (r*τ) n t (fun i=>arm J r (r*τ) d (v i))
  rw [WilsonPositionPrescribedScreen.actual F J _ _ _ _ (mul_pos hr ht),
      WilsonPositionPrescribedScreen.actual F (fun _=>J r) _ _ _ _ (mul_pos hr ht)]
  apply congrArg t.applyTo
  funext x
  unfold measured
  congr 1
  funext j
  exact (paid_at_home J ..).symm

theorem window {p:ℝ→Prop} (h:∀ᶠρ in trail,p ρ):
    ∀ᶠ r in trail,0<r ∧ ∀τ∈Icc (1:ℝ) 2,p (r*τ):=by
  obtain ⟨a,ha,inside⟩:=mem_nhdsGT_iff_exists_Ioo_subset.mp h
  refine mem_nhdsGT_iff_exists_Ioo_subset.mpr ⟨a/2,show 0<(a:ℝ)/2 from half_pos ha,?_⟩
  intro r hr
  refine ⟨hr.1,fun τ hτ=>inside ⟨mul_pos hr.1 (lt_of_lt_of_le zero_lt_one hτ.1),?_⟩⟩
  calc r*τ≤r*2:=mul_le_mul_of_nonneg_left hτ.2 hr.1.le
       _ <a:=by linarith [hr.2]

theorem original (lead:Leading F J)(V:Store G)(d:ℕ):
    ∀ᶠ r in trail,∀τ∈Icc (1:ℝ) 2,
      let ρ:=r*τ
      let H:=(arm J r ρ d).toLinearMap ∘ₗ stand (WilsonPositionPrescribedScreen.correction F J V d ρ)
      (V.measure d).D (recruit H (samples F J r τ d))=(V.measure d).D (reference G d) ∧
      recruit H (samples F J r τ d)=recruit (stand (WilsonPositionPrescribedScreen.correction F J V d ρ))
        (WilsonPositionPrescribedScreen.hierarchy F J d ρ):=by
  filter_upwards [window (WilsonPositionPrescribedScreen.original F J lead V d).2] with r hr
  intro τ hτ
  dsimp only
  rw [←recruits_comp,←full F J hr.1 (lt_of_lt_of_le zero_lt_one hτ.1)]
  exact ⟨(hr.2 τ hτ).1,rfl⟩

end YM.Integration.WilsonPhysicalPositionHomeDilation
end
