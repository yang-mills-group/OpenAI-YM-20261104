import YM.Integration.WilsonThermometerWeakRetainedRow

/-! A short received coefficient re-enters the original reflected marked gas as the issued
group field, its regular signed error, and a compulsory term supported on a genuine flag. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakFlagStrike
open Next.Rank Next.Rank.Edition Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker
open Perch Vac.Numbers Alarm Finset Baler Source Labels EntryWord Exponential Extra.Histories
open Next.Rank Next.Rank.Edition Next.Rank.Spindle Station Cells Atlas Configuration Rise
open WilsonThermometerWeakRetainedRow
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G} {V:Type} [Fintype V] [DecidableEq V]
variable {k N p d m:ℕ} {q:BudgetPoint}
local notation "n" => C.side k p
local notation "ℙ" => C.path.rep N p k

theorem original (X:Coefficient (C.labels.level d) n) (Z:Keepat n) (B:Config G n→ℂ)
    (mask:Reliable (ℙ).p.threshold G n (halo 8 Z.val) (short (C:=C) X N m))
    (raw:Reliable (ℙ).p.threshold G n Z.val (unmasked (C:=C) X N m))
    (agrees:∀ U,Healthy (ℙ).p.threshold Z.val U→short (C:=C) X N m U=unmasked (C:=C) X N m U)
    (fresh:Reliable q.threshold G n Z.val B)
    {cap δ:ℝ} (gross:∀ U,‖short (C:=C) X N m U‖≤cap)
    (score:∀ U,Healthy q.threshold Z.val U→‖short (C:=C) X N m U-B U‖≤δ)
    (debt:0≤δ) (hu:q.threshold≤(ℙ).p.threshold)
    (ζ:V→Site n) (s:Signed) (r:Prop) (j:V) :
    ∃ (file error:SourceAt G ζ) (forced:Strike G ζ q.threshold),
      file=Edition.traverse (C:=C) s r j Z.property fresh ∧ error.extent=swath s (ζ j) Z.val ∧ error.fires=slot j ∧
      forced.extent=halo 8 (swath s (ζ j) Z.val) ∧ forced.fires=slot j ∧
      (∀ U,Poly.send (slot j) (dot r (short (C:=C) X N m (pull s (ζ j) U)))=
        file.amount q.threshold U+error.amount q.threshold U+forced.occ U) ∧
      ∀ w:V→ℝ,0≤w j →
        transported error q.threshold w (w j*δ) ∧ Taxed forced (q:=q) w (w j*cap) := by
  let F:=pull (K:=G.El) s (ζ j)
  let z:=swath s (ζ j) Z.val
  let file:=Edition.traverse (C:=C) s r j Z.property fresh (ζ:=ζ)
  have D:Reliable q.threshold G n Z.val (fun U=>unmasked (C:=C) X N m U-B U):=
    ⟨fun g U=>congrArg₂ (·-·) (raw.inv g U) (fresh.inv g U),raw.meas.sub fresh.meas,
      fun U U' h=>congrArg₂ (·-·) (raw.locally _ _ h) (fresh.locally _ _ h)⟩
  let error:=Edition.traverse (C:=C) s r j Z.property D (ζ:=ζ)
  let forced:Strike G ζ q.threshold:=by
    refine { extent:=halo 8 z, active:=?_, fires:=slot j, remembers:=?_,
             value:=fun U=>dot r (short (C:=C) X N m (F U))-
               masked q.threshold z (dot r ∘ unmasked (C:=C) X N m ∘ F) U,
             meas:=?_,inv:=?_,sees:=?_,only:=?_ }
    · exact Finset.Nonempty.mono (halo_subset ..) ((show Z.val.Nonempty from ⟨_,Z.property⟩).image (affine s (ζ j)))
    · intro i h;obtain rfl:i=j:=Finset.mem_singleton.mp h
      exact halo_subset _ _ (by simpa only [z,affine,Signed.act_zero,zero_add] using (stay s (ζ i) _|>.2 Z.property))
    · exact ((dot_meas r).comp (mask.meas.comp (continuous_pull ..|>.measurable))).sub
        (masked_measurable _ _ _ ((dot_meas r).comp (raw.meas.comp (continuous_pull ..|>.measurable))))
    · intro g U;apply congrArg₂ (·-·)
      · exact congrArg (dot r) (p_invar s (ζ j) mask.inv g U)
      exact sails _ _ _ (fun g U=>congrArg (dot r) (p_invar s (ζ j) raw.inv g U)) g U
    · intro U U' h _;apply congrArg₂ (·-·)
      · exact congrArg (dot r) (p_local s (ζ j) _ mask.locally U U' (by rw [swath_iffHalo];exact h))
      exact sail _ z _ (fun a b hab=>congrArg (dot r) (p_local s (ζ j) Z.val raw.locally _ _ hab)) U U' h
    intro U h;have h':Healthy q.threshold z U:=Disjoint.mono_left (halo_subset _ _) h
    rw [agrees _ ((s_healthy ..).2 (threshold_fit _ _ hu _ h')),masked_eq _ _ _ _ h'];exact sub_self _
  refine ⟨file,error,forced,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · intro U
    dsimp only [SourceAt.amount,file,error,forced,Strike.occ,Edition.traverse,fulcrum]
    rw [←send_plus,←send_plus];apply congrArg
    by_cases h:Healthy q.threshold z U
    · rw [masked_eq _ _ _ _ h,masked_eq _ _ _ _ h,masked_eq _ _ _ _ h]
      simp only [Function.comp_apply];rw [←dot_add,add_comm (B _),sub_add_cancel]
      abel
    rw [masked_ne _ _ _ _ h,masked_ne _ _ _ _ h,masked_ne _ _ _ _ h];simp [F]
  intro w hw
  constructor
  · apply (transferD ..).2;refine ⟨mul_nonneg hw debt,?_⟩
    intro U h
    dsimp only [error,Edition.traverse,fulcrum]
    rw [Function.comp_apply,Function.comp_apply,dot_norm,Poly.solo_toll]
    have h':Healthy q.threshold Z.val (F U):=(s_healthy ..).2 h
    exact mul_le_mul_of_nonneg_left ((agrees _ (threshold_fit _ _ hu _ h')) ▸ score (F U) h') hw
  have cap_nonneg:0≤cap:=(norm_nonneg _).trans (gross (1:Config G n))
  refine ⟨mul_nonneg hw cap_nonneg,fun U=>?_⟩
  dsimp only [forced];by_cases h:Healthy q.threshold z U
  · rw [masked_eq _ _ _ _ h];simp only [Function.comp_apply]
    rw [agrees _ ((s_healthy ..).2 (threshold_fit _ _ hu _ h)),sub_self,norm_zero,mul_zero]
    exact mul_nonneg hw cap_nonneg
  rw [masked_ne _ _ _ _ h,sub_zero,Poly.solo_toll,dot_norm]
  exact mul_le_mul_of_nonneg_left (gross _) hw

end YM.Integration.WilsonThermometerWeakFlagStrike
end
