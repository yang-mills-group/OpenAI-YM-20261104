import YM.Integration.WilsonCenteredFourSpatialSupport

/-! Subtract the complete measured field under the actual two-site far test.
Both original ordinary integrals use independently placed near and far points. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourSpatialIntegral
open Function Filter Set MeasureTheory Table Spec RG17 OPE OPE.Orbits OPE.Arboreal
open PhysMS Climb PhysicalNext.Repeat.Legato
open WilsonCenteredFourSpatialNodes WilsonMacroscopicRichSignedAmplitude
open WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichMovingPlane
open private field positions from YM.Integration.WilsonMacroscopicRichSignedAmplitude
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→PhysMS.tower S)

include F in
private lemma swapped {I:Type}[Fintype I]{d:I→ℕ}(x:I→E4)(u:Labels S d)(z:E4)(w:S.Field 4)
    (clr:Injective (beside x (sole z))):
    whole (S:=S) S x u (fun _:Fin 1=>z) (e:=fun _:Fin 1=>4) (fun _=>w) =
      whole (S:=S) S (sole z) (sole w:Labels S (fun _:Unit=>4)) x u:=by
  let b:Labels S (fun _:Unit=>4):=sole w
  let reindex:=whole_perm (S:=S) S (Equiv.refl I) WilsonCenteredFourSpatialSupport.one
    (v:=u) (w:=b) F.room.kernel clr
  exact reindex.trans (whole_flip u b x (sole z) F.room.kernel clr).symm

include F in
private lemma atSite (x:Fin 2→E4)(u:Fin 2→S.Field 4)(w Y:S.Field 4)(z:E4)
    (clr:Injective (beside x (sole z))) (ex:Injective (beside (sole (0:E4)) (sole z))):
    whole (S:=S) S x (d:=fun _:Fin 2=>4) u (fun _:Fin 1=>z) (e:=fun _:Fin 1=>4) (fun _=>w) -
       upon (S:=S) S 4 0 (fun _:Fin 1=>z) (e:=fun _:Fin 1=>4) (fun _=>w) Y=defect (S:=S) 4 x u Y z w:=
  congrArg₂ (fun a b:ℂ=>a-b) (swapped F (d:=fun _:Fin 2=>4) x u z w clr)
    (swapped F (d:=fun _:Unit=>4) (sole 0) (sole Y) z w ex)

private lemma mass (φ:Test 2)(k:Points 2→ℂ)(ok:∀z∈tsupport φ,ContinuousAt k z):
    Integrable (fun z=>φ z*k z):=by
  have cont:Continuous (fun z:Points 2=>φ z*k z):=by
    apply continuous_iff_continuousAt.mpr;intro z
    by_cases hz:z∈tsupport φ
    · exact φ.continuous.continuousAt.mul (ok z hz)
    · apply continuousAt_const.congr
      filter_upwards [(isClosed_tsupport (φ:Points 2→ℂ)).isOpen_compl.mem_nhds hz] with t ht
      rw [image_eq_zero_of_notMem_tsupport ht,zero_mul]
  exact cont.integrable_of_hasCompactSupport (HasCompactSupport.mul_right φ.hasCompactSupport)

theorem original (φ:Test 2){r t:ℝ}(tp:0<t)(x:Points 2)(v:Fin 2→RG17.Free R.family 4)
    (a:RG17.Free R.family 4)(Y:S.Field 4)
    (safe:∀z∈tsupport φ,placed r t x (relative z)∈conf 3)
    (inside:∀z∈tsupport φ,Injective (beside (posed r x) (sole (t • relative z 0))) ∧
      Injective (beside (sole (0:E4)) (sole (t • relative z 0)))):
    reading J φ tp ⟨4,a⟩ r x (fun i=>⟨4,v i⟩) -
      (stencil J φ tp ⟨4,a⟩).charge F 4 Y =
      ∫z:Points 2, φ z*defect (S:=S) 4 (posed r x) (fun i=>J r 4 (v i)) Y (t • relative z 0) (J t 4 a):=by
  let X:=stencil J φ tp ⟨4,a⟩
  let A:=integrand J φ tp ⟨4,a⟩ r x (fun i=>⟨4,v i⟩)
  let B:=fun z:Points 2=>X.pay 4 Y (t • z)
  let tags:=Fin.append (fun i=>WilsonMacroscopicRichReflectedRoster.physical J r (⟨4,v i⟩:(Bel R.family.book).Tag))
    (fun _:Fin 1=>WilsonMacroscopicRichReflectedRoster.physical J t (⟨4,a⟩:(Bel R.family.book).Tag))
  have aInt:=mass φ A (fun z hz=>by
    have good:=safe z hz
    have flow:=positions r t x
    have ev:∀ᶠu in 𝓝 z,placed r t x (relative u)∈conf 3:=flow.continuousAt ((conf_open _).mem_nhds good)
    have h:ContinuousAt (fun u:Points 2=>S.useAt S (placed r t x (relative u)) tags) z:=
      ((S.class_smooth S F.room.kernel.smooth tags).continuousOn.continuousAt ((conf_open _).mem_nhds good)).comp (f:=fun u=>placed r t x (relative u)) flow.continuousAt
    exact h.congr (ev.mono fun u hu=>(field F J φ tp ⟨4,a⟩ r x (fun i=>⟨4,v i⟩) hu).symm))
  have bInt:=mass φ B (fun z hz=>by
    have good:=Work.A05.smul_conf tp (φ.tsupport_subset hz)
    have flow:Continuous (fun u:Points 2=>t • u):=continuous_const_smul t
    have ev:∀ᶠu in 𝓝 z,t • u∈conf 2:=flow.continuousAt ((conf_open _).mem_nhds good)
    let slots:Fin 2→S.Tag:=Fin.cons (⟨4,Y⟩:S.Tag) X.tags
    have h:ContinuousAt (fun u:Points 2=>S.useAt S (t • u) slots) z:=
      ((S.class_smooth S F.room.kernel.smooth slots).continuousOn.continuousAt ((conf_open _).mem_nhds good)).comp (f:=fun u:Points 2=>t • u) flow.continuousAt
    exact h.congr (ev.mono fun u hu=>(X.pay_eq F 4 Y (t • u) hu).symm))
  change (Next.UVStress.dilate tp φ).applyTo _-(Next.UVStress.dilate tp φ).applyTo _=_
  rw [Next.UVStress.zoom_integral,Next.UVStress.zoom_integral]
  change (∫z:Points 2,φ z*A z)-(∫z:Points 2,φ z*B z)=_
  rw [←integral_sub aInt bInt]
  apply integral_congr_ae; filter_upwards with z
  by_cases hz:z∈tsupport φ
  · rw [←mul_sub];apply congrArg (φ z*·)
    have off:X.offset (t • z) = fun _:Fin 1=>t • relative z 0:=by
      change (fun i:Fin 1=> t•z i.succ-t•z 0)=_
      funext i;have e:i=0:=Subsingleton.elim _ _;subst i
      change t • z 1-t • z 0=t • (z 1-z 0);rw [smul_sub]
    change whole (S:=S) S (posed r x) (d:=fun _:Fin 2=>4) (fun i=>J r 4 (v i)) (X.offset (t • z)) X.labels -
      upon (S:=S) S 4 0 (X.offset (t • z)) X.labels Y=_
    rw [off];exact atSite F _ _ _ _ _ (inside z hz).1 (inside z hz).2
  · rw[image_eq_zero_of_notMem_tsupport hz];simp

end YM.Integration.WilsonCenteredFourSpatialIntegral
