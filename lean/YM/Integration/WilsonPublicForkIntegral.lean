import YM.Integration.WilsonPublicForkSupport
import YM.Integration.WilsonPublicForkLabels

/-! Subtract the complete measured field under the actual two-site far test.
Both original ordinary integrals use independently placed near and far points. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkIntegral
open Function Filter Set MeasureTheory Table Spec RG17 OPE OPE.Orbits OPE.Arboreal
open PhysMS Climb PhysicalNext.Repeat.Legato
open WilsonPublicForkLabels WilsonMacroscopicRichSignedAmplitude
open WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichMovingPlane
open private field positions from YM.Integration.WilsonMacroscopicRichSignedAmplitude
open scoped Classical Topology
variable {n:ℕ}{G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(J:ℝ→PhysMS.tower S)

include F in
private lemma swapped {e:ℕ}{I:Type}[Fintype I]{d:I→ℕ}(x:I→E4)(u:Labels S d)(z:E4)(w:S.Field e)
    (clr:Injective (beside x (sole z))):
    whole (S:=S) S x u (fun _:Fin 1=>z) (e:=fun _:Fin 1=>e) (fun _=>w) =
      whole (S:=S) S (sole z) (sole w:Labels S (fun _:Unit=>e)) x u:=by
  let b:Labels S (fun _:Unit=>e):=sole w
  let reindex:=whole_perm (S:=S) S (Equiv.refl I) WilsonPublicForkSupport.one
    (v:=u) (w:=b) F.room.kernel clr
  exact reindex.trans (whole_flip u b x (sole z) F.room.kernel clr).symm

include F in
private lemma atSite {d:Fin n→ℕ}{e h:ℕ}(x:Fin n→E4)(u:Labels S d)(w:S.Field e)(Y:S.Field h)(z:E4)
    (clr:Injective (beside x (sole z))) (ex:Injective (beside (sole (0:E4)) (sole z))):
    whole (S:=S) S x (d:=d) u (fun _:Fin 1=>z) (e:=fun _:Fin 1=>e) (fun _=>w) -
       upon (S:=S) S h 0 (fun _:Fin 1=>z) (e:=fun _:Fin 1=>e) (fun _=>w) Y=defect (S:=S) e h x u Y z w:=
  congrArg₂ (fun a b:ℂ=>a-b) (swapped F (d:=d) x u z w clr)
    (swapped F (d:=fun _:Unit=>h) (sole 0) (sole Y) z w ex)

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

theorem original (φ:Test 2){r t:ℝ}(tp:0<t)(x:Points n){d:Fin n→ℕ}{e h:ℕ}(v:∀i,RG17.Free C (d i))
    (a:RG17.Free C e)(Y:S.Field h)
    (safe:∀z∈tsupport φ,placed r t x (relative z)∈conf (n+1))
    (inside:∀z∈tsupport φ,Injective (beside (posed r x) (sole (t • relative z 0))) ∧
      Injective (beside (sole (0:E4)) (sole (t • relative z 0)))):
    reading J φ tp ⟨e,a⟩ r x (fun i=>⟨d i,v i⟩) -
      (stencil J φ tp ⟨e,a⟩).charge F h Y =
      ∫z:Points 2, φ z*defect (S:=S) e h (posed r x) (fun i=>J r (d i) (v i)) Y (t • relative z 0) (J t e a):=by
  let X:=stencil J φ tp ⟨e,a⟩
  let A:=integrand J φ tp ⟨e,a⟩ r x (fun i=>⟨d i,v i⟩)
  let B:=fun z:Points 2=>X.pay h Y (t • z)
  let tags:=Fin.append (fun i=>WilsonMacroscopicRichReflectedRoster.physical J r (⟨d i,v i⟩:(Bel C.book).Tag))
    (fun _:Fin 1=>WilsonMacroscopicRichReflectedRoster.physical J t (⟨e,a⟩:(Bel C.book).Tag))
  have aInt:=mass φ A (fun z hz=>by
    have good:=safe z hz
    have flow:=positions r t x
    have ev:∀ᶠu in 𝓝 z,placed r t x (relative u)∈conf (n+1):=flow.continuousAt ((conf_open _).mem_nhds good)
    have cont:ContinuousAt (fun u:Points 2=>S.useAt S (placed r t x (relative u)) tags) z:=
      ((S.class_smooth S F.room.kernel.smooth tags).continuousOn.continuousAt ((conf_open _).mem_nhds good)).comp (f:=fun u=>placed r t x (relative u)) flow.continuousAt
    exact cont.congr (ev.mono fun u hu=>(field F J φ tp ⟨e,a⟩ r x (fun i=>⟨d i,v i⟩) hu).symm))
  have bInt:=mass φ B (fun z hz=>by
    have good:=Work.A05.smul_conf tp (φ.tsupport_subset hz)
    have flow:Continuous (fun u:Points 2=>t • u):=continuous_const_smul t
    have ev:∀ᶠu in 𝓝 z,t • u∈conf 2:=flow.continuousAt ((conf_open _).mem_nhds good)
    let slots:Fin 2→S.Tag:=Fin.cons (⟨h,Y⟩:S.Tag) X.tags
    have cont:ContinuousAt (fun u:Points 2=>S.useAt S (t • u) slots) z:=
      ((S.class_smooth S F.room.kernel.smooth slots).continuousOn.continuousAt ((conf_open _).mem_nhds good)).comp (f:=fun u:Points 2=>t • u) flow.continuousAt
    exact cont.congr (ev.mono fun u hu=>(X.pay_eq F h Y (t • u) hu).symm))
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
    change whole (S:=S) S (posed r x) (d:=d) (fun i=>J r (d i) (v i)) (X.offset (t • z)) X.labels -
      upon (S:=S) S h 0 (X.offset (t • z)) X.labels Y=_
    rw [off];exact atSite F _ _ _ _ _ (inside z hz).1 (inside z hz).2
  · rw[image_eq_zero_of_notMem_tsupport hz];simp

end YM.Integration.WilsonPublicForkIntegral
