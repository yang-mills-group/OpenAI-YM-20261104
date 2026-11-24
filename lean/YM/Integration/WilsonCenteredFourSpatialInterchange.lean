import YM.Integration.WilsonCenteredFourSpatialProfile

/-! Fubini on the complete original located two-by-two test. Both positions
of the exterior and the full signed near shape remain in the kernel. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredFourSpatialInterchange
open Function Filter Set MeasureTheory Table Spec RG17 OPE OPE.Orbits
open PhysMS Climb PhysicalNext.Repeat.Legato
open WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichTestGeometry WilsonMacroscopicRichMovingPlane
open private coordinate from YM.Integration.WilsonMacroscopicRichTestGeometry
open private field from YM.Integration.WilsonMacroscopicRichSignedAmplitude
open scoped Classical Topology
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family f S)(J:ℝ→PhysMS.tower S)

private lemma motion (r t:ℝ):Continuous (fun q:Points 2×Points 2=>placed r t q.1 (relative q.2)):=by
  apply (PiLp.continuous_toLp 2 _).comp (continuous_pi ?_)
  intro i;cases i using Fin.addCases with
  | left i=>simp only [Fin.append_left];exact (continuous_const_smul r).comp ((coordinate i).comp (continuous_fst:Continuous fun q:Points 2×Points 2=>q.1))
  | right i=>simp only [Fin.append_right];exact (continuous_const_smul t).comp ((coordinate i).comp (continuous_relative.comp (continuous_snd:Continuous fun q:Points 2×Points 2=>q.2)))

include F in
private lemma kernel {r t:ℝ}(tags:Fin (2+1)→S.Tag)(q:Points 2×Points 2)
    (good:placed r t q.1 (relative q.2)∈conf (2+1)):
    ContinuousAt (fun p:Points 2×Points 2=>S.useAt S (placed r t p.1 (relative p.2)) tags) q:=by
  let y:=fun p:Points 2×Points 2=>placed r t p.1 (relative p.2)
  have initial:ContinuousAt (fun z:Points (2+1)=>S.useAt S z tags) (y q):=
    (S.class_smooth S F.room.kernel.smooth tags).continuousOn.continuousAt ((conf_open _).mem_nhds good)
  exact initial.comp (f:=y) (motion r t).continuousAt

private lemma pairs (ψ φ:Test 2)(m:Points 2×Points 2→ℂ)
    (germ:∀q∈tsupport ψ ×ˢ tsupport φ,ContinuousAt m q):
    Integrable (fun q:Points 2×Points 2=>ψ q.1*(φ q.2*m q)) (volume.prod volume):=by
  let A:=fun q:Points 2×Points 2=>ψ q.1*(φ q.2*m q)
  let box:=tsupport ψ ×ˢ tsupport φ
  have compact:IsCompact box:=ψ.hasCompactSupport.prod φ.hasCompactSupport
  have outside(q:Points 2×Points 2)(h:q∉box):A q=0:=by
    by_cases hx:q.1∈tsupport ψ
    · have hz:q.2∉tsupport φ:=fun hit=>h ⟨hx,hit⟩
      simp [A,image_eq_zero_of_notMem_tsupport hz]
    · simp [A,image_eq_zero_of_notMem_tsupport hx]
  have bounded:HasCompactSupport A:=compact.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (fun q hn=>by by_contra h;exact hn (outside q h)) compact.isClosed)
  have c:Continuous A:=by
    apply continuous_iff_continuousAt.mpr;intro q
    by_cases h:q∈box
    · exact (ψ.continuous.comp continuous_fst).continuousAt.mul ((φ.continuous.comp continuous_snd).continuousAt.mul (germ q h))
    · exact (show ContinuousAt (fun _:Points 2×Points 2=>(0:ℂ)) q from continuousAt_const).congr
        ((show ∀ᶠp in 𝓝 q,p∉box from compact.isClosed.isOpen_compl.mem_nhds h).mono fun p hp=>(outside p hp).symm)
  exact c.integrable_of_hasCompactSupport bounded

include F in
private lemma joint (ψ φ:Test 2){r t:ℝ}(tp:0<t)(v:Fin 2→RG17.Free R.family 4)(a:RG17.Free R.family 4)
    (safe:∀x∈tsupport ψ,∀z∈tsupport φ,placed r t x (relative z)∈conf 3):
    Integrable (fun q:Points 2×Points 2=>ψ q.1*(φ q.2*integrand J φ tp ⟨4,a⟩ r q.1 (fun i=>⟨4,v i⟩) q.2)) (volume.prod volume):=by
  let tags:=Fin.append (fun i=>WilsonMacroscopicRichReflectedRoster.physical J r (⟨4,v i⟩:(Bel R.family.book).Tag))
    (fun _:Fin 1=>WilsonMacroscopicRichReflectedRoster.physical J t (⟨4,a⟩:(Bel R.family.book).Tag))
  apply pairs ψ φ
  intro q h
  have good:=safe q.1 h.1 q.2 h.2
  have ev:∀ᶠp in 𝓝 q,placed r t p.1 (relative p.2)∈conf 3:=(motion r t).continuousAt ((conf_open _).mem_nhds good)
  exact (kernel F tags q good).congr (ev.mono fun p hp=>(field F J φ tp ⟨4,a⟩ r p.1 (fun i=>⟨4,v i⟩) hp).symm)

theorem original (ψ φ:Test 2){r t:ℝ}(tp:0<t)(v:Fin 2→RG17.Free R.family 4)(a:RG17.Free R.family 4)
    (safe:∀x∈tsupport ψ,∀z∈tsupport φ,placed r t x (relative z)∈conf 3):
    let X:=stencil J φ tp ⟨4,a⟩
    let y:=fun x=>reading J φ tp ⟨4,a⟩ r x (fun i=>⟨4,v i⟩)
    Integrable (fun x:Points 2=>ψ x*y x) ∧
      appeared F (d:=fun _:Fin 2=>4) (fun i=>J r 4 (v i)) X r ψ = ∫x:Points 2,ψ x*y x:=by
  let X:=stencil J φ tp ⟨4,a⟩
  let u:=fun i:Fin 2=>J r 4 (v i)
  let A (x z:Points 2):=ψ x*(φ z*integrand J φ tp ⟨4,a⟩ r x (fun i=>⟨4,v i⟩) z)
  have all:Integrable A.uncurry (volume.prod volume):=joint F J ψ φ tp v a safe
  have first(x:Points 2):(∫z:Points 2,A x z)=ψ x*reading J φ tp ⟨4,a⟩ r x (fun i=>⟨4,v i⟩):=by
    change (∫z:Points 2,ψ x*(_*_))=ψ x*(Next.UVStress.dilate tp φ).applyTo _
    rw [integral_const_mul,Next.UVStress.zoom_integral];rfl
  have last(z:Points 2):φ z*query F u (X.offset (t • z)) X.labels none r ψ=∫x:Points 2,A x z:=by
    change φ z*(∫x:Points 2, ψ x*whole S (posed r x) (d:=fun _:Fin 2=>4) u (X.offset (t • z)) X.labels)=_
    rw [←integral_const_mul];apply integral_congr_ae;filter_upwards with x;exact mul_left_comm _ _ _
  refine ⟨all.integral_prod_left.congr (Eventually.of_forall first),?_⟩
  change (Next.UVStress.dilate tp φ).applyTo (fun z=>query F u (X.offset z) X.labels none r ψ)=_
  rw [Next.UVStress.zoom_integral]
  calc
    _=∫z:Points 2,∫x:Points 2,A x z:=integral_congr_ae (Eventually.of_forall last)
    _=∫x:Points 2,∫z:Points 2,A x z:=(integral_integral_swap (f:=A) all).symm
    _=_:=integral_congr_ae (Eventually.of_forall first)

end YM.Integration.WilsonCenteredFourSpatialInterchange
