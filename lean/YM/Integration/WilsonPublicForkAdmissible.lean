import YM.Integration.WilsonPublicForkSupport
import YM.RG17.Tested

/-! A supported pair of tests on the actual moving two-site detector owns
its packing and its original ordinary integral at that same radius. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPublicForkAdmissible
open Function Filter Set MeasureTheory Table Spec RG17 OPE OPE.Orbits PhysMS Maxwell Climb
open WilsonMacroscopicRichSignedAmplitude WilsonMacroscopicRichTestGeometry
open scoped Classical Topology
variable {n:ℕ}{G:Gauge}{C:Family G}{f:Extraction.Order}{S:Table C.book}

theorem covered (J:ℝ→tower S)(φ:Test 2){r t:ℝ}(tp:0<t)(w:(Bel C.book).Tag)(ψ:Test n)
    (clear:∀x∈tsupport ψ,∀z∈tsupport φ,Injective (beside (posed r x) (sole (t • relative z 0)))):
    packs (stencil J φ tp w) r ψ:=by
  let X:=stencil J φ tp w
  rintro _ ⟨⟨x,z⟩,⟨hx,hz⟩,rfl⟩
  let a:=t⁻¹ • z
  have ha:a∈tsupport φ:=by
    let P: Set (Points 2):=(fun v:Points 2=>t⁻¹ • v) ⁻¹' tsupport φ
    refine (show tsupport (Next.UVStress.dilate tp φ)⊆P from closure_minimal (fun v hv=>?_)
      ((isClosed_tsupport _).preimage (by fun_prop))) hz
    apply subset_closure;change φ _≠0
    change (((t^(4*2))⁻¹:ℝ):ℂ)*φ (t⁻¹ • v)≠0 at hv
    exact fun vanish=>hv (by rw [vanish,mul_zero])
  have za:t • a=z:=by dsimp [a];rw [smul_smul,mul_inv_cancel₀ tp.ne',one_smul]
  let ff:Fin n ⊕ Fin 1 ≃ Fin n ⊕ Unit:=Equiv.sumCongr (Equiv.refl _) WilsonPublicForkSupport.one
  have eq:beside (posed r x) (X.offset z)=(beside (posed r x) (sole (t • relative a 0))) ∘ ff:=by
    funext i;rcases i with i|i
    · rfl
    · change Fin 1 at i
      have si:i=0:=Subsingleton.elim _ _;subst i
      change z 1-z 0=t • (a 1-a 0)
      rw [smul_sub]
      exact congrArg₂ (fun u v:E4=>u-v) (congrArg (fun v:Points 2=>v 1) za).symm (congrArg (fun v:Points 2=>v 0) za).symm
  apply (RG17.rooted_packing X r x z).mp
  rw [eq];exact (clear x hx a ha).comp ff.injective

theorem integrable (F:Final C f S)(X:External C S)(r:ℝ){d:Fin n→ℕ}(v:Labels S d)(ψ:Test n)
    (packed:packs X r ψ):Integrable (fun z:Points (X.n+1)=>X.test z*query F v (X.offset z) X.labels none r ψ):=by
   let A y x:= X.test y * (ψ x* whole S (posed r x) v (X.offset y) X.labels)
   let K':Set (Points (X.n+1) × Points n):= tsupport X.test ×ˢ tsupport ψ
   have hP(q:Points (X.n+1) × Points n)(h:q∉ K'): uncurry A q=0:=by
       change X.test q.1 * _= _
       by_cases hp:q.1∈tsupport X.test
       · have hh:q.2∉ tsupport ψ:= fun hv=> h ⟨hp,hv⟩
         simp [image_eq_zero_of_notMem_tsupport hh]
       simp [image_eq_zero_of_notMem_tsupport hp]
   have hy:IsCompact K':= X.test.hasCompactSupport.prod ψ.hasCompactSupport
   have hM: HasCompactSupport (uncurry A) := hy.of_isClosed_subset isClosed_closure (closure_minimal (fun x hx=>by
       by_contra h; exact hx (hP x h)) hy.isClosed)
   have hB:Continuous (uncurry A):=by
       refine continuous_iff_continuousAt.mpr fun z=> ?_
       by_cases h:z∈ K'
       · let C' (q:Points (X.n+1) × Points n):Loc (Fin n) (Fin X.n):=(posed r q.2,0,X.offset q.1)
         have he:Injective (beside (posed r z.2) (X.offset z.1)):=
           (RG17.rooted_packing X r z.2 z.1).mpr (packed ⟨(z.2,z.1),⟨h.2,h.1⟩,rfl⟩)
         refine ((X.test.continuous.comp continuous_fst).continuousAt).mul (g:=(fun z:Points (X.n+1) × Points n=> ψ z.2 * whole S (posed r z.2) v (X.offset z.1) X.labels)) ?_
         exact ((ψ.continuous.comp continuous_snd).continuousAt).mul ((whole_cont_at v X.labels _ F.room.kernel he).comp (f:=C')
           (((posed_continuous r).comp continuous_snd|>.prodMk (continuous_const.prodMk (X.continuous_offset.comp continuous_fst))).continuousAt))
       refine ContinuousAt.congr (f:=fun _ : Points (X.n+1) × Points n=> (0:ℂ)) continuousAt_const
        ((show ∀ᶠ x in 𝓝 z,x ∉ K' from hy.isClosed.isOpen_compl.mem_nhds (show z∈ K'ᶜ from h)).mono fun x hx=> (hP x hx).symm)
   have hv : Integrable (uncurry A) (volume.prod volume):= hB.integrable_of_hasCompactSupport hM
   have hz(y:Points (X.n+1)):(∫ x:Points n,A y x)= X.test y * query F v (X.offset y) X.labels none r ψ:=by unfold A; rw [integral_const_mul]; rfl
   exact hv.integral_prod_left.congr (Eventually.of_forall fun z=> hz z)
end YM.Integration.WilsonPublicForkAdmissible
