import YM.RG17.Relative
import YM.OPE.Nesting.Motions

/-!
# Absolute smear adapter
 Exact continuum shape charge with absolute height for spectators.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG17
open Function Set WithLp Filter MeasureTheory Extraction Table OPE OPE.Orbits
open scoped BigOperators Topology Classical ContDiff

variable {G:Gauge} {C:Family G}{S:Table C.book}{f:Extraction.Order} {F:Spec.Final C f S}
    (X:External C S){n:ℕ}

private def dust {n k:ℕ}(φ:Test (k+1))(ψ:Test n)(r:ℝ)(H:Points (n+k)→ℂ)(u:E4)(q:Points n × Points k):ℂ :=
    φ (openRoot (u,q.2))*ψ (r⁻¹ • (q.1 - echo n u))* H (pad q)
lemma dust_int (ψ:Test n){r:ℝ}(hr:r≠0)(hx:packs X r ψ){H:Points (n+X.n)→ℂ}(he:ContinuousOn H (conf _)) : Integrable (uncurry (dust X.test ψ r H)) (volume.prod volume) := by
    let A:= tsupport ψ; let B:=tsupport X.test; let V:=openRoot (k:=X.n)
    let y : E4 × Points n × Points X.n → Points n × Points (X.n+1) := fun p=> (r⁻¹ • (p.2.1 - echo n p.1), V (p.1,p.2.2))
    let Z := y ⁻¹' (A ×ˢ B)
    let v := dust X.test ψ r H
    have hp:Continuous y :=by
       have ha:Continuous (fun p : E4 × Points n × Points X.n=> (V (p.1,p.2.2))):=V.continuous.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
       refine Continuous.prodMk (f:=fun p:E4 × Points n × Points X.n=> r⁻¹ • (p.2.1 - echo n p.1)) ?_ ha
       fun_prop
    let w (p:Points n × Points (X.n+1)) : E4 × Points n × Points X.n:= ((V.symm p.2).1,r • p.1+ echo n ((V.symm p.2).1),(V.symm p.2).2)
    have hQ:LeftInverse w y:=by rintro ⟨u,x,p⟩; simp [w,y,hr]
    have hw:Continuous w:=by dsimp only [w]; fun_prop
    have hc : IsCompact Z := (((ψ.hasCompactSupport.prod X.test.hasCompactSupport).image hw).of_isClosed_subset (((ψ.hasCompactSupport.prod X.test.hasCompactSupport).isClosed).preimage hp) (fun p hx=>⟨y p,hx,hQ p⟩))
    have hP(q:E4 × Points n × Points X.n)(h:q∉Z): uncurry v q=0 := by
       dsimp only [uncurry,dust,v]; by_cases hz:(y q).2∈ B
       · have ht:(y q).1∉A:= fun hi=> h ⟨hi,hz⟩
         rw [show ψ _=0 from image_eq_zero_of_notMem_tsupport ht]; simp
       rw [show X.test _=0 from image_eq_zero_of_notMem_tsupport hz]; simp
    have hK: HasCompactSupport (uncurry v):= hc.of_isClosed_subset isClosed_closure (closure_minimal (fun p hx=> by by_contra h; exact hx (hP p h)) hc.isClosed)
    apply Continuous.integrable_of_hasCompactSupport _ hK; apply continuous_iff_continuousAt.mpr; intro x
    by_cases hv:x ∈ Z
    · have hh: absCord n X.n r (y x) = pad x.2:= by simp only [absCord,y,V,ContinuousLinearEquiv.symm_apply_apply,smul_inv_smul₀ hr _, sub_add_cancel]
      have hx : pad x.2∈ conf _:= hh ▸ (hx ⟨_, show _ ∈ _ from hv,rfl⟩)
      exact (((X.test.continuous.comp hp.snd).continuousAt).mul ((ψ.continuous.comp hp.fst).continuousAt)).mul
        (((he _ hx).continuousAt ((conf_open _).mem_nhds hx)).comp (f:=(pad (n:=n) (k:=X.n)) ∘ (Prod.snd:E4 × Points n × Points X.n→_)) (((pad (n:=n) (k:=X.n)).continuous.comp continuous_snd).continuousAt))
    apply ContinuousAt.congr (f:=fun _ : E4 × Points n × Points X.n=> (0:ℂ)) continuousAt_const; filter_upwards [hc.isClosed.isOpen_compl.mem_nhds (show x∈Zᶜ from hv)] with p hp using (hP p hp).symm

lemma evaluate_shape (ψ: Test n){r:ℝ}(hr:0<r)(hx:packs X r ψ)(H:Points (n+X.n)→ℂ)(he:ContinuousOn H (conf _))
    (hh: Integrable (fun z:Points (X.n+1)=> X.test z * ψ.applyTo (fun y=>H (absCord n X.n r (y,z))))) :
     (shape X r ψ).applyTo H=∫ z:Points (X.n+1), X.test z * ψ.applyTo (fun y=>H (absCord n X.n r (y,z))) := by
    let φ:= X.test; let J:ℂ:= (r:ℂ)⁻¹ ^ (4*n); let D:= dust φ ψ r H; let A:= pad (n:=n) (k:=X.n); let V:= openRoot (k:=X.n)
    let Q (x:Points (X.n+1)) := X.test x * ψ.applyTo (fun y=>H (absCord n X.n r (y,x)))
    have hP : Integrable D.uncurry (volume.prod (volume.prod volume)):= dust_int X ψ hr.ne' hx he
    have hk(q:Points n × Points X.n): shape X r ψ (A q) * H (A q)= J * ∫ u:E4,D u q := by
        simp_rw [shaped X hr.ne' hx,absolute,D,dust,integral_mul_const, A,ContinuousLinearEquiv.symm_apply_apply,φ,J]; ring
    have hV : Integrable (Q ∘ V) := by exact (openRoot_volume.integrable_comp_emb V.toHomeomorph.measurableEmbedding).mpr hh
    have hz(u:E4)(p:Points X.n): J* (∫ x:Points n,D u (x,p))= (Q ∘ V) (u,p):=by
        let G (x:Points n):= D u (x + echo n u,p)
        let z:= V (u,p)
        rw [← integral_add_right_eq_self (fun x:Points n=> D u (x,p)) (echo n u)]
        have he := Measure.integral_comp_smul_of_nonneg volume G r (hR:=hr.le); rw [Next.UVStress.point_dimension, Complex.real_smul] at he
        rw [show J=↑((r^(4*n))⁻¹) by simp [J,inv_pow], ← show (∫ x:Points n,G (r•x))=_ from he]
        change (∫ x:Points n,G (r•x)) = φ z* ∫ x:Points n, ψ x* H (absCord n X.n r (x,z)); rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards with x
        simp only [G,D,dust,add_sub_cancel_right,inv_smul_smul₀ hr.ne']; dsimp only [z,V,absCord]; rw [ContinuousLinearEquiv.symm_apply_apply,mul_assoc]
    calc
         _ = ∫ q: Points n × Points X.n, (shape X r ψ) (A q) * H (A q) := (pad_volume.integral_comp A.toHomeomorph.measurableEmbedding (fun x=> shape X r ψ x * H x)).symm
         _ = ∫ q: Points n × Points X.n,J* ∫ u:E4,D u q:= by simp_rw [hk]
         _ = ∫ u:E4,J* ∫ q: Points n × Points X.n,D u q:=by
               rw [integral_const_mul,integral_const_mul]; refine congr_arg (J * ·) (integral_integral_swap (f:=D) hP).symm
         _ = ∫ u:E4,∫ v:Points X.n, (Q ∘ V) (u,v) :=by
               apply integral_congr_ae; filter_upwards [hP.prod_right_ae] with u hu
               simp_rw [← hz]; rw [integral_const_mul]; exact congr_arg (J * ·) (integral_prod_symm _ hu)
         _ = ∫ p:E4 × Points X.n, (Q ∘ V) p := (integral_prod _ hV).symm
         _ = _ := openRoot_volume.integral_comp V.toHomeomorph.measurableEmbedding Q

variable {d:Fin n→ℕ}{U:Fin (n+X.n)→ S.Tag}
include F
lemma whole_absolutely (v:Labels S d){r:ℝ}{x:Points n}{z:Points (X.n+1)}(h:absCord n X.n r (x,z) ∈ conf _) :
    whole S (posed r x) v (X.offset z) X.labels = S.useAt S (absCord n X.n r (x,z)) (Fin.append (tags v) X.tags):=by
    obtain ⟨⟨u,y⟩,rfl⟩:= openRoot.surjective z
    let a:= r • x + echo n u; let b:=pad (a,y)
    let e: Fin n ⊕ Fin X.n ≃ Fin (n+X.n):= finSumFinEquiv
    let p:= Fin.append (names v) (names X.labels); have hh:= (rooted_packing ..).mpr h
    simp only [absCord,ContinuousLinearEquiv.symm_apply_apply] at h ⊢
    have hz: whole S (posed r x) v (X.offset (openRoot (u,y))) X.labels= whole S a.ofLp v y.ofLp X.labels:=by
       have he:(fun i=> posed r x i+u)=a.ofLp:=funext fun i=>rfl
       have hY:(fun j=>X.offset (openRoot (u,y)) j + u)=y.ofLp:=funext fun j=>by simp [External.offset,openRoot_eq,Points.cons]
       rw [← he,← hY]; exact (Nesting.Motion.whole_shift F.room.kernel v X.labels hh).symm -- field projection?
    have ha: beside a.ofLp y.ofLp=b.ofLp ∘ e:=by
       funext i; cases i <;> simp [b,pad_xy,comp,e]
    have hv: beside (names v) (names X.labels)= p ∘ e:=by funext i; cases i <;> simp [p,e,comp]
    rw [hz,whole_observed,ha,hv,perm_observe S F.room.kernel.laws.toSymmetric e _ h]
    have ht:= (named_fin S F.room.kernel.laws.toSymmetric (x:=b) p h).trans (S.at_project S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) h p).symm
    refine ht.trans (congr_arg _ ?_); funext i; cases i using Fin.addCases <;> simp only [p,Function.comp_apply, Fin.append_left, Fin.append_right]; all_goals change (⟨_,S.project _ (S.representative _ _)⟩:S.Tag)=_; rw [S.rep]; rfl
lemma chargedShape (v:Labels S d)(ψ: Test n){r:ℝ}(hr:0<r)(hx:packs X r ψ) (hh:Integrable (fun z:Points (X.n+1)=> X.test z* query F v (X.offset z) X.labels none r ψ)) :
    (shape X r ψ).applyTo (fun y=>S.useAt S y (Fin.append (tags v) X.tags)) = appeared F v X r ψ :=by
    let H y:= S.useAt S y (Fin.append (tags v) X.tags)
    have he:ContinuousOn H (conf _):= (Next.UVStress.smoothDisc F.room.kernel.smooth _).continuousOn
    have hz (z:Points (X.n+1)): X.test z * ψ.applyTo (fun y=>H (absCord n X.n r (y,z)))= X.test z * query F v (X.offset z) X.labels none r ψ:=by
       by_cases h:z∈tsupport X.test
       · refine congr_arg (X.test z * ·) (integral_congr_ae ?_); filter_upwards with y
         by_cases hY:y∈tsupport ψ
         · refine congr_arg (ψ y * ·) (whole_absolutely (F:=F) X v (hx ⟨(y,z),⟨hY,h⟩,rfl⟩)).symm
         simp [image_eq_zero_of_notMem_tsupport hY]
       simp [image_eq_zero_of_notMem_tsupport h]
    exact (evaluate_shape X ψ hr hx H he (hh.congr (Eventually.of_forall (fun z=> (hz z).symm)))).trans (integral_congr_ae (Eventually.of_forall hz))
end YM.RG17
