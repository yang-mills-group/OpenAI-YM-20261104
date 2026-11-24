import YM.WilsonCoeffUV.FieldRead.Stencil
/-!
# Reading back actual stencil calibration with all valence of gains
Combination in radial variables. Never discard shifted terms of the same α.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 40000
noncomputable section
namespace YM.WilsonCoeffUV.Cosmos
open Filter Function Set Laurent Lattice RG Exterior Precision Next.Free Gauge Power
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Blue FreeResolvent Bank
open Embroider Fountain Work.G05
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G:Gauge}{r h D l n k e:ℕ}{A C s t :ℝ}{F:Frame G h}(T:SectionData F)

lemma polana (i:F.Index)(x:Lawn (Toe T)) (r:ℕ): Tensor.diagonal (Tensor.coeff (collar T i) r 0) x=∑ u,(rye (collar T i) r u) * ∏ j, x (u j):=by
    have he:=rayon (collar T i) r x; rw [jet_apply,Blue.toll] at he; exact he.symm

def reading (X:Snap G h): Lawn (Toe T):= (vixen T).symm (Film.localLane X)
@[simp] lemma reading_at (X:Snap G h)(i:Toe T): reading T X i=flex (dance T i) X:=by unfold flex dance; rw [feather_at]; rfl
lemma reading_smooth : ContDiffAt ℝ ω (reading T) 0:= ((vixen T).symm.toContinuousLinearMap.contDiff.contDiffAt).comp (0:Snap G h) (Film.local_smooth _)
lemma reading_root : reading T 0=0:=by unfold reading; rw [Film.local_zero,map_zero]

def sheeted (v: F.Index)(r:ℕ):Snap G h→ℝ:= Tensor.diagonal (Tensor.coeff (collar T v) r 0) ∘ reading T
lemma mark (v:F.Index)(r:ℕ): ContDiffAt ℝ ω (sheeted T v r) 0:= (Tensor.diag_smooth (Tensor.coeff (collar T v) r 0) ω).contDiffAt.comp 0 (reading_smooth T)
lemma marked (v:F.Index)(r:ℕ)(X:Snap G h): sheeted T v r X= ∑ u: Fin r → Toe T, floatA T v r (dance T ∘ u)*mite (dance T ∘ u) X:=by
    simp_rw [sheeted, Function.comp_apply,polana,reading_at]; apply Finset.sum_congr rfl; intro u _; rw [apt]; rfl

section
variable (w:h<D)

lemma shrubbery (v i:Alma F)(r:ℕ)(u:Fin r→YForest G): (carte T w v r u) (brow F i D)=(if notar F v=notar F i then floatA T (sheet F v) r u else 0):=by unfold carte; rw [smul_apply,packBloom]; split<;>simp
lemma foreign (v i:Alma F)(r:ℕ)(u:notar F v ≠ notar F i): arret (brow F i D) (carte T w v r) h l=0:=by unfold arret; simp_rw [shrubbery,if_neg u,zero_smul,tsum_zero]
lemma glancing (i v:Alma F)(r:ℕ)(H:notar F v=notar F i)(X:Snap G h):
    Tensor.diagonal (latent (arret (brow F i D) (carte T w v r) h l)) X = leading l (fun t:ℝ=> sheeted T (sheet F v) r (t • X)):=by
    let a:=sheet F v
    let A:=carte T w v r
    obtain ⟨C,hc⟩:=paidAnn T a r 1
    have hx: Twig 0 1 (C*‖jewelBloom w v‖) A:= by refine ⟨mul_nonneg hc.1 (norm_nonneg _),fun j=>?_⟩; unfold A carte; rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (hc.2 j) (norm_nonneg _)).trans_eq (by ring)
    rw [lat_sum _ A _ _ hx zero_lt_one]; unfold A; simp_rw [shrubbery,if_pos H, marked]
    let f (u:Fin r→Toe T) (t:ℝ):= mite (dance T ∘ u) (t•X); let g (u:Fin r→Toe T):= rye (collar T a) r u
    have hg u:ContDiffAt ℝ (↑l) (f u) 0:= by
       let L: ℝ→L[ℝ]Snap G h:=(ContinuousLinearMap.id ℝ ℝ).smulRight X
       have hC: ContDiffAt ℝ (↑l) (mite (dance T ∘ u)) (L 0):=by rw [map_zero]; exact (mite_smooth ..).of_le le_top
       exact hC.comp 0 L.contDiff.contDiffAt
    let P:=fun u:Fin r→Toe T=> dance T ∘ u
    have hi: Injective P:= fun x y p=>funext fun k=>dance_inj T (congr_fun p k)
    rw [tsum_eq_sum (s:=Finset.univ.image P) (fun x hp=>by rw [treasury _ _ _ (fun ⟨i,hh⟩=>hp (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hh⟩)),zero_mul]), Finset.sum_image (fun i _ j _ q=>hi q)]; simp_rw [apt]
    change _ = leading l (fun t=>∑ u,g u • f u t)
    rw [lead_sum _ (fun u t=> g u • f u t) (fun i _=> ContDiffAt.const_smul (g i) (hg i))]; apply Finset.sum_congr rfl; intro u _; unfold P; rw [lost, apt]
    exact (lead_sc (hg u) _).symm

private lemma ivory (i v:Alma F)(r l:ℕ)(H:notar F v=notar F i): latent (arret (brow F i D) (carte T w v r) h l)=Tensor.coeff (sheeted T (sheet F v) r) l 0:=by
    let a:=sheet F v; let K:=carte T w v r
    obtain ⟨C,hc⟩:=paidAnn T a r 1
    have hx: Twig 0 1 (C*‖jewelBloom w v‖) K:= by refine ⟨mul_nonneg hc.1 (norm_nonneg _),fun j=>?_⟩; unfold K carte; rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (hc.2 j) (norm_nonneg _)).trans_eq (by ring)
    have hg (p:Fin l→ Snap G h) (t:Equiv.Perm (Fin l)):= arret_seal (brow F i D) K h l hx zero_lt_one (fun j=>casing G h (p j)) t
    refine Tensor.ext_diag _ _ (fun y t=>hg y t) (Tensor.coeff_symm (f:=sheeted T a r) ((mark ..).of_le le_top)) (funext fun X=>?_)
    exact (glancing T w _ _ r H X).trans (leading_tensor X _ ((mark ..).of_le le_top))

lemma bona (v:Alma F) (H:Hol G)(hq:T.Sound H)(n l:ℕ)(hv:n≤h)(hl:l≤h)(i:Alma F)(u:notar F v=notar F i):
    let R:=∑ r∈Finset.range (l+1), arret (brow F i D) (carte T w v r) h l
    seedTile R n=(gradePart (n,l) (F.basis (sheet F v))).val:=by
   classical
   intro R; let P:=Place.copy F (sheet F v); let z:=sheet F v
   have he : F.basis z= Parts.archive (Film.still T hq P):= by rw [Film.corner T hq P, show P=F.coords (F.basis z) from Eq.symm (Frame.coords_basis _ _), F.coords.symm_apply_apply]
   rw [show F.basis _ = _ from he, Parts.capture _ hv hl,seedTile]
   let T':=collar T z; let S:= Finset.range (l+1); let f:=reading T; let M r:=sheeted T z r; let g:= T' ∘ f
   have heq: Complex.ofRealCLM ∘ g = Place.column T z ∘ Film.localLane (d:=h):= by
      funext X; change Complex.ofReal (collar T z (reading T X))=_; rw [shawl T z H hq,reading,(vixen T).apply_symm_apply]; rfl
   have ht: ContDiffAt ℝ (↑l) f 0:= (reading_smooth T).of_le le_top
   have hX:f 0=0:= reading_root _
   have hf: ContDiffAt ℝ (↑l) T' 0:= (follicle T z).of_le le_top
   have hp: ContDiffAt ℝ (↑l) g 0:= (hX.symm ▸ hf).comp 0 ht
   let Δ (x:Snap G h):=∑ i∈ S,M i x
   have hΔ: Δ= blockTaylor l T' ∘ f:= by funext x; simp [Δ,M,sheeted,blockTaylor,f,T',S]
   have har:iteratedFDeriv ℝ l g 0=iteratedFDeriv ℝ l Δ 0:=by rw [hΔ]; exact jets_comp (d:=l) ht ht (hX.symm ▸ hf) (blockTaylor_contDiff l T' _).contDiffAt rfl (fun _ _=>rfl) (by rw [hX]; intro _ t; exact Eq.symm (blockTaylor_jets hf _ t)) l le_rfl
   apply congr_arg (tile · n); change Complex.ofRealCLM.compContinuousMultilinearMap (latent R)=Tensor.coeff (Place.column T z ∘ Film.localLane (d:=h)) l 0
   rw [← heq]; ext1 U
   unfold Tensor.coeff; rw [Complex.ofRealCLM.iteratedFDeriv_comp_left hp le_rfl,har]
   have hS : iteratedFDeriv ℝ l Δ 0=∑ i∈ S,iteratedFDeriv ℝ l (M i) 0:= iteratedFDeriv_fun_sum_apply (f:=M) (fun i _=> (mark ..).of_le le_top)
   rw [hS]; change Complex.ofRealCLM (latent R U) = _
   have hr : latent R U= ∑ i∈S, (l.factorial:ℝ)⁻¹ • iteratedFDeriv ℝ l (M i) 0 U:=by
       rw [Fountain.latent,ContinuousMultilinearMap.compContinuousLinearMap_apply]; unfold R; rw [sum_apply]; exact Finset.sum_congr rfl fun j _=> DFunLike.congr_fun (ivory T w i v j l u) U
   rw [hr,smul_apply]; change Complex.ofRealCLM _=(l.factorial:ℝ)⁻¹ • Complex.ofRealCLM ((∑ i∈ S,iteratedFDeriv ℝ l (M i) 0) U); rw [_root_.map_sum]; simp only [map_smul,sum_apply,map_sum,Finset.smul_sum]

private lemma shewn (i v:Alma F)(b:Bid.pop T)(z:valence F i=e+valence F v) : glean F (anthem T w v) e i = ∑ r∈Finset.range (valence F i+1), echoS F (carte T w v r) i:=by
    unfold glean; apply Finset.sum_congr rfl; intro r _; split
    next h=> unfold anthem; rw [show valence F v+(e+r-valence F i)=r by omega,shine_lit]
    next h=> have hp: carte T w v r=0:= by
                 funext i; unfold carte; rw [aca T _ (show r< valence F v from by omega) b]; change (0:ℝ) • _= _; exact zero_smul ..
             rw [hp, echo_zero]
private lemma sent (i v:Alma F)(e:ℕ)(t:valence F i≠ e+valence F v) : glean F (anthem T w v) e i=0:=by
    unfold glean; apply Finset.sum_eq_zero; intro r h; split
    next p=> unfold anthem; rw [shine_dark (by omega),echo_zero]
    rfl

lemma cornerRead (i v:Alma F)(H:Hol G)(t:T.Sound H)(p:Bid.pop T)(e:ℕ): glean F (anthem T w v) e i=if e=0 then if i=v then 1 else 0 else 0:=by
    by_cases H': valence F i=e+valence F v
    · rw [shewn T w i v p H']; by_cases he:notar F v=notar F i
      ·
        let V:= gradePart (weave F i,valence F i) (F.basis (sheet F v))
        let R:=∑ r∈Finset.range (valence F i+1),arret (brow F i D) (carte T w v r) h (valence F i)
        have ht : seedTile R (weave F i)=V.val:= bona T w v H t _ _ (F.bound _) (valence_cap ..) i he
        have hu : F.coords V=Bell F (weave F i) (valence F i) R:=by
           have hx: seedTile R (weave F i)∈localFields G h:= ht.symm ▸ V.property
           rw [detecting F R (weave F i) hx]; exact congr_arg F.coords (Subtype.ext ht.symm)
        have hz : (∑ r∈Finset.range (valence F i+1),echoS F (carte T w v r) i)=(F.coords V (sheet F i)).re:=by rw [hu]; unfold R; rw [map_sum, Finset.sum_apply,Complex.re_sum]; rfl
        unfold V at hz; rw [hz,ticket_grade];
        rw [if_pos (show (weave F i,valence F i)=(F.grades (sheet F i)) from rfl), F.coords_basis]
        by_cases H:i=v
        · subst i; have hp:e=0:= by omega
          rw [if_pos hp,if_pos rfl,Pi.single_eq_same]; rfl
        rw [if_neg H, Pi.single_eq_of_ne (show sheet F i≠sheet F v from fun t=>H (Subtype.ext (Prod.ext t he.symm)))]; simp
      rw [Finset.sum_eq_zero]; · rw [if_neg (show i≠v from fun b=>he (congr_arg (notar F) b).symm)]; simp
      intro r _; unfold echoS trellis; rw [foreign T w v i r he,map_zero]; rfl
    rw [sent T w i v e H']; by_cases hv:e=0
    · rw [if_pos hv, if_neg]; intro b; apply H'; rw [b,hv]; simp
    rw [if_neg hv]
end
end YM.WilsonCoeffUV.Cosmos
