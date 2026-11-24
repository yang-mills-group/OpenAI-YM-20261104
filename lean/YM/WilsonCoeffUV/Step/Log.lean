import YM.WilsonCoeffUV.Step.Unshifted
/-!
# Exact W projection theorem

Includes all residual action terms, the heat evaluation, and conditional scalar
normalizations. Estimates in cover norm separately. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV
open Wilson Lattice Laurent Exterior Bloch Matrix Precision RG Blue
open Next.Free FreeResolvent Tree Filter Metric Function
open PowerSeries
open scoped Topology ContDiff BigOperators
variable {G:Gauge}{c f:Side}(S:StepData c f)

lemma unspin0 (Ñ:ChartRatio G) : flash (sprig (unhaar (n:=f) Ñ) 0)=jet (unhaar Ñ) := by apply PowerSeries.ext; intro n; simp_rw [sprig_flash,coeff_mk,Nat.zero_add]
lemma spring_pen (q:S.patch.Branches S.kernel G): sprig (jointPen G S) 2 0=shine (orbQ (penQuad G S)) := sprouts_lead (penSmooth G S q) (pen_jets G S q).2.2 (penSym G S)

lemma sterol {P:PChart G f}(p:shellK 2 P)(Ñ:ChartRatio G)(M:Matrix (Woods G f) (Woods G c) ℝ) :
    flash (casePW S Ñ M P)=loom (camber G M) (jet (unhaar Ñ))- loom (groundM G M) (flash (scrub (sprig (jointPen G S) 2)))-loom (camber G M) (flash (scrub P)) := by
  let h i:= finite_shell (sprig_count (unhaar (n:=f) Ñ) 0) i
  let g i:= finite_shell (shell_scrub (sprig_count (jointPen G S) 2)) i
  let t i:= finite_shell (shell_scrub p) i
  let h' i:= fade_finite (h i) (camber G M); let g' i:= fade_finite (g i) (groundM G M); let t' i:= fade_finite (t i) (camber G M)
  rw [←unspin0 Ñ, casePW, flash_sub ?a t', flash_sub h' g', loom_fade _ _ h,loom_fade _ _ g,loom_fade _ _ t]
  case a=> intro i
           have he:= finite_μ (g' i) (-1)
           rw [Pi.sub_apply]; rw [sub_eq_add_neg]; apply finite_add (h' i); simpa only [neg_smul,one_smul] using he

section
variable (F:Forest S.ratio) (H Y:FreeResolvent.FaceRow) (Q:Matrix (Body 1 f) (Body 1 c) ℝ)
variable {Ñ:ChartRatio G}{P:PChart G f}

/-- exact shifted FULL formal action before Haar, including penalty germ -/
def unscaled (P:PChart G f) : Ink (Active G F ⊕ Woods G c) :=
   loom (camSlice G S F (extractV G S F Q)) (flash P) + loom (panSlice G S F (extractV G S F Q)) (flash (sprig (jointPen G S) 2))
/-- positive powers in the shifted, padded integrand, interpreted on the active slice -/
def shot (Ñ:ChartRatio G) (P:PChart G f) := loom (overM G S F) (flash (casePW S Ñ (extractV G S F Q) P))
/-- Centered Gaussian vacuum density-series correction on the active off-tree variables (prior to division by the linkZ) -/
def inside (Ñ:ChartRatio G) (P:PChart G f) := Wick (Woods G c) (treeInverse G S F H 0) (raiseE (shot S F Q Ñ P))

private lemma shell_alg {U:Type} [AddCommGroup U] (a b c d e:U) : a-b-c=a-(d+c+(e+b))+(d+e):=by abel

lemma shot_bill (p:shellK 2 P)(e:P 0=shine (orbQ (precisionC G f H)))(hz:S.patch.Branches S.kernel G) (hu:Inputs S Q (H.acts f) (Y.acts c)) (hs:(H.acts f).transpose=H.acts f) :
    shot S F Q Ñ P= loom (camSlice G S F (extractV G S F Q)) (jet (unhaar Ñ))- unscaled S F Q P + (holdUp (Active G F) (orbC (precisionC G c Y))+bodyQ (Woods G c) (treeMatrix G S F H)) := by
  have hb (M:Matrix (Woods G f) (Woods G c) ℝ)(v) : loom (overM G S F) (loom (camber G M) v)= loom (camSlice G S F M) v:= DFunLike.congr_fun (loom_loom (camber G M) (overM G S F)) v
  have hk (M:Matrix (Woods G f) (Woods G c) ℝ)(v) : loom (overM G S F) (loom (groundM G M) v)= loom (panSlice G S F M) v:= DFunLike.congr_fun (loom_loom (groundM G M) (overM G S F)) v
  let M:= extractV G S F Q
  let b:=loom (panSlice G S F M) (flash (scrub (sprig (jointPen G S) 2)))
  let c':=loom (camSlice G S F M) (flash (scrub P))
  let u:=loom (camSlice G S F M) (orbC (precisionC G f H)); let v:=loom (panSlice G S F M) (orbC (penQuad G S));
  let a:=loom (camSlice G S F M) (jet (unhaar Ñ))
  have hS : shot S F Q Ñ P=a-b-c' := by
    unfold shot; rw [sterol S p Ñ,map_sub,map_sub,hb,hk,hb]
  have hU : unscaled S F Q P=u+c'+(v+b) := by
    unfold unscaled
    have hw := spring_pen S hz
    let E:= sprig (jointPen G S) 2
    have he : loom (camSlice G S F M) (flash P)=u+c' := by rw [flash_scrub P (precisionC G f H) e,map_add]
    have ht : loom (panSlice G S F M) (flash E)=v+b := by rw [flash_scrub E (penQuad G S) hw,map_add]
    exact congr_arg₂ (· + ·) he ht
  have hy : holdUp (Active G F) (orbC (precisionC G c Y))+bodyQ (Woods G c) (treeMatrix G S F H)=u+v := (close_square G S F H Y Q hu hs).symm
  rw [hS,hU,hy]; exact shell_alg a b c' u v
lemma wedgeW (p:shellK 2 P)(hh:LocalRatio Ñ)(hz:S.patch.Branches S.kernel G)(g:(H.acts f).transpose=H.acts f)(hp:∀ i,Pure (P i)) :
    flash (summer S F H Q Ñ P) = logOf (inside S F H Q Ñ P) := by
  classical
  let M:=extractV G S F Q
  let B := casePW S Ñ M P
  let Γ:= covariance G S F H; let T:= treeInverse G S F H 0; let I:= reveal G S F
  let v:=reveal G S F; let O:=overM G S F; let W:= path (U:=Woods G c)
  have h : O=bridgeM (reveal G S F) (Woods G c):=rfl
  have hZ : constantCoeff (flash B)=0:=flash_blank (pack_zero S hh)
  have hΓ : Γ= I*T*I.transpose:= rfl
  have hT: T.transpose=T:= by unfold T treeInverse resolve; rw [zero_smul,add_zero,transpose_nonsing_inv,treeMatrix,transpose_submatrix,full_symmetric _ g]
  have ht : loom O= railCov I W:= bridge_rail _
  have hsc : inside S F H Q Ñ P=Wick (Woods G c) Γ (raiseE (flash B)):=by
    unfold inside shot; change Wick _ T (raiseE ((loom O) (flash B)))=_
    rw [← raise_map _ (by simp [loom]) hZ, ht, W_linear _ _ (by rw [hΓ,transpose_mul,transpose_mul,hT,transpose_transpose,Matrix.mul_assoc]) hT hΓ,show train W=RingHom.id _ from train_id,RingHom.id_apply]
  have hB : shellK 2 B:= pack_band S p
  have hy : B 0=0:= pack_zero S hh
  have hc:=stops_abr (fillSlots (Woods G c) Γ) hB hy
  let J (e): Gen ℝ (Joint G f c) := ∑ j∈Finset.range (3+3*e), abr (fillSlots (Woods G c) Γ) B j e
  rw [hsc,wick_log hB hy (pack_pure S hh hz hp),at_one _ _ hc, plug_project]
  change _=loom _ (flash J); rw [loom_fade _ J (fun i=> finite_sum fun j _=> finite_stops hc j i)]; rfl
lemma inside_mass (hh:LocalRatio Ñ) : constantCoeff (inside S F H Q Ñ P)=1 := by
  have hz: constantCoeff (shot S F Q Ñ P)=0:= by rw [shot,loom,← coeff_zero_eq_constantCoeff_apply,coeff_map, coeff_zero_eq_constantCoeff_apply,flash_blank (pack_zero S hh),map_zero]
  rw [inside,Wick,projectZero,←coeff_zero_eq_constantCoeff_apply,coeff_map,overlay_apply,coeff_zero_eq_constantCoeff_apply,raise_one hz,glaze_one,map_one]
theorem winter_read (p:shellK 2 P)(hh:LocalRatio Ñ)(hz:S.patch.Branches S.kernel G)(g:(H.acts f).transpose=H.acts f)(hp:∀ i,Pure (P i)) :
    flash (winter S F H Y Q Ñ P)=orbC (precisionC G c Y)- logOf (inside S F H Q Ñ P) + soil (plugζ S Ñ) := by
  let h i:= finite_shell (summer_band S F H Q hh p) i
  let hy : shellK 2 (flatPal (precisionC G c Y)) := flat_count _
  rw [winter,flash_add (finite_shell (shell_sub hy (summer_band S F H Q hh p))) (finite_shell (uband_length _ _ 2)), flash_sub (finite_shell hy) h, uband_flash, wedgeW S F H Q p hh hz g hp, flat_flash]

end
end YM.WilsonCoeffUV
