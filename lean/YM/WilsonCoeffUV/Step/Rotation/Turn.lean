import YM.WilsonCoeffUV.Step.Rotation.Earth
import YM.WilsonCoeffUV.Ward.AxisColor
/-!
# Fulfillment of auxiliary bend and cross-tree W equalities

Formal ordinary tori, no estimates on masked or period-collapse densities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Power.Freedom
open Wilson Lattice Laurent Exterior Bloch Matrix Precision Stationary RG Blue
open Next.Free FreeResolvent Tree Work.F05 Function Filter Gauge PowerSeries
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {c f : Side}{G:Gauge}(S:StepData c f)
variable (B T:Forest S.ratio)
variable (K Y:FreeResolvent.FaceRow) (Q:Matrix (Body 1 f) (Body 1 c) ℝ){Ñ:ChartRatio G}{P:PChart G f}
variable (hq:S.patch.Branches S.kernel G)(h: Inputs S Q (K.acts f) (Y.acts c))(hs:(K.acts f).transpose= K.acts f)
    (p: LocalRatio Ñ)(w:Interlace K P)
private lemma shot_floor (p:LocalRatio Ñ): constantCoeff (shot S B Q Ñ P)=0 := floor_pres (T:=loom (overM G S B)) (by simp [loom]) (flash_blank (pack_zero S p))
section
variable (e:B.Free≃ T.Free)
include hq h hs p w
lemma assembled :
    let M:=extractV G S B Q; let M':=extractV G S T Q
    let L:=loom (beam S e (G:=G))
    let I:=onKey (G:=G) e
    Blue.Freedom.Bend (shot S B Q Ñ P) (L (shot S T Q Ñ P))
      (unscaled S B Q P) (L (unscaled S T Q P))
      (loom (camSlice G S B M) (jet (unhaar Ñ))) (L (loom (camSlice G S T M') (jet (unhaar Ñ))))
      (orbC (precisionC G c Y)) (internal S e M M') (treeMatrix G S B K) ((treeMatrix G S T K).submatrix I I) := by
  intro M M' L I
  have hz (B:Forest S.ratio) : constantCoeff (loom (camSlice G S B (extractV G S B Q)) (jet (unhaar Ñ)))=0 := by apply floor_pres (by simp [loom]); rw [jet_lead,unhaar_zero p,map_zero]
  have hI := primalSweeps (G:=G) S (B:=B) Q
  have hT := primalSweeps (G:=G) S (B:=T) Q
  refine ⟨internal_zero ..,internal_green ..,det_anchor S e M M' Ñ p hI hT,hz B,floor_pres (by simp [L,loom]) (hz T),shot_floor S B Q p,floor_pres (by simp [L,loom]) (shot_floor S T Q p),?_,?_,bill_exact S e Q P (w.valid 1 0) hq,det_tariff S e M M' Ñ p hI hT⟩
  · rw [shot_bill S B K Y Q w.lamp w.stem hq h hs]; unfold M; abel
  let C:= orbC (precisionC G c Y)
  have hy : L (holdUp (Active G T) C)=holdUp (Active G B) C := by
    classical
    unfold L; rw [← hold_loom (U:=Active G T),← hold_loom (U:=Active G B),← RingHom.comp_apply, loom_loom]; congr 2; exact (flag_cast (Woods G c) (stripe S e)).2
  rw [shot_bill S T K Y Q w.lamp w.stem hq h hs]
  simp only [map_add,map_sub]
  have he : L (bodyQ (Woods G c) (treeMatrix G S T K)) = _ := across_body (X':=Woods G c) (treeMatrix G S T K) (onKey (G:=G) e)
  rw [hy,he]; unfold M' I; abel
end

include hq h hs p w
lemma allegiance (g:(treeMatrix G S B K).PosDef) :
    Fintype.card B.Free=Fintype.card T.Free ∧
    (treeMatrix G S B K).det=(treeMatrix G S T K).det ∧
    (treeMatrix G S T K).PosDef := by
  let e:=freeEquiv B T
  have W:=assembled S B T K Y Q hq h hs p w e
  let J:=onKey (G:=G) e
  let D:=edgeM (internal S e (extractV G S B Q) (extractV G S T Q)) 0
  let T':=treeMatrix G S T K
  let X:=(treeMatrix G S T K).submatrix J J; let X':=treeMatrix G S B K
  have he (T): (treeMatrix G S T K).transpose=treeMatrix G S T K := by rw [treeMatrix,transpose_submatrix, full_symmetric _ hs]
  have hv : X.transpose=X:= by simp only [X,transpose_submatrix,he]
  have hu : IsUnit (treeMatrix G S B K).det:=(Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
  have ha : X'=D.transpose*X*D:= (W.tall (he B) hu hv).1
  have hh: |D.det|=1:= W.det
  refine ⟨Fintype.card_congr e, ?_, ?_⟩
  · change X'.det = _; rw [ha, Matrix.det_mul,Matrix.det_mul, Matrix.det_transpose]
    unfold X; rw [Matrix.det_submatrix_equiv_self]; rcases abs_eq_abs.mp (by rwa [abs_one]:|D.det|=|(1:ℝ)|) with H|H <;> simp [H]
  have hx: X.PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff ((Matrix.isUnit_iff_isUnit_det D).mpr W.slip)).mp (show PosDef (star D * X * D) from by rw [star_eq_conjTranspose,conjTranspose_eq_transpose_of_trivial,←ha]; exact g)
  have ht: T'= X.submatrix J.symm J.symm := by simp [T',X]
  change T'.PosDef; rw [ht]; exact hx.submatrix J.symm.injective
lemma bill_cross (b:IsUnit (treeMatrix G S B K).det) (A:Ink (Woods G f))(he:rollTest A A 1 0) :
   Wick (Woods G c) (treeInverse G S B K 0) (raiseE (shot S B Q Ñ P)*loom (camSlice G S B (extractV G S B Q)) A)=
   Wick (Woods G c) (treeInverse G S T K 0) (raiseE (shot S T Q Ñ P)*loom (camSlice G S T (extractV G S T Q)) A) := by
  let e:=freeEquiv B T
  let I:=onKey (G:=G) e
  let D:=edgeM (internal S e (extractV G S B Q) (extractV G S T Q)) 0
  let X:=treeMatrix G S B K; let X':=treeMatrix G S T K
  let F:= X'.submatrix I I
  let A':=loom (camSlice G S T (extractV G S T Q)) A
  let L:=loom (beam S e (G:=G))
  have W:=assembled S B T K Y Q hq h hs p w e
  have hg (T): (treeMatrix G S T K).transpose=treeMatrix G S T K := by rw [treeMatrix,transpose_submatrix,full_symmetric _ hs]
  have hv : F.transpose=F:= by simp only [F,X', transpose_submatrix,hg]
  have hy:=W.sky (hg B) b hv _ (L A') (pan_price S e _ _ A (primalSweeps ..) (primalSweeps ..) he)
  simp only [treeInverse,resolve,zero_smul,add_zero]
  rw [hy,across_read (hg T) I _]; change _=Wick _ F⁻¹ (L _)
  rw [map_mul,raise_map L (by simp [L,loom]) (shot_floor S T Q p)]
lemma inside_neutral (b:IsUnit (treeMatrix G S B K).det) : inside S B K Q Ñ P=inside S T K Q Ñ P:= by
  have he:= bill_cross S B T K Y Q hq h hs p w b 1 (fun _=>by simp)
  rw [map_one,map_one,mul_one,mul_one] at he; exact he

omit B T hq h hs p w in
private lemma shine_eq {P Q:PChart G c}{k:ℕ}(ha:shellK k P)(hb:shellK k Q)(pa:∀ i,Pure (P i))(pb:∀ i,Pure (Q i))(x:flash P=flash Q): P=Q := funext fun i=> gen_inj (finite_shell ha i) (finite_shell hb i) (pa i) (pb i) (by simpa only [Blue.flash,coeff_mk] using congrArg (coeff i) x)
lemma winter_neutral (b:IsUnit (treeMatrix G S B K).det) (v:(Y.acts c).transpose=Y.acts c) : winter S B K Y Q Ñ P=winter S T K Y Q Ñ P := by
  apply shine_eq (winter_band S B K Y Q p w.lamp) (winter_band S T K Y Q p w.lamp) (winter_pure S B K Y Q p hq w.shape v) (winter_pure S T K Y Q p hq w.shape v)
  rw [winter_read S B K Y Q w.lamp p hq hs w.shape, winter_read S T K Y Q w.lamp p hq hs w.shape, inside_neutral S B T K Y Q hq h hs p w b]
lemma reed_neutral (b:IsUnit (treeMatrix G S B K).det)(A:PChart G f) (k:ℕ)(ha:shellK k A)(x:∀ i,Pure (A i))(e:rollTest (flash A) (flash A) 1 0) :
    reed S B K Q Ñ P k A=reed S T K Q Ñ P k A := by
  have he : insideMark S B K Q Ñ P A=insideMark S T K Q Ñ P A:= bill_cross S B T K Y Q hq h hs p w b _ e
  rw [inside_reed S B K Q k w.lamp p ha hq hs w.shape x, inside_reed S T K Q k w.lamp p ha hq hs w.shape x, inside_neutral S B T K Y Q hq h hs p w b] at he
  exact shine_eq (reed_band S B K Q k w.lamp p ha) (reed_band S T K Q k w.lamp p ha) (reed_smooth S B K Q k Ñ P x) (reed_smooth S T K Q k Ñ P x) ((PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [inside_mass S T K Q p]; simp) : IsUnit (inside S T K Q Ñ P)).mul_right_inj.mp he)
end YM.WilsonCoeffUV.Power.Freedom
