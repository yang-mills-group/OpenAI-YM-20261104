import YM.WilsonCoeffUV.Product.Report.Fcut
import Mathlib.Analysis.Complex.ExponentialBounds
/-!
# Capture to one marked stencil
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Mer
open Filter Function Matrix Lattice RG Laurent Bloch Metric Blue FreeResolvent Work.F08 Bank Soil
open Gauge Power PathCost Precision Embroider Fountain Cosmos Shard Realm
open PowerSeries
open scoped Topology BigOperators
variable {n c:Side}{U V α β:Type*}{r h D j e i l k:ℕ}{A B C s:ℝ}{G:Gauge}
open Embroider
open scoped ContDiff
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos PathCost PowerSeries
open scoped Matrix.Norms.Frobenius
variable {b b' v u m M N a:ℕ}{H:Hol G} {x δ Z y:ℝ} {E W V' W':Credit}{R:Realm G (e+1) E}
variable {Q:Fin (a+1)→ SealR G}
-- measured report whole-cell normalized transmission on cover
abbrev LodeStar (A:Levels G)(Ñ:ChartRatio G)(F:Wilt Q)(X:Herit Q)(m b N:ℕ)(y:ℝ): Era G Lounge:= cruises A Ñ N (capP Q) N b (HearthC Q A Ñ F X m N N y)
lemma capsizing (P: HorizonP H R W V' Q)(F:Wilt Q)(X:Herit Q)(o:CellR)(u:R.anchor≤m)(v:b≤m)(q:m≤ N):
   locale o (LodeStar R.draws R.paid F X m b N y)=cruises R.draws R.paid N (capP Q) m b (loadK R.draws R.paid F X m N N y o):=by
    unfold locale LodeStar; rw [cruiseT (century o) _ (v.trans q) R.hG R.green le_rfl (Hearth_enter P F X (u.trans q) le_rfl),cruisesMore _ _ _ v q,loadK,ash_spans];
lemma oldGuard (p:R.anchor≤b)(v:b≤ m):Escort R b m (fun _=>1):=⟨p,v,fun _ _ _=>zero_le_one,fun _ _ _=>le_rfl,fun i _ _=> by unfold thinLevel; rw [one_div]; exact inv_le_one_of_one_le₀ (Nat.one_le_cast.mpr (R.draws.S.block i).pos)⟩
lemma Captures (H:Hol G)(Q: Fin (a+1)→ SealR G)(E W V W' L:Credit)(e u:ℕ): ∃ C:Credit,∀ (R:Realm G (e+1) E), HorizonP H R W V Q→ SpringD R (capP Q) u (capP Q+2) W' → Dormitory R (capP Q) u L → ∀ m c b N M (F:Wilt Q)(X Y: Herit Q)(A B:Fin (a+1)→ℝ)(Z y δ)(o:CellR), R.anchor ≤ b → b≤ m → m≤ c → c≤ N → c≤ M → PadRank R b m Z → Bough Q F y Z B → R.tempC m c≤ δ → Sitting Q A e δ X Y →
   let T:= ∏ i,B i*A i; Fringed (capP Q) e u 1 (C.buy Z*T) δ (locale o (LodeStar R.draws R.paid F X m b N y)) (locale o (LodeStar R.draws R.paid F Y m b M y)):=by
    obtain ⟨C,h⟩:= topDay H Q E W V W' L e u; obtain ⟨A,g⟩:=waveSeen G (capP Q) e u E L
    refine ⟨A.prodC C,fun R H' v t m c b N M F X Y B W' Z y δ o hv hm hb hn hM hz hy hδ l=>?_⟩; intro B'
    have he:= h R H' v t m (max N M) c N M F X Y B W' Z y δ o (hv.trans hm) ((hb.trans hn).trans (le_max_left ..)) hb hn hM (hz.year _ hm le_rfl) hy hδ l; rw [min_eq_right (le_max_left ..),min_eq_right (le_max_right ..)] at he
    rw [capsizing H' F X o (hv.trans hm) hm (hb.trans hn),capsizing H' F Y o (hv.trans hm) hm (hb.trans hM),Credit.products,mul_assoc]; exact g R t b m _ c N M _ _ _ (oldGuard hv hm) hz hb hn hM hδ _ _ he

-- full normalized root capture. accepts any probability before fix of policy. unmasked
open MeasureTheory
open scoped ENNReal
noncomputable def dayMeasure: Measure CellR:= Measure.comap (fun x:CellR=>x.val) volume
instance : IsProbabilityMeasure dayMeasure:=by
   refine ⟨?_⟩; rw [dayMeasure, Measure.comap_apply _ Subtype.val_injective (fun _=> MeasurableSet.subtype_image Metric.isClosed_closedBall.measurableSet) _ MeasurableSet.univ,Subtype.coe_image_univ]; rw [Real.volume_pi_closedBall _ (by norm_num)]; norm_num

section
variable (μ: Measure CellR)[IsProbabilityMeasure μ]
def FaceM (D:ℕ) (x:Volume D): Lounge:= x.val ⟨(0:Fin (D+1)),(fun _=>0)⟩
omit [IsProbabilityMeasure μ] in
lemma face_at (φ:Phrase D)(x: CellR) : FaceM D (page D φ) x=φ.val x.val:=by unfold FaceM; rw [submission,Embroider.draft]; exact iteratedFDeriv_zero_apply ..
omit [IsProbabilityMeasure μ] in
lemma face_norm (X:Volume D): ‖FaceM _ X‖≤‖X‖:= norm_le_pi_norm X.val _
lemma readyCash (x:Lounge): Integrable x μ:= Continuous.integrable_of_hasCompactSupport x.continuous (HasCompactSupport.of_compactSpace _)
lemma drape_norm (x:Lounge) : (∫ p,‖x p‖ ∂μ)≤‖x‖:= by
   apply (integral_mono (readyCash μ x |>.norm) (integrable_const ‖x‖) (show (fun i=>‖x i‖)≤ fun _=>‖x‖ from fun y=> ContinuousMap.norm_coe_le_norm _ _)).trans
   simp
lemma swoop (x:Lounge)(v: Volume D): ‖∫ p, (x*FaceM _ v) p ∂μ‖≤ (∫ p, ‖x p‖ ∂μ)*‖v‖:=by
    apply (norm_integral_le_integral_norm _).trans
    rw [← integral_mul_const]; apply integral_mono (readyCash μ _ |>.norm) ((readyCash μ x).norm.mul_const _) (fun i=>?_); rw [ContinuousMap.mul_apply,norm_mul]; exact mul_le_mul_of_nonneg_left ((ContinuousMap.norm_coe_le_norm _ _).trans (face_norm v)) (norm_nonneg _)
def skyLinear (D:ℕ)(x:Lounge): Volume D→ₗ[ℝ]ℝ where
   toFun y:= ∫ p,(x*FaceM _ y) p ∂μ
   map_add' a b:=by rw [show x*FaceM D (a+b)=_ from Eq.trans (congr_arg (x*·) (show FaceM D (a+b)=FaceM D a+FaceM D b from rfl)) (mul_add ..), ← integral_add (readyCash μ (x*FaceM _ a)) (readyCash μ (x*FaceM _ b))]; rfl
   map_smul' c b:=by rw [show x*FaceM D (c•b)=c • (x*FaceM _ b) from Eq.trans (congr_arg (x*·) (show FaceM D (c•b)=c • FaceM D b from rfl)) (mul_smul_comm ..)]; exact integral_smul c (fun p=> (x*FaceM _ b) p)
def skyPoint (D:ℕ)(x:Lounge): Vote D:= (skyLinear μ D x).mkContinuous (∫ p,‖x p‖ ∂μ) (swoop μ x)
lemma sky_price (x:Lounge)(D): ‖skyPoint μ D x‖≤ ∫ p,‖x p‖ ∂μ := by apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun p=> norm_nonneg (x p)); exact swoop μ x
def HourFace (D:ℕ) : Lounge→L[ℝ] Vote D:=
    let L:Lounge→ₗ[ℝ] Vote D:={
       toFun:=skyPoint μ D
       map_add' x y:=by ext1 i; change (∫ p, ((x+y)*FaceM _ i) p ∂μ)= (∫ p, (x*FaceM _ i) p ∂μ)+∫ p,(y* FaceM _ i) p ∂μ; rw [add_mul]; exact integral_add (readyCash μ (x*FaceM _ i)) (readyCash μ (y*FaceM _ i))
       map_smul' x y:=by ext1 i; change (∫ p, ((x•y)*FaceM _ i) p ∂μ)=x • (∫ p,(y*FaceM _ i) p ∂μ); rw [smul_mul_assoc]; exact integral_smul x (fun p=> (y*FaceM _ i) p) }
    L.mkContinuous 1 (fun i=> by rw [one_mul]; exact (sky_price μ i _).trans (drape_norm ..))
lemma hour_price (x:Lounge)(D): ‖HourFace μ D x‖ ≤ ∫ p,‖x p‖ ∂μ:=sky_price μ x _
lemma hour_at (x:Lounge)(φ:Phrase D): HourFace μ D x (page D φ) = ∫ p,x p*φ.val p.val ∂μ := by simp_rw [←face_at]; rfl
-- sum budget over root costs pointwise.
lemma MintD (D:ℕ)(T: ChamberTen G Lounge r)(v:∀ p:CellR,Fruit 0 1 u (fun x=> T x p) A): Fruit 0 1 u (fun i=>HourFace μ D (T i)) A:=by
    let V p i:= hedge 0 1 u i * ‖T i p‖; let L i:= hedge 0 1 u i* ‖HourFace μ D (T i)‖; have hL i:0≤L i:=mul_nonneg (hedge_nn zero_le_one _) (norm_nonneg _)
    have hp (S:Finset _): (∑ i∈ S,L i) ≤ A:= by
        have hv i:L i ≤ ∫ p,V p i ∂μ:=by unfold V; rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left (hour_price μ _ _) (hedge_nn zero_le_one _)
        have he i: Integrable (fun p=>V p i) μ := ((readyCash μ (T i)).norm.const_mul _)
        refine (Finset.sum_le_sum (fun x _=>hv x)).trans ?_; rw [← integral_finsetSum S (fun i _=>he i)]; apply (integral_mono (integrable_finsetSum S (fun i _=>he i)) (integrable_const A) (fun i=>(Summable.sum_le_tsum S (fun j _=>(v i).1 j) (v i).2.1).trans (v i).2.2)).trans; simp
    have he:= summable_of_sum_le hL hp; exact ⟨hL,he,he.tsum_le_of_sum_le hp⟩
end
end YM.WilsonCoeffUV.Mer
