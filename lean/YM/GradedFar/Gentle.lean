import YM.GradedFar.PhysicalBook
import YM.GradedFar.Preinverse
/-!
# (M.3) and other comparisons, on fixed *arbitrarily* priced field labels

Use on the actual unnormalized A example labels etc. Especially for licenses including unit labels:
it doesn't matter if `width (Normalize.leaf ..)` is <= 1 in the Gram pose. Can take **any** fixed
common bound. Also allows using prices over arbitrary fixed equivalently normed label spaces.
Thus no ambiguity over credential purchases meaning those actual same concrete labels.

These are exercises of the earlier results over continuum here, not changing cutoff prices etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar
namespace Gentle
open Function Filter Set PowerSeries
open Extraction Table Spec PhysMS Trace.Pilot
open OPE (Viewers)
open OPE.Orbits (Reader)
open FVA2 XSpace XSpace.Normalize Register Scale Dframe O O.Score O.Enh FVA2.GradedFar
open MS MS.Land MS.Fleet
open scoped Topology BigOperators Classical
variable {G:Gauge} {C:Family G}{f:Extraction.Order}{S:Table C.book}
    (F:Final C f S)(P:ℝ→tower S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {n m h p' p l:ℕ}{d:Fin n→ℕ}{e:Fin m→ℕ}
    (A:Arenas G)(W:ℝ→Frames G)(η r T z:ℝ)(hd:AppointedH140Through l d)(he:AppointedH140Through l e)(hh:h≤l)
    (o:E4)(ω : Viewers F) (x:Points n)(y:Points m) (u:AppointedH140Inputs G d)(v:AppointedH140Inputs G e)

lemma allot (u:AppointedH140Inputs G d) {R:ℝ}(hR:1 ≤ R)(h:Box u R) : ∃ v:AppointedH140Inputs G d, Box v 1 ∧ u=(fun i=> (R:ℂ) • v i):= by
 let c:ℂ:=R; let v (i:Fin n) := c⁻¹ • u i
 have hg:0<R:=zero_lt_one.trans_le hR; have he : ‖c‖=R:=by rw [show c=(R:ℂ) from rfl,Complex.norm_real,Real.norm_of_nonneg hg.le]
 refine ⟨v,(boxes zero_le_one).2 (fun i=>?_ ), funext (fun i=> (smul_inv_smul₀ (norm_pos_iff.mp (he.symm ▸ hg)) (u i)).symm)⟩
 rw [show v i=c⁻¹ • u i from rfl,width_smul,norm_inv,he]; exact (mul_le_mul_of_nonneg_left ((boxes hg.le).1 h i) (inv_nonneg.mpr hg.le)).trans_eq (inv_mul_cancel₀ hg.ne')
-- written schematically by homogeneous actions (frame-independent)
variable (c s:ℂ)
local notation "u∗" => fun i=> c • u i
local notation "v∗" => fun i=> s • v i
lemma packet_scale : GradedFar.packet F P Q h o r x u∗=c^n • GradedFar.packet F P Q h o r x u:= by
 simp_rw [packet, ← Fork.packetCost_apply]; have he: labels P r u∗ = fun i=> c • labels P r u i:= by unfold labels; simp_rw [map_smul]
 rw [he,(Fork.packetCost ..).map_smul_univ, map_smul]; simp
lemma component_scale (a:O.Score.Q G) : ope A u∗ x a = PowerSeries.C (c^n)*ope A u x a:= by
 unfold ope multipliers; rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun b _=>?_)
 simp only [map_smul,smul_eq_mul,Finset.prod_mul_distrib, map_mul, mul_assoc,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
lemma vector_scale : croppedVector A h p u∗ x z=c^n • croppedVector A h p u x z:= by
 have hx(B:PowerSeries ℂ): appointedH140Crop p z (PowerSeries.C (c^n)*B)=c^n*appointedH140Crop p z B:= by
    rw [crop_eq,crop_eq, Finset.mul_sum]; refine Finset.sum_congr rfl (fun i _=> ?_); rw [coeff_C_mul]; ring
 simp_rw [croppedVector, Finset.smul_sum, component_scale, smul_smul,hx]
lemma joint_scale (f: Both G d e) : f u∗ v∗=(c^n*s^m) • f u v:= by
 -- reduce mixed scaling in curried order
 rw [f.map_smul_univ,_root_.smul_apply,(f u).map_smul_univ, smul_smul]
 simp
lemma prediction_scale : appointedH140Crop p z (fullSeries A W η hd he x y u∗ v∗)= (c^n*s^m) • appointedH140Crop p z (fullSeries A W η hd he x y u v):= by
 rw [crop_eq,crop_eq,Finset.smul_sum]; refine Finset.sum_congr rfl (fun k _=>?_); rw [fullSeries, fullSeries, coeff_mk, coeff_mk, joint_scale]; simp only [smul_eq_mul]; ring
lemma D_scale : atCenter F P h ω o r T y v∗=s^m • atCenter F P h ω o r T y v:= by
 ext1 a; simp_rw [LinearMap.smul_apply, center_length,atLength]; have h:= joint_scale (d:=Output h) (fun _=>a) v 1 s (today F P ω o r (r*T) (r*T) 0 y); simpa only [one_smul,one_pow,one_mul] using h
lemma predictionCenter_scale : croppedResponse A W η hh he y v∗ p z=s^m • croppedResponse A W η hh he y v p z:= by
 ext1 a; simp_rw [LinearMap.smul_apply,croppedResponse_apply]; let b:AppointedH140Inputs G (Output h):= fun _=>a
 have he:= prediction_scale A W η z (p:=p) (d:=Output h) (fun _=>hh) he 0 y b v 1 s; simpa only [one_smul,one_pow,one_mul] using he
-- factors tracked explicitly for row bill
lemma scalar_bill {d':ℕ} (f:Sec G d'→ₗ[ℂ] ℂ) (c:ℂ) : rowPrice (c • f)=‖c‖ * rowPrice f:= by
 rw [rowPrice,show row (c • f)=c • row f from rfl, norm_smul]; rfl
-- purchase BeforeInverse for arbitrary fixed bounding boxes. See Dawn `respondsBox`.
variable (N: WilsonPrescription G) (Z:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
variable (ν:ℝ)
local notation "g"=>strength G
local notation "δ*" => GroupS.gaugeN N.scheme N.criterion Z ν
local notation "Ξx"=> Scale.Measure.outlook N.scheme N.criterion

def BeforeBox (t:ℝ→ℝ) (hd:AppointedH140Through l d)(he:AppointedH140Through l e)(hh:h≤l)(K:Set (Points n))(L:Set (Points m))(a b β B:ℝ)(p' p:ℕ)(R E:ℝ) : Prop:=
    ∃ C:ℝ,0<C ∧ ∀ᶠ r in trail,∀ T,Budget.receding (g r) B a b T → ∀ x∈ K,∀ y∈ L,
      forest x (T • y) ∈ conf (n+m) ∧ outgoing (T • y) ∈ conf (1+m) ∧
        ∀ o (ω:Viewers F) (u : AppointedH140Inputs G d)(v:AppointedH140Inputs G e), Box u R → Box v E →
        let c:=croppedVector Ξx h p u x (t r)
        let Y := atLength F P ω o r T x y u v
        let dY := Y - appointedH140Crop p (t r) (fullSeries Ξx δ* (-Real.log T) hd he x y u v)
        let D₀ := atCenter F P h ω o r T y v
        let dM := D₀ - croppedResponse Ξx δ* (-Real.log T) hh he y v p (t r)
        ‖dY‖ + rowPrice dM + ‖dY-dM c‖ + ‖Y-D₀ (packet F P Q h o r x u)‖ + ‖Y-D₀ c‖ ≤
          C*(g r)^p'*T^(-(h:ℝ)-β)
-- helper for alignment, common scales real above one
set_option maxHeartbeats 400000 in
private lemma realigned {Y y:ℂ}{v w:Sec G h}{A B : Sec G h→ₗ[ℂ] ℂ}{D:ℝ}
    (R E:ℂ) (hR:1≤‖R‖)(He:‖Y-y‖ + rowPrice (A-B)+‖Y-y-(A-B) v‖ + ‖Y-A w‖ + ‖Y-A v‖ ≤ D):
    let z:= R*E
    ‖z • Y - z • y‖ + rowPrice (E • A-E • B)+‖z • Y - z • y -(E • A-E • B) (R • v)‖ + ‖z • Y-(E • A) (R • w)‖+‖z • Y-(E • A) (R • v)‖ ≤ ‖R‖*‖E‖*D:= by
 dsimp only
 have hrr: ‖E‖ ≤ ‖R‖*‖E‖:=by exact (one_mul _).symm.le.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))
 have h':=mul_le_mul_of_nonneg_right hrr (show 0 ≤ rowPrice (A-B) from (row (A-B)).opNorm_nonneg)
 have hv (x:Sec G h)(B:Sec G h →ₗ[ℂ] ℂ): (E • B) (R • x)= (R*E) • B x := by rw [map_smul,LinearMap.smul_apply,smul_smul]
 rw [← smul_sub E A B,scalar_bill,hv v (A-B),hv w A,hv v A,←smul_sub (R*E) Y y,←smul_sub (R*E) (Y-y) _,← smul_sub (R*E) Y (A w),← smul_sub (R*E) Y (A v)]
 simp_rw [norm_smul,norm_mul]
 refine le_trans ?_ (mul_le_mul_of_nonneg_left He (by positivity)); simp only [mul_add]
 exact add_le_add (add_le_add (add_le_add (add_le_add le_rfl h') le_rfl) le_rfl) le_rfl

theorem extend {t:ℝ→ℝ}{K:Set (Points n)}{L:Set (Points m)}{a b β B:ℝ}(H:BeforeInverse F P Q N Z ν t hd he hh K L a b β B p' p) {R E:ℝ}(hR:1≤ R)(hE:1≤ E) : BeforeBox F P Q N Z ν t hd he hh K L a b β B p' p R E:= by
 let z:ℂ:=R; let w:ℂ:=E; have hr:0<R:=zero_lt_one.trans_le hR; have hw:0<E:=zero_lt_one.trans_le hE
 have hh' : 1 ≤ ‖z‖:= by unfold z; rwa [Complex.norm_real,Real.norm_of_nonneg hr.le]
 have hw':0<‖w‖:=by unfold w; rwa [Complex.norm_real,Real.norm_of_nonneg hw.le]
 obtain ⟨C,hC,H'⟩:= H; refine ⟨‖z^n‖*‖w^m‖*C,by rw [norm_pow,norm_pow]; positivity,?_⟩; filter_upwards [H'] with r hA T hT x hX y hY; obtain ⟨ hx,hy,hB⟩:= hA _ hT x hX y hY
 refine ⟨hx,hy,?_⟩; intro o ω u v hu hv; obtain ⟨u0,hU,rfl⟩:= allot _ hR hu; obtain ⟨v0,hV,rfl⟩:= allot _ hE hv
 dsimp only
 specialize hB o ω u0 v0 hU hV
 simp_rw [packet_scale, vector_scale, prediction_scale, D_scale,predictionCenter_scale, atLength, joint_scale]
 exact (realigned (z^n) (w^m) (by rw [norm_pow]; exact one_le_pow₀ hh') hB).trans_eq (by ring)
end Gentle
end YM.Integration.GradedFar
