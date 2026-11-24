import YM.FormalOPE.RG10.Horizon.Bump

/-!
# One far-frame testing matrix legitimately reaches full rank
On arranged **smooth** reflected pair footprints (not point probes or unreflected coordinate
estimates, which aren't being transported to the interacting continuum). Necessary for $B_T$
comparison using large-support version; proves honest free rank for all Gauges & heights.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Apertures
open Position Position.Grade Function Finset Maxwell Labels PertExtension Extraction Filter Extra.FD
open MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle
open scoped Topology BigOperators ContDiff Classical
variable {G:Gauge} (F:Frames G)(d:ℕ)
local notation "θ" => points marks
namespace Halo
lemma featured (B:Halo) {x:Points 2} (hp : x∈tsupport B.pane): dist x θ ≤ 2*B.bump.rOut := by
 rw [dist_eq_norm]; let g:=x-θ; change ‖g‖ ≤ _; have h (i:Fin 2): ‖g i‖≤B.bump.rOut:= le_of_eq (dist_eq_norm (x i) (marks i)).symm |>.trans (Set.mem_iInter.mp (B.narrow hp) i) -- params?
 have he:= PiLp.norm_sq_eq_of_L2 _ g; simp only [Fin.sum_univ_succ,Finset.univ_eq_empty, Finset.sum_empty, add_zero] at he;
 change ‖g‖^2= ‖g 0‖^2+‖g 1‖^2 at he; nlinarith only [he, pow_le_pow_left₀ (norm_nonneg (g 0)) (h 0) 2,pow_le_pow_left₀ (norm_nonneg (g 1)) (h 1) 2,B.bump.rOut_pos]
lemma priceTest (B:Halo) {X:Points 2→ℝ} (h:ContinuousOn X (conf _)) : Integrable (fun x=>B.pane x*X x):=by
 refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.mul_right B.compact)
 apply continuous_iff_continuousAt.mpr; intro x; by_cases he:x∈ conf 2
 · exact B.smooth.continuous.continuousAt.mul ((h x he).continuousAt ((conf_open 2).mem_nhds he))
 refine continuousAt_const.congr (show (fun _ : Points 2=> (0:ℝ)) =ᶠ[𝓝 x] (fun y=>B.pane y*X y) from ?_); filter_upwards [(isClosed_tsupport B.pane).isOpen_compl.mem_nhds (show x∈ (tsupport B.pane)ᶜ from fun a=> he (B.separated a))] with y hy; rw [image_eq_zero_of_notMem_tsupport hy,zero_mul]

lemma dots (D:ℕ→Halo) (hd:Tendsto (fun i=>(D i).bump.rOut) atTop (𝓝 0)){X:Points 2→ℝ} (hx : ContinuousOn X (conf _)) : Tendsto (fun i=> ∫ x, (D i).pane x*X x) atTop (𝓝 (X θ)):=by
 have hu: θ∈conf _:= unique_marks
 have ht:= (hx θ hu).continuousAt ((conf_open _).mem_nhds hu)
 apply Metric.tendsto_nhds.mpr; intro ε hε;
 obtain ⟨δ,hδ,H⟩:= Metric.continuousAt_iff.mp ht (ε/2) (by positivity);
 filter_upwards [hd.eventually (gt_mem_nhds (show 0 < δ/2 by positivity))] with i hi
 rw [Real.dist_eq]; let B:=D i; have hK:B.bump.rOut < δ/2:= hi
 have hs : Integrable B.pane:= Continuous.integrable_of_hasCompactSupport B.smooth.continuous B.compact
 change ‖(∫ x,B.pane x* X x)- X θ‖ < _
 calc
   _ = ‖∫ x, (B.pane x* X x - B.pane x* X θ)‖:= by rw [integral_sub (B.priceTest hx) (hs.mul_const _), integral_mul_const, unital, one_mul]
   _ ≤ ∫ x, ‖B.pane x* X x-B.pane x*X θ‖:= norm_integral_le_integral_norm _
   _ ≤ ∫ x, B.pane x * (ε/2):= by
     apply integral_mono ((B.priceTest hx).sub (hs.mul_const _) |>.norm) (hs.mul_const _); intro p; dsimp only [Pi.sub_apply]; rw [← mul_sub,norm_mul,Real.norm_of_nonneg (B.nonneg p)]; by_cases hh:B.pane p=0
     · rw [hh,zero_mul,zero_mul]
     exact mul_le_mul_of_nonneg_left ((H (lt_of_le_of_lt (B.featured (subset_closure hh)) (by linarith))).le : dist (X p) (X θ) ≤ _) (B.nonneg _)
   _ < _:= by rw [integral_mul_const,unital,one_mul]; linarith
end Halo

local notation "X₄" => (Deck F d)
abbrev upright : Signed := Signed.mirror timeAxis
variable (φ: Halo)

def entry (i j: X₄) (p:Points 2) : ℂ := Wick.moment G p (fun a=> writes F d (deck F d (![i,j] a)))
lemma vision_center (i j:X₄) : entry F d i j θ=readsTwo F d bottom top (deck F d i) (deck F d j):= by
 rw [scan_used,writes_eval]; unfold entry; congr 1; ext1 k; fin_cases k <;> rfl
lemma real_leaf {p:Points 2} (hp:p∈conf _) (i j:X₄): ((entry F d i j p).re:ℂ)= entry F d i j p:= by
  have ht : (entry F d i j p).im=0:= Position.ostinate ![i,j] hp; simpa only [ht,Complex.ofReal_zero,zero_mul,add_zero] using Complex.re_add_im (entry F d i j p)

def land (B:Halo): Matrix (Deck F d) (Deck F d) ℝ:= of fun i j=> Physical.free (L:=Maxwell.standard F) (deck F d) ⟨⟨2,B.shape⟩,![i,j]⟩
def pane (B:Halo): Matrix (Deck F d) (Deck F d) ℝ:= land F d B * (swing d upright)ᵀ

lemma land_read (i j:X₄) : land F d φ i j= ∫ x, φ.pane x*(entry F d i j x).re:= by
 rw [land,Matrix.of_apply, Position.vision]; rfl

def origin : Matrix (Deck F d) (Deck F d) ℝ:= (of fun i j=> (entry F d i j θ).re)* (swing d upright)ᵀ
lemma determines : (origin F d).det ≠ 0 := by
 let B:=origin F d; let A:= B.map Complex.ofRealHom; let b:= deck F d
 let r:= Signed.reflect timeAxis; let c:= b.map (rideO F r d); let K:= readsTwo F d bottom top
 have ht (i j:X₄): A i j= K (b i) (c j) := by
    change (↑(origin F d i j):ℂ)=_
    unfold origin; rw [Matrix.mul_apply]; change _ = K _ (ride F r d (b j))
    conv_rhs => rw [← b.sum_repr (ride F r d (b j))];
    push_cast; rw [map_sum]; refine sum_congr rfl fun l _=>?_
    rw [map_smul]; simp only [Matrix.of_apply,Matrix.transpose_apply, swing_deck]; rw [real_leaf F d (show θ∈conf 2 from unique_marks), vision_center]; exact mul_comm ..
 have he : A.det ≠0:=by
   apply isUnit_iff_ne_zero.mp; apply (isUnit_iff_isUnit_det _).mp; apply Matrix.vecMul_injective_iff_isUnit.mp
   intro f g h
   have hz (u : X₄→ℂ)(j : X₄): K (∑ i,u i • b i) (c j)= A.vecMul u j:= by simp [LinearMap.sum_apply, LinearMap.smul_apply, Matrix.vecMul, dotProduct,ht,map_smul, map_sum]
   let x : E4:= bottom; have hf : ∑ i,f i • b i= ∑ i,g i • b i:=
     Extra.FD.scanner_inj F d c bottom top (unique_marks.ne (show (0:Fin 2)≠ 1 by decide)) (funext fun i=>(hz f i).trans ((congr_fun h i).trans (hz g i).symm));
   exact funext fun i=> Fintype.linearIndependent_iffₛ.mp b.linearIndependent f g hf i
 rw [show origin F d =B from rfl]; intro hh; change Matrix.det (RingHom.mapMatrix _ B) ≠ 0 at he; apply he; rw [← RingHom.map_det,hh,map_zero]
-- scanner reality+reflection identity not needing Hermitian condition for this consumption
lemma illumination (B:ℕ→Halo) (hb:Tendsto (fun i=>(B i).bump.rOut) atTop (𝓝 0)) : ∀ᶠ i in atTop, (pane F d (B i)).det ≠ 0:= by
 apply Eventually.mono ((show Tendsto (fun i=>(pane F d (B i)).det) atTop (𝓝 (origin F d).det) from ?_).eventually (isOpen_compl_singleton.mem_nhds (determines F d))) fun _ h=> h
 refine continuous_id.matrix_det (n:=Deck F d) |>.continuousAt (x:=origin F d) |>.tendsto |>.comp ?_
 apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j; 
 change Tendsto (fun k=>pane F d (B k) i j) atTop (𝓝 (origin F d i j)); simp_rw [origin,pane,Matrix.mul_apply]
 refine tendsto_finsetSum _ fun k _=> ?_ ; simp_rw [land_read,of_apply]; exact (Halo.dots B hb (Complex.continuous_re.comp_continuousOn fun x hx=>(Wick.moment_smooth _ hx).continuousAt.continuousWithinAt)).mul_const _

def Valid := (pane F d φ).det ≠ 0
lemma shines : ∃ B:Halo, Valid F d B := by
  let r(n:ℕ):ℝ:= 1/(↑n+1); have h n: r n > 0:= by unfold r; positivity
  let D(n:ℕ) : Halo := ⟨⟨r n/2,r n,by specialize h n; positivity,by specialize h n; linarith⟩,(by change r n ≤_; unfold r; rw [div_le_iff₀ (by positivity)]; simp)⟩
  obtain ⟨i,hi⟩ := (illumination F d D (by exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))).exists
  exact ⟨D i,hi⟩
end YM.FormalOPE.RG10.Apertures
