import YM.OPE.Therm.Touched
/-!
# DLG result on all meshes p,N

Prefix-ready (Poetry adds only a low-raking delay, user must pair witness or carry).
Not yet claiming X-space matching; this file supplies a probability kernel for pricing.
Quantifier on mean-zero scopes across any mesoscopic probes, bounded temperature
within the clean margin. Receives after-L choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Therm
open Function Set Filter RG Lattice Wilson MeasureTheory Cells Push.GridApprox Next Next.Rank Alarm House Cradle Portolan
open scoped BigOperators Classical Topology ENNReal Matrix.Norms.Frobenius
variable {G:Gauge} {H:History G}{L:Levels G}{i N p:ℕ}
variable (Y:Poetry H.levels)(Z:H.Selected)(θ:G.Simple)
local notation "U" => H.levels
local notation "X" => H.levels.clock.hatBeta
local notation "r₀"=> burning U
local notation "D"=> scene H
local notation "S"=> H.S
local notation "nn" => H.S.side
local notation "T"=> cool U
local notation "R"=> H.rep
local notation "P"=> (Fintype.card PlaqAxes:ℝ)
local notation "d"=> Module.finrank ℝ G.Mat
variable (m:ℕ)(h0:10≤ m)
include θ Y h0
lemma tilts : ∀ᶠ i:ℕ in atTop,∀ p:ℕ,∃ t:Tiling (nn i p), t.kind=.site ∧
   (X i ^m)^14 ≤ t.side.val ∧ (t.side.val:ℝ) ≤ (X i^m)^16:=by
   filter_upwards [(ember_mul («K»:=U) θ (m*14)).eventually (gt_mem_nhds zero_lt_one)] with i hi p
   let F:=(X i^m)^14; have ht := (U).fits.delayed i; have hp := one_lt_pow₀ (n:=m) ht (by omega); have he : 1<F:= one_lt_pow₀ hp (by norm_num)
   obtain ⟨j,hj,h1,h2⟩:= shelter («K»:=U) i F he (by simpa only [F,pow_mul,Set.mem_Iio] using hi)
   let t:Tiling (nn i p):= {tilesAt S p hj.le with kind:=.site}; refine ⟨t,rfl,?_,?_⟩
   all_goals
     have hT: (S).a i * (t.side.val:ℝ) = (S).a j:= H.S.embeds_scale (H.S.toDepth hj.le p)
     apply le_of_mul_le_mul_left _ ((S).a_pos i); rw [hT]
   · rw [mul_comm]; exact h2.le
   let a:ℝ:= (H.S.block j).val; let x:=(S).a
   have ha:0<a:=by unfold a; positivity
   have hC:a≤ X i:= ((Y.stage j).track.trans (Real.log_le_log (zero_lt_one.trans ((U).fits.delayed _)) (WilsonStartup.Timing.hat_mono U (Gauge.slopeConstant_pos θ).le hj.le))).trans (Real.log_le_self (zero_lt_one.trans ht).le)
   calc
      H.S.a j = a*((S).a (j+1)):= by rw [(S).a_step,mul_div_cancel₀ _ ha.ne']
      _ ≤ (X i^m)^2*(F*x i):= mul_le_mul (hC.trans (by rw [←pow_mul]; simpa only [pow_one] using pow_le_pow_right₀ ht.le (show 1≤ m*2 by omega))) h1 ((S).a_pos _).le (by positivity)
      _= _:= by unfold F x; ring
omit Y h0 m in
private lemma funds : ∀ᶠ i:ℕ in atTop,(0<T i/4 ∧ T i/4≤1) ∧ touchW (G:=G) (T i/4) 1 ≤ (X i)^4:=by
    let ht:= Station.hat_rate U θ
    filter_upwards [(log_raised («K»:=U) θ).eventually_ge_atTop 1,narrow (H:=H) θ,ht.eventually_ge_atTop 16,ht.eventually_ge_atTop d] with i hi ⟨hz,hv⟩ h16 hB
    have hx:= (U).fits.delayed i; have hX:=zero_lt_one.trans hx
    have hsc:1/X i ≤ T i := by
       apply (fuelOdds (H:=H) i).2.2.trans; unfold cool; apply le_mul_of_one_le_right (fuelOdds (H:=H) i).1.le; exact one_le_pow₀ hi
    have hy : 4/(T i/4) ≤ 16*X i:= by
       rw [div_le_iff₀ (by positivity)]; have he:= (div_le_iff₀ hX).mp hsc; linarith only [he]
    have h:=Real.log_le_self (by positivity: 0≤4/(T i/4)); refine ⟨⟨by positivity, by linarith only [hz,hv, (U).fits.smallField i]⟩,?_⟩
    unfold touchW; rw [Nat.cast_one,one_mul]; apply (mul_le_mul_of_nonneg_left (h.trans hy) (Nat.cast_nonneg _)).trans ((mul_le_mul_of_nonneg_right hB (by positivity:0≤16*X i)).trans _); linarith only [mul_le_mul_of_nonneg_right h16 (pow_nonneg hX.le 2), pow_le_pow_right₀ hx.le (by decide:3≤4)]

def Homes (H:History G) (m:ℕ) (i:ℕ) := ∀ N p,i≤N → ∀ q:ℕ,q≤(H.levels.clock.hatBeta i)^m → ∀ τ:ℝ, cool H.levels i≤τ → 2* τ ≤ (H.rep N p i).p.threshold →
    ∀ (z:Site (H.S.side i p)) (f:Config G (H.S.side i p)→ℝ)(Y:Finset (Edge (Site (H.S.side i p)))), Attempt (H.rep N p i) (burning H.levels i) τ q z f Y → ‖∫ V, f V∂ scene H N p i‖ ≤ (H.levels.clock.hatBeta i ^m)⁻¹
include Z
lemma homes : ∀ᶠ i:ℕ in atTop,Homes H m i:=by
   let ht:= Station.hat_rate U θ
   filter_upwards [rare Y θ Z, tilts Y θ m h0,funds (H:=H) θ, ht.eventually_ge_atTop P,ht.eventually_ge_atTop 10000,tended Y θ Z,(disappears (H:=H) θ (m*15+6)).eventually (gt_mem_nhds zero_lt_one),(disappears (H:=H) θ (m*200)).eventually (gt_mem_nhds zero_lt_one)] with i hy htilt ⟨⟨hp0,hp1⟩,hp⟩ hF h10 hY hV hv
   intro N p hk q hq τ hτ htc z f Y hf; let S':= H.rep N p i; obtain ⟨t,hh,ha,hb⟩:= htilt p; obtain ⟨hX,hK⟩:= hY N p hk; let L:=(X i)^m; let x:=X i; have hx:1<x:= (U).fits.delayed i; have hL:x ≤ L:= by simpa only [pow_one] using pow_le_pow_right₀ hx.le (show 1≤ m by omega)
   have hY : 0<x:= zero_lt_one.trans hx
   have he : safeCost G (nn i p) t.side (Stove.haloFee S' (r₀ i)) q (x^6) (vanishP U i*x^6) (T i/4) L:= by
      refine ⟨hF.trans hL,hp.trans (pow_le_pow_right₀ hx.le (by omega)),h10.trans hL,hK.trans ?_,hq,hp1,hp0,pow_nonneg hY.le _,pow_le_pow_right₀ hx.le (by omega),?_,ha,hb⟩
      · have hh:=pow_le_pow_left₀ (Real.log_nonneg hx.le) (Real.log_le_self hY.le) 6; have ht:=mul_le_mul_of_nonneg_right h10 (pow_nonneg hY.le 6); have hp : x^7 ≤ L:=pow_le_pow_right₀ hx.le (by omega); linarith only [hh,ht,hp,pow_nonneg hY.le 6]
      unfold L; rw [← pow_mul]; change x^ _ * _ < _ at hV; rw [pow_add] at hV; unfold x at *; linarith only [hV]
   have hm(x : Face (Per (nn i p))): (D N p i).real (trigger x τ) ≤ (L⁻¹)^200 := by
      letI := probability (p:=p) Z hk; have he :=hy N hk p x; apply (measureReal_mono (μ:=D N p i) (show trigger x τ ⊆ trigger x (T i) from fun V h=>lt_of_le_of_lt hτ h)).trans (he.trans ?_)
      change (X i ^ _)*vanishP U i< 1 at hv; rw [inv_pow]; unfold L; rw [← pow_mul]; rw [← one_div]; apply (le_div_iff₀ (pow_pos (zero_lt_one.trans ((U).fits.delayed i)) _)).mpr; rw [mul_comm]; exact hv.le
   exact Portolan.patches Z t hh hk hX he (by linarith only [htc,hτ]) (by linarith only [hτ]) hm hf
end YM.OPE.Therm
