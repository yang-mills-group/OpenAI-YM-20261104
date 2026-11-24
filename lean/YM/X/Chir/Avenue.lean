import YM.X.Chir.Fleet
/-!
# Limit argument large-z uniformly for directions. ratio infinity only to certify nonzero test at fixed compacts.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity Imprint
open Maxwell (Green normal)
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R e c:ℝ}
local notation "L"=>(atTop:Filter ℕ)
local notation "T"=>Tet
local notation "ε" => epsilon q
variable {x y z:ℕ→E4}{Z a b:E4}
abbrev ambition (z:ℕ→E4)(i:ℕ):= ‖z i‖
abbrev froth (z:ℕ→E4)(i:ℕ):= (ambition z i)⁻¹ • z i
def goalM (g:ℕ→ℝ)(F:ℕ→ℝ)(n:ℕ)(a:ℝ):Prop:= Tendsto (fun i=>g i^n * F i) atTop (𝓝 a)
local notation "ρ"=> ambition z
namespace goalM
variable {f n₁ m₁:ℕ→ℝ}{a b:ℝ}
lemma link (F G:ℕ→ℝ)(hf:goalM f F k a)(hg:goalM f G m b): goalM f (F*G) (k+m) (a*b):= by unfold goalM; simp_rw [Pi.mul_apply,pow_add, mul_mul_mul_comm (f _^k)]; exact Tendsto.mul hf hg
lemma succ (hf:goalM f n₁ k a)(hg:goalM f m₁ k b): goalM f (n₁+m₁) k (a+b):= by unfold goalM; simp_rw [Pi.add_apply,mul_add]; exact Tendsto.add hf hg
lemma loss (hf:goalM f n₁ k a)(hg:goalM f m₁ k b):goalM f (n₁-m₁) k (a-b):= by unfold goalM;simp_rw [Pi.sub_apply, mul_sub]; exact Tendsto.sub hf hg
lemma left (c:ℝ)(h:goalM f n₁ k a):goalM f (fun x=> c*n₁ x) k (c*a) := by unfold goalM; simp_rw [mul_left_comm _ c]; exact Tendsto.const_mul c h
lemma collects {p:V→ℕ→ℝ}{c:V→ℝ}(s:Finset V)(h:∀i∈s,goalM f (p i) k (c i)): goalM f (fun j=>∑ i∈s,p i j) k (∑ i∈s,c i):= by unfold goalM; simp_rw [mul_sum]; exact tendsto_finsetSum s h
lemma weakens (h:goalM f n₁ 6 a)(hx:Tendsto f atTop atTop): goalM f n₁ 4 0:= by
    have ht:= hx.eventually (eventually_gt_atTop 0); have he := tendsto_inv_atTop_zero.comp hx; change Tendsto _ _ _ at h; let M(i:ℕ):=(f i)⁻¹^2 * ((f i)^6*n₁ i); have hh:Tendsto M atTop (𝓝 0):= by simpa [M] using! (he.pow 2).mul h
    unfold goalM; exact hh.congr' (ht.mono fun i hi=> by unfold M; field_simp)
end goalM
variable (p u v t:Tet)
lemma aim_shift (hz:Tendsto ρ atTop atTop)(he:Tendsto x L (𝓝 a))(hx:Tendsto (froth z) L (𝓝 Z)): Tendsto (fun i=> (ρ i)⁻¹ • (z i-x i)) L (𝓝 Z):= by
    have hg:Tendsto (fun i=>(ρ i)⁻¹ • x i) L (𝓝 0):= by simpa using! (tendsto_inv_atTop_zero.comp hz).smul he
    simp_rw [smul_sub]; simpa using! hx.sub hg
lemma aim_s (hz:Tendsto ρ atTop atTop)(ht:Tendsto x L (𝓝 a))(hx:Tendsto (froth z) L (𝓝 Z))(he: Z ≠ 0): goalM ρ (fun i=>solar (z i-x i) p t) 4 (solar Z p t):= by
     let F(i:ℕ):= solar ((ρ i)⁻¹ • (z i-x i)) p t; have hh:Tendsto F L (𝓝 (solar Z p t)):= (shine p t he).tendsto.comp (aim_shift hz ht hx); unfold goalM; exact hh.congr' ((hz.eventually (eventually_gt_atTop 0)).mono fun i hi=>by unfold F; rw [tint_s p t _ (inv_pos_of_pos hi),inv_inv])
lemma aim_C (i:Axis)(hz:Tendsto ρ atTop atTop)(ht:Tendsto x L (𝓝 a))(hx:Tendsto (froth z) L (𝓝 Z))(he: Z ≠ 0): goalM ρ (fun k=> Cup p i (x k-z k)) 3 (Cup p i (-Z)) := by
     let F(k:ℕ):= Cup p i (-((ρ k)⁻¹ • (z k-x k))); have h:Tendsto F atTop (𝓝 (Cup p i (-Z))):=(cshine p i (neg_ne_zero.mpr he)).tendsto.comp (aim_shift hz ht hx).neg; unfold goalM; apply h.congr'; filter_upwards [hz.eventually (eventually_gt_atTop 0)] with k hk; unfold F; rw [← smul_neg,neg_sub,tilt_C p i _ (inv_pos_of_pos hk),inv_inv]
variable (hq:1<q.val){J:ℕ→Ter} (H:∀ i:ℕ,Crowd q (x i) (y i) (z i) (J i))
local notation "K"=> goalM ρ
variable (hz:Tendsto (ambition z) atTop atTop)(ht:Tendsto (froth z) L (𝓝 Z))(hS:‖Z‖=1) (hx:Tendsto x L (𝓝 a))(hy:Tendsto y L (𝓝 b))
lemma duel (h:∀ i,7≤‖x i-y i‖)(hx:Tendsto x L (𝓝 a))(hy:Tendsto y L (𝓝 b)):a≠b:= by
    apply sub_ne_zero.mp; apply norm_pos_iff.mp; refine lt_of_lt_of_le (by norm_num : (0:ℝ)<7) ?_; exact ge_of_tendsto' (hx.sub hy |>.norm) h
lemma map_divine (h:‖Z‖=1) : Z≠0:= norm_pos_iff.mp (by rw [h]; norm_num)
include hz ht hS hx hy
lemma scaleL_seed : K (fun k=>seedL (x k) (y k) (z k) p u v) 4 0 := by
    let f(i j:Axis):= ps p i j * Cup u i (-Z) * Cup v j (-Z); refine goalM.weakens (a:=∑ i:Axis,∑ j:Axis,f i j) ?_ hz; unfold seedL; refine goalM.collects _ (fun _ _=> ?_); rename_i i ih; apply goalM.collects; intro j _; exact goalM.link _ _ (goalM.left (form 1 p i j) (aim_C u i hz hx ht (map_divine hS))) (aim_C v j hz hy ht (map_divine hS)) -- function product Pi ext
include H hq
lemma scaleJ_star : goalM ρ (fun k=> J k p u v t) 4 (solar Z t p*(η u p v*Green (a-b))):= by
    obtain ⟨c,hc,U⟩:= rich p u v t hq; let f(i:ℕ):= η u p v* Green (x i-y i); let w:=η u p v* Green (a-b); have hf : Tendsto f L (𝓝 w):= ((Maxwell.freeSmooth (sub_ne_zero.mpr (duel (fun i=> (H i).openWide.wide_xy.1) hx hy))).continuousAt.tendsto.comp (hx.sub hy) |>.const_mul (η u p v));
    let g(i:ℕ):=solar (z i-x i) t p; let l(i:ℕ):= (ρ i)^4*(J i p u v t-g i*f i); let c'(i:ℕ):=(ρ i)⁻¹*c; have h : Tendsto l L (𝓝 0):= by
        refine squeeze_zero_norm (a:=c') ?_ (by simpa using! (tendsto_inv_atTop_zero.comp hz).mul_const c); intro i; unfold l; specialize U (H i); have hp:ρ i>0:= (H i).openWide.z0; rw [norm_mul,Real.norm_of_nonneg (by positivity:(ρ i)^4≥0)]; refine (mul_le_mul_of_nonneg_left U (by positivity:(ρ i)^4≥0)).trans_eq ?_; change (ρ i)^4*(c*(ρ i)⁻¹^5)=_; unfold c'; field_simp
    have he:= aim_s t p hz hx ht (map_divine hS); unfold goalM at *; have hh:= h.add (he.mul hf); rw [zero_add] at hh; exact hh.congr fun i=>by change l i+((ρ i)^4*g i)*f i=_; unfold l; ring
set_option maxHeartbeats 650000 in
lemma spin_far : goalM ρ (fun i=> SpinLimit (J i) (x i) (y i) (z i)) 12 ((-6)*(8*normal)^3* Green (a-b)):= by
    let f(k:ℕ):=solar (z k-x k); let g(k:ℕ):=solar (z k-y k); let U:=solar Z; let a':= Green (a-b); rw [← coat_sun Z hS]; unfold SpinLimit; refine goalM.collects _ fun i _=> goalM.collects _ fun u _=> goalM.collects _ fun v _=> ?_; let w(k:ℕ):=Α (f k) (g k) i u v; have A:goalM ρ w 8 (Α U U i u v):= goalM.loss (goalM.link _ _ (aim_s (loop i) u hz hx ht (map_divine hS)) (aim_s (ℓ i) v hz hy ht (map_divine hS))) (goalM.link _ _ (aim_s (ℓ i) u hz hx ht (map_divine hS)) (aim_s (loop i) v hz hy ht (map_divine hS)))
    exact goalM.link _ _ A (goalM.loss (scaleL_seed i u v hz ht hS hx hy) (goalM.collects _ (fun t _=> scaleJ_star t u v i hq H hz ht hS hx hy))) -- types?
end YM.PositionX.Chir
