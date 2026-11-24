import YM.X.Chir.Drama
/-!
# all-air remote estimator. applied to PP– transfer derivatives with normalized shock. Does not assume scale uniformity of Leg/P^+.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Chir.Imprint
open Lattice Wilson Next.Rank LiftMark PertExtension LatticePT Crate Porch Rays Clove Interval Size Braid Shelf Tot
open Finset Filter Set Function Reed Ocean Stems Hinge Haze Fielding Print Tri Plate Gravity Imprint
open scoped Topology BigOperators Classical
variable {G:Gauge} {m k:ℕ} {V:Type*} {n:Side} {q:ℕ+}{r R t c:ℝ}
local notation "S"=>Site n
local notation "D"=>Interval.mass
local notation "p"=>fund
abbrev remote (x y z:S):= 128≤ D x z∧8*D x y≤D x z
abbrev Cubic :Type:= (n:Side)→Site n→Site n→Site n→ℝ
def bias (F G P:Scaff) : Cubic:= fun n x y z=> turn n x y z F G P
def Moderate (q:ℕ+) : Submodule ℝ Cubic where
    carrier:={F| ∃ c:ℝ,c≥0 ∧ ∀ᶠ i in atTop,∀ x y z:Site (side q i),remote x y z→‖F _ x y z‖ ≤ c*p 5 x z*p 1 x y}
    zero_mem':=⟨0, le_rfl, by simp⟩
    add_mem' {F G} h ht:= by
       obtain ⟨c,hc,h⟩:= h; obtain ⟨d,hd,ht⟩:=ht; refine ⟨c+d, add_nonneg hc hd,?_⟩; filter_upwards [h,ht] with i h ht x y z hv; let n:= side q i; exact le_trans (norm_add_le (F n x y z) (G n x y z)) ((add_le_add (h x y z hv) (ht x y z hv)).trans_eq (by ring))
    smul_mem' a F h:= by
       obtain ⟨c,hc,h⟩:=h; refine ⟨‖a‖*c,by positivity,?_⟩; filter_upwards [h] with i h x y z hv; simp only [Pi.smul_apply, norm_smul,mul_assoc];exact mul_le_mul_of_nonneg_left (by simpa only [mul_assoc] using h x y z hv) (norm_nonneg a)
lemma moderate_0 (V:Cubic): V∈Moderate q ↔ ∃ c:ℝ,c≥0 ∧ ∀ᶠ i in atTop,∀ x y z:Site (side q i),remote x y z→‖V _ x y z‖ ≤ c*p 5 x z*p 1 x y:= Iff.rfl
variable (hq:1<q.val)(F G P:Scaff)
include hq
lemma bias_leg (h:F∈air 1)(hp:G∈air 1)(he:P∈air 1)(i:Axis): bias F G (ds i P)∈ Moderate q:= by
    obtain ⟨a,ha,h⟩:= nice hq F h; obtain ⟨b,hb,hp⟩:= nice hq G hp; obtain ⟨c,hc,h'⟩:= nice hq P he; obtain ⟨d,hd,h₁⟩:= nice hq (ds i P) (air_ds i he); let H:=a+b+c+d; refine ⟨10^10*H^3,by unfold H; positivity,?_⟩; filter_upwards [h,hp,h',h₁] with i' hi hx hu hr x y z w; exact d_turn x y z (show 0 ≤ H from by unfold H; linarith) F G P (sturdy (by unfold H; linarith only [ha,hb,hc,hd]) F hi) (sturdy (by unfold H; linarith only [ha,hb,hc,hd]) G hx) (sturdy (by unfold H; linarith only [ha,hb,hc,hd]) P hu) w.1 w.2 i (sturdy (by unfold H; linarith only [ha,hb,hc,hd]) _ hr) -- L1/2 implicit
omit hq in
def biasL (F G:Scaff): Scaff→ₗ[ℝ] Cubic where
    toFun := bias F G; map_add' a b:= by ext1 n; ext1 x; ext1 y; ext1 z; simp [bias,turn,add_sub_add_comm (a _ _ _), add_mul,sum_add_distrib]
    map_smul' a b:= by ext1 n; ext1 x; ext1 y; ext1 z; simp [bias,turn, mul_sum,mul_assoc, ← mul_sub]
lemma bias_budget (h:F∈air 1)(ht:G∈air 1)(he:P∈air 2): bias F G P∈ Moderate q:= by
    change P∈Submodule.comap (biasL F G) (Moderate q); apply le_trans (le_of_eq (air_span (k:=2))) (Submodule.span_le.mpr ?_) he; rintro Sx ⟨l,x,hx,rfl⟩; obtain ⟨i,a,rfl⟩:=List.length_eq_two.mp hx; change biasL F G (graphS [i,a] x)∈ Moderate q; rw [show graphS [i,a] x = -(ds i (graphS [a] (x+step i))) from (by rw [graph_d,add_sub_cancel_right,neg_neg]),map_neg]; exact Submodule.neg_mem _ (bias_leg hq F G _ h ht (air_graph _ _ rfl) i)
variable (t u v w:Tet) (r' : ℝ)
-- ∗specific bias unscaled* contracted with L rows.C
omit hq in
def crest (r':ℝ)(u v t w:Tet): Cubic:= ∑ i:Axis,∑ j:Axis, mn t i j • bias (transfer (-1) u i) (transfer (-1) v j) (exchangeF r' w (-1) t)
omit hq
-- PP − expansion kernel.J integral
local notation "ε"=>epsilon q
def Union_z (n:Side)(e:ℝ)(x y z:Site n)(t u v w:Tet) : ℝ:= galley e (fun i=> Wpp e 1 w (-1) t n z i*ester n e (-1) t u v x y i)
lemma cut_lo (x y z:S)(e:ℝ)(he:0<e) : Union_z n e x y z t u v w - Wpp e 1 w (-1) t n z x * trinity n e t u v x y = e⁻¹^6 * crest 1 u v t w n x y z:= by
    unfold Union_z trinity galley ester crest; simp_rw [Wpp,Wpv,sprite_val]; let B:= exchangeF 1 w (-1) t n z; simp only [Pi.smul_apply, Finset.sum_apply,smul_eq_mul, bias,turn, mul_sum,← sum_sub_distrib]; -- wrong organization
    rw [sum_comm]; refine sum_congr rfl fun i _=>?_ ; rw [sum_comm]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro u _; unfold mn; field_simp; ring
include hq
lemma crest_est : crest r' u v t w∈ Moderate q:= Submodule.sum_mem _ (fun i _=> Submodule.sum_mem _ (fun j _=> (Moderate q).smul_mem _ (bias_budget hq _ _ _ (transfer_air i u (-1)) (transfer_air j v (-1)) (exchange_air w t r' (-1)))))
lemma sunroom : ∃ c:ℝ,c≥0 ∧ ∀ᶠ k in atTop,∀ x y z : Site (side q k), remote x y z→ let e:=ε k; let n:=side q k; ‖Union_z n e x y z t u v w - Wpp e 1 w (-1) t n z x * trinity n e t u v x y‖ ≤ c* (e*D x z)⁻¹^5 * (e*D x y)⁻¹:= by
    obtain ⟨c,hc,h⟩:= (moderate_0 _ ).1 (crest_est hq t u v w 1); refine ⟨c,hc,?_⟩; filter_upwards [h] with i hi x y z hv; intro e n; have he:= epsilon_pos q i; rw [cut_lo t u v w x y z _ he,norm_mul]; rw [Real.norm_of_nonneg (by positivity : 0 ≤ (ε i)⁻¹^6)]; apply le_trans (mul_le_mul_of_nonneg_left (hi x y z hv) (by positivity)); unfold fund; rw [mul_inv,mul_inv,mul_pow]; exact le_of_eq (by ring) -- Let e local
end YM.PositionX.Chir.Imprint
