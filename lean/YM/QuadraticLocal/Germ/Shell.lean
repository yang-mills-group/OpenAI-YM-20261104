import YM.QuadraticLocal.Germ.Focal
/-!
# Accounting after λ-kernel envelopes (explicit q factor & Signed product).

 Remain on EXACT same test & origin inventory when extracting.Neur. Only per-marker multipliers;
 for per-block with separate slots for newer errors see downstream (Room). All rows, captions & full
 input.Output FullBudget with readiness and charging. Does NOT infer simultaneous readiness under
 every shrinking Universe.Extension; hypotheses are `FullBudget at` all costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Shell
open Function Filter Finset Wilson Lattice RG Marker Push Push.AbsoluteSums MeasureTheory Animals
open RG3.Forms RG3.Held RG3.Script.Picnic
open Integration.LocalComparison Mix
open scoped Topology Classical Matrix.Norms.Frobenius BigOperators ContDiff
variable {G:Gauge}{n:Side}{p:BudgetPoint}{o:Site n}{P:Rep G n}{α:Type*}{V:Type}[Fintype V][DecidableEq V]{R:Census V}{X:V→Site n}
variable {S:Support n}{F:Config G n→ℂ}{a b c δ κ : ℝ}
-- uses native grain currency exactly. hE chosen before unit cost.
lemma grain_scale (hf:p.Regular S F)(h:Mix.grain p S F o a)(hp:0≤b): Mix.grain p S (fun U=> b • F U) o (b*a):=by
   obtain ⟨f,h,hP,hC⟩:=h; refine ⟨fun i=>b*f i,fun i=>mul_nonneg hp (h i), ?_,fun k hk hx U hU=>?_⟩
   · refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hP hp); rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; ring
   let L:= b • ContinuousLinearMap.id ℝ ℂ; change ‖leftDerivs (L ∘ F) k U‖≤ _; rw [Local.left_linear L k (hf.smooth U hU) hk]; change ‖b • (leftDerivs F k U)‖≤ _; rw [norm_smul,Real.norm_of_nonneg hp]; exact mul_le_mul_of_nonneg_left (hC k hk hx U hU) hp
variable {w:V→ℝ}(hw:∀ i,0<w i)(T:Taste α X P R)
private lemma regular_scaled {b:ℝ}(h:p.Regular S F): p.Regular S (fun U=> b • F U):= Next.Foundations.regular_smul (↑b :ℂ) h
private lemma remains (c:R.Mode→ℝ) {x:α} (h:(T.leaf x).Active): ((priceNormalized c T).leaf x).Active:=by
   let T':=T.leaf x; let Y:=(priceNormalized c T).leaf x; let X':=T'.contents; let Y':=Y.contents
   refine ⟨⟨h.articles.proper,h.articles.pins,fun i=> regular_scaled (h.articles.regular i),h.articles.occurs,?_,?_,?_,?_,?_⟩,⟨h.captions.card,h.captions.pins⟩⟩
   · intro i j hi; exact h.articles.retained i j (fun ht=> hi (by change (c (T.menu.marks i j))⁻¹ • (T.leaf x).contents.entries i j=_; rw [ht,smul_zero]))
   · exact fun i j U V' hx ht=> congr_arg (fun x:ℂ=> (c (T.menu.marks i j))⁻¹ • x) (h.articles.inspects i j U V' hx ht)
   · exact fun i j u hu=> h.articles.keeps i j u (fun ht=> hu (by change (c (T.menu.marks i j))⁻¹ • (T.leaf x).contents.entries i j u=_; rw [ht, smul_zero]))
   · exact fun i j=> (h.articles.meas i j).const_smul ((c (T.menu.marks i j))⁻¹)
   exact fun i j v U=> congr_arg (fun x:ℂ=> (c (T.menu.marks i j))⁻¹ • x) (h.articles.invi i j v U)
variable (cost : V→ℝ) (hc:∀ i,0<cost i)
local notation "z"=> envelopeProduct cost
local notation "K"=> fun v : R.Mode => (envelopeProduct cost v)⁻¹
local notation "a'"=> w / cost
local notation "T'"=> priceNormalized z T
variable (H:FullBudget p T (w / cost) κ b δ)
include hw hc H
lemma restore : Nonempty (RelativeBudget p T w κ z b δ):= by
   let Z:R.Mode→ℝ:= z; have hp i:0< Z i:=prod_pos fun j _=> hc j; have hh i:0≤ K i:=inv_nonneg.mpr (hp i).le
   have he i: Poly.toll a' i= Poly.toll w i * K i:= by change (∏j∈i.val,w j/cost j)=_; simp_rw [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]; rfl
   let v:= T'; let F:=v.menu; let A i:= T.menu.rays i; let t i j:= T.menu.marks i j; let a₀ i:=(K (A i))*H.white i; let b₀ (x:ℕ×ℕ):=K (t x.1 x.2)*H.black x; let k i:= K (T.tag i)*H.gold i; let u (i:V):=K (R.fire i)*H.unitBound i; have ht i (s:Support n) a: Poly.toll w i*p.mass s (K i*a)=Poly.toll a' i*p.mass s a:=by rw [he]; unfold BudgetPoint.mass; ring
   have hX(x y:ℝ)(a:ℂ)(hx:0≤x)(h:‖a‖≤y): ‖x • a‖≤x*y:=by rw [norm_smul,Real.norm_of_nonneg hx]; exact mul_le_mul_of_nonneg_left h hx
   refine ⟨hp,(show Z R.quiet=1 from (Poly.quiet_toll)),a₀,b₀,k,u,(fun i=>remains T Z (H.active i)),hw,H.divisor,fun i=> mul_nonneg (hh _) (H.white_nonnegative _), fun i=>?_,fun x i=> regular_scaled (H.regular_law x i),fun i=>mul_nonneg (hh _) (H.black_nonnegative i),fun x i j U=>hX _ _ _ (hh _) (H.forced x i j U),fun i=>mul_nonneg (hh _) (H.gold_nonnegative i),fun x i=>hX _ _ _ (hh _) (H.caption x i),fun i=>mul_nonneg (hh _) (H.unit_nonnegative i),fun x i=>hX _ _ _ (hh _) (H.unit x i),?_,?_⟩
   · exact ⟨fun x k hk=> grain_scale (H.regular_law x i) ((H.regular i).controls x k hk) (hh _)⟩
   · intro v; obtain ⟨a,b,h,hq,hv⟩:= H.regularTotal v; refine ⟨a,b,?_,?_,?_⟩ -- edit
     · convert h using 1; ext i; dsimp only [priceNormalized]; split; exact ht _ _ _; rfl
     · convert hq using 1; ext i; dsimp only [priceNormalized]; split; exact ht _ _ _; rfl
     change w v*( (Z (R.fire v))⁻¹* H.unitBound v)+a+b ≤ _; rw [show Z (R.fire v)=cost v from Poly.solo_toll _, ← mul_assoc, ← div_eq_mul_inv]; exact hv
   intro i; convert H.forcedTotal i using 1; ext j; dsimp only [priceNormalized]; split; exact ht _ _ _; rfl
end YM.QuadraticLocal.Shell
