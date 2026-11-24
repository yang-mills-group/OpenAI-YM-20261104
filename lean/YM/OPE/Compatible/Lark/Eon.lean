import YM.OPE.Compatible.Lark.Rash
/-!
# All trace accounts, ordinary torque identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cascade.Rill
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
variable {I J:Type}{G:Gauge}{n c f:Side}
variable (S:StepData c f)(he:Odd S.ratio.count.val)(H:Even c.val)(X: Plot H)
local notation "μ"=> even_both S.ratio H
local notation "X!"=> forest S.ratio he
local notation "W!" => stroll S he H X
local notation "V!" => valley S he H X
local notation "Z!" => AxisChart G X!
local notation "Qµ"=> Blocx S he H
local notation "P!" => Keys G X.Free
local notation "J!" => Keys G (Blocx S he H)
open PertExtension Series ScriptJ GaussianScore Work.F05 Glass Coin Pilot Radial Flock
attribute [local instance] Gauge.frobInner
variable {K:Sponsor G}{T:Seasons K}{d i:ℕ}{v u r b:ℝ}
variable {A:Alps K T i v}{D:Alps K T d u} (U:Boxes G S.patch S.kernel){L:Matrix (Body 1 f) (Body 1 c) ℝ}{g: Bid.Dir G c→AxisChart G (forest S.ratio he)}
variable (t:S.Choices) (h:licensed S he U A.clip A.live L A.sky g)
variable (V:Bor H D b)(Y:Elm A S H t r){P:ChartRatio G}(ht:LocalRatio P)
local notation "LK"=> Keys G (Stand.Free (stroll S he H X))
local notation "Wμ"=> Chart.tangent G Qµ
variable {C:Law (Keys G (Blocx S he H))}(hc:Roomy S he H U C)
-- accounting index and oriented trans
local notation "Q!"=> Active G (forest S.ratio he)
local notation "S!"=> Bid.Dir G c × AxisChart G X!
-- effort graph taut bounds use large power k≥m+24 (Matter dims 4+4+12=20; trace adds4).
open Page Planned.PrimaryIntegral295.Carrier
lemma scaleXX (k m:ℕ)(n b c d e f u w:ℝ)(hn:1≤n)(hb:0≤b)(hx:0≤c)(he:0≤e)(hf:0≤f)(_hw:0≤w)(_hu:0≤u)(h:n^(m+24)*d≤4*(n^4*b)*8^k*((n^4*b*(c*(n^4* (3^k*w^2)*f))+ n^4*b*(c*(n^4* (3^k*w^2)*e)))+(n^4*b)*((n^4*b*(n^4*b*(c*(n^4*3^k*w*u))*c))*(n^4*3^k*w*u)))): n^m*d≤4*b*8^k*(b*c*(3^k*f+3^k*e)+b^3*c^2*(3^k*u)^2)*w^2:=by
      have hp:0<n:=zero_lt_one.trans_le hn
      apply le_of_mul_le_mul_left _ (pow_pos hp 24)
      rw [← mul_assoc,← pow_add,Nat.add_comm 24 m] -- edit
      apply h.trans; have hQ : n^(12:ℕ) ≤ n^(24:ℕ):= pow_le_pow_right₀ hn (by decide)
      calc
       _ = n^12*((4*b*8^k)*b*c*(3^k*f+3^k*e)*w^2)+n^24*(4*b*8^k*b^3*c^2*(3^k*u)^2*w^2):=by ring
       _≤ _:=by apply (add_le_add_left (mul_le_mul_of_nonneg_right hQ (by positivity)) _).trans_eq; ring -- orientation
local notation "R!"=> U.Fly A.live A.clip
local notation "M!"=> pane X! t A.clip A.live
include U A L h t g S he H
lemma iceberg (m:ℕ)(a s b d f:ℝ)(hp:0<s)(hh:0≤a)(hy:U.dot.strip s a)(ht: soot (m+24) (voteV S.patch S.kernel A.live A.clip 4) b) (hw:soot (m+24) (U.Fly A.live A.clip) f)(hz:soot (m+24) (voteV S.patch S.kernel A.live A.clip 3) d)(x:Bid.Dir G c):
     let k:=m+24
     let N:ℝ:= Fintype.card (Slip G S.ratio.count)
     let W:=widthCost s (m+24)*a
     (c.val:ℝ)^m * ‖(skipH S he H G * Matter S he U t g A x).trace‖ ≤4*N*8^k*(N*W*(3^k*f+3^k*b)+N^3*W^2*(3^k*d)^2)*‖dance S he G (fieldT (cabin g) x)‖^2:=by
          intro k N W; obtain ⟨ha,hQ⟩:= Pyramid S he U t h x ht hw; have hY:=pyre S he U t h x hz; have hA:=payD S he U t h s hy hh hp k; have hc:=PaidT.add ((hA.links hQ).add (hA.links ha)) (((((hA.links hY).links hA).links hY)).neg); have ht(k:ℕ)(Z:Matrix Q! Q! ℝ)(c)(h:ZoneP S he k Z c):=saluteTrace S he H k Z c h
          have hv:= ht k _ _ hc; rw [show (Fintype.card Q!:ℝ)= _ from cards ..] at hv; unfold Matter; dsimp only; rw [sub_eq_add_neg]; exact scaleXX k m _ _ _ _ b f d _ (by exact_mod_cast c.pos) (Nat.cast_nonneg _) hA.1 ((tsum_nonneg (show soot _ _ b from ‹soot _ _ b›).1).trans ‹soot _ _ b›.2.2) ((tsum_nonneg hw.1).trans hw.2.2) (norm_nonneg _) ((tsum_nonneg hz.1).trans hz.2.2) hv
end YM.OPE.Cascade.Rill
