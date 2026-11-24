import YM.OPE.Compatible.Gum.Stilt
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
open Flume.Script Shell
local notation "T!"=> Flume.Script.Tile G S.ratio.count
open Planned.PrimaryIntegral295.Carrier
local notation "U!"=> FUND S he U
local notation "CAX" => actLight S he H G
def Settle (a b:Site n)(t:ℝ) :=∀ k:Kv,(n.val:ℝ) ≤ t*(separation (decks k a) b:ℝ)
abbrev cloudFee (s K z: ℝ)(n:ℕ) := 4*z^n*(widthCost s n*K)
lemma turnH (q:Kv)(x:Q!): separation (decks q (HingeT S he G x)) (HingeT S he G (Varp S he H G q x)) ≤ 2:=by
      let p:=x.1.val; have hp: separation (decks q p.1) (ferry q p).1 ≤ 1:=by
         unfold ferry Step.used; split; next he=> simp only [separation,sub_sub_cancel]; rw [←wrap_step]; refine (within_size (step _) _).trans ?_; unfold size; simp [apply_ite (f:=Int.natAbs)]
         next h=>simp
      change separation (decks q (S.ratio.parent p.1)) (S.ratio.parent (ferry q p).1) ≤ _; rw [← (step_parent S.ratio H he q p.1).1]; exact (Work.E04.parent_separation S.ratio ..).trans (Nat.add_le_add_right hp _)
variable {a:ℝ}
-- frost with sums
lemma hoof (X: Finset Kv)(M:Funds Q!)(k:ℕ)(h:ZoneP S he k M a)(i j:Q!)(b:ℝ)(hb:0 ≤ b)(hp:∀ q∈X, (c.val:ℝ) ≤ b*(1+(separation (HingeT S he G (Varp S he H G q i)) (HingeT S he G j):ℝ))):
    (c.val:ℝ)^k * ‖(((∑ x∈X, leanI S he H G x)*M) i j )‖ ≤ 4*b^k * a:=by
       rw [Finset.sum_mul, Matrix.sum_apply] -- name
       apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (by positivity)).trans;rw [Finset.mul_sum]; apply (Finset.sum_le_sum (g:=fun _=> b^k*a) fun q hq=>?_).trans
       · rw [Finset.sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (show (X.card:ℝ) ≤ 4 from by exact_mod_cast (X.card_le_univ.trans_eq kvCard)) (show 0 ≤ b^k * a from mul_nonneg (pow_nonneg hb k) h.1)).trans_eq; ring
       erw [ leanAt]; apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (hp q hq) k) (norm_nonneg _)).trans; rw [mul_pow,mul_assoc]; exact mul_le_mul_of_nonneg_left (h.2 _ _) (pow_nonneg hb _)
omit H
lemma piax_nil (i:Flume.Script.Tab (Shade G) c)(j: Flume.Script.Tab T! c): (Piax S G U).acts c (starI i) j=0∧(Piax S G U).acts c j (starI i)=0:=by
       refine ⟨ROOT_left ..,?_⟩; rcases j with ⟨j,v|v⟩; exact ROOT_left U.dot (j,v) _; exact ROOT_cross U.dot (j,v) _ -- verify
include H
variable {s K':ℝ} (hσ:0<s) (hK:0≤ K') (hz:U.dot.strip s K')
include H t S L h A g hσ hK hz C hc G
lemma sameBias (i: Site c)(k:ℕ):Cold i i (Oriel C CAX-(show Funds (Flume.Script.Tab T! c) from (Piax S G U).acts c)) (cloudFee s K' 8 k) k:=by
     let V:= skipH S he H G; have hh: V=∑ x∈Finset.univ.erase 0, leanI S he H G x:=by
          unfold V skipH SUMp; rw [← Finset.sum_erase_add _ _ (Finset.mem_univ _), lean0, add_sub_cancel_right]
     have hp:=payD S he U t h s hz hK hσ k; intro p q; have hy : 0 ≤ StepN p.1 q.1 i i k * cloudFee s K' 8 k:=by unfold StepN cloudFee; have hx:= zero_le_one.trans (widthCost_ge hσ k); positivity
     rcases pile_or S he p with ⟨j,rfl⟩|⟨j,rfl⟩; · erw [Matrix.sub_apply,(cam_nil S he H (C:=C) j q).1,(piax_nil S U j q).1,sub_zero,norm_zero,mul_zero]; exact hy -- parameters
     rcases pile_or S he q with ⟨a,rfl⟩|⟨a,rfl⟩; · erw [Matrix.sub_apply,(cam_nil S he H (C:=C) a _).2,(piax_nil S U a _).2,sub_zero,norm_zero,mul_zero]; exact hy
     let v:= HingeT S he G j; let w:= HingeT S he G a; let b:ℝ:=8*(1+(separation v i:ℝ)+(separation w i:ℝ)); have hB:0 ≤ b:= by unfold b; positivity
     have hv(q)(hq:q∈ (Finset.univ:Finset Kv).erase 0): (c.val:ℝ) ≤ b*(1+ (separation (HingeT S he G (Varp S he H G q j)) w:ℝ)):=by
          let D:= HingeT S he G (Varp S he H G q j); have hz:c.val ≤8*(1+ separation v i+separation w i)*(1+separation D w):=by
               have hp:c.val /2 ≤ 2+ separation D v :=frost S he H j q (Finset.ne_of_mem_erase hq); have hg:= separation_triangle D w v; rw [separation_comm w v] at hg; have he:=separation_triangle v i w; rw [separation_comm i w] at he; have hh:c.val ≤ 6 + 2*separation D v:=by omega
               exact hh.trans (by nlinarith)
          unfold b; exact_mod_cast hz
     rw [Matrix.sub_apply,planeR S he U t h,camIs S he H U t h hc]; change _* ‖((SUMp S he H G* _ -U!⁻¹):Funds Q!) j a‖ ≤ StepN v w i i k * _; rw [show SUMp S he H G*_ - U!⁻¹= V*U!⁻¹ by unfold V skipH;rw [Matrix.sub_mul,one_mul],hh]; exact (hoof S he H (Finset.univ.erase 0) U!⁻¹ k hp j a b hB hv).trans_eq (by unfold b StepN cloudFee; rw [mul_pow]; ring)
end YM.OPE.Cascade.Rill
