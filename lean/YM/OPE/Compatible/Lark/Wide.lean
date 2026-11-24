import YM.OPE.Compatible.Lark.Hind
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
open Page Planned.PrimaryIntegral295.Carrier Boxes
include S he K U G L h A t g
lemma zipFi (k:ℕ)(α s v' d:ℝ)(hs: U.dot.strip s α)(he':0<s)(hr:0≤α)(hh:soot (4+k) (voteV S.patch S.kernel A.live A.clip 4) d)(hp:soot (4+k) (U.Fly A.live A.clip) v')(u: Bid.Dir G c):
     let x:= fieldT (cabin g) u
     let y:=spool G c u
     (c.val:ℝ)^k* ‖narrate c (U.talo A.live A.clip P) y-U.silo A.live A.clip P c ![y,y]‖ ≤8^(4+k) * widthCost s (4+k)*α*(2*v'+d)* ‖dance S he G x‖^2:=by
          intro x y; let V:= U.Fly A.live A.clip; let A':=voteV S.patch S.kernel A.live A.clip 3; let D':=voteV S.patch S.kernel A.live A.clip 4; let Q:= U.lip A.live A.clip; have hQ:= folk_whole (U.folk_lip A.pays); let Y:= dance S he G x; let w:=![Y,Y]; have hw:U.main.acts c*ᵥ y=Y:=(bounty S he U t h _).symm; let T:= U.talo A.live A.clip P; let L:= U.silo A.live A.clip P; let R:=collarY S.patch A.live; let D:= collarH S.patch P; have hz:=U.folk_crown (V:=P) A.pays; have ht:Summable R:=folk_whole (folk_collar S.patch A.pays); have hu:Summable ((-1:ℝ) • D):=folk_whole (folkS (folk_cap S.patch P) (-1))
          have hp1 : narrate c T y - L c ![y,y]= library c Q w - tuneH U.dot A' D' c w:=by
               unfold T narrate Boxes.talo L Boxes.silo; erw [raftReads _ U.rocket2 _ (folk_whole hz),show (fun i:Fin 2=> U.main.acts c*ᵥ (![y,y] i))=w from funext fun i=>by fin_cases i<;>exact hw,show (fun _ : Fin 2=>U.main.acts c*ᵥ y)=w from funext fun i=>by fin_cases i<;>exact hw]; change library c ((R+Q)+(-1:ℝ) • D) w - (library c R w+tuneH U.dot A' D' c w + (-1:ℝ)*library c D w)= _; rw [libAdd (R+Q) _ (ht.add hQ) hu,libAdd R Q ht hQ,libScale];ring
          rw [hp1, norm_sub_rev]; exact (TuneHi U.dot k he' hs hr A' D' hh v' hp w).trans_eq (by rw [Fin.prod_univ_two]; unfold w; change _ * (‖dance S he G x‖*‖dance S he G x‖)= _; ring)
omit S he K U G L h A t g in
def EonFee (k:ℕ) (a s b f d N:ℝ):ℝ:=
     let U:=widthCost s (k+24)*a
     let W:=4*N*8^(k+24)*(N*U*(3^(k+24)*f+3^(k+24)*b)+N^3*U^2*(3^(k+24)*d)^2)
     8^(4+k)*widthCost s (4+k)*a*(2*f+b)+W
omit S he K U G L h A t g in
lemma soot_le_k {k m j:ℕ}(z:Script I j)(v:ℝ)(h:soot k z v)(hp:m≤k):soot m z v:= budget_minor h (fun i=>mul_nonneg (zero_le_one.trans (payer m _)) (norm_nonneg _)) fun i=>mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast (notch_one i.xy)) hp) (norm_nonneg _)
include H
lemma feast (k:ℕ)(a s b f' d:ℝ)(hs:0<s)(hr:0 ≤ a)(hy: U.dot.strip s a)(hk: soot (k+24) (voteV S.patch S.kernel A.live A.clip 4) b) (hw:soot (k+24) (U.Fly A.live A.clip) f')(hz:soot (k+24) (voteV S.patch S.kernel A.live A.clip 3) d)(x:Bid.Dir G c):
  (c.val:ℝ)^k * ‖CostH S he H U t g A P x‖ ≤ EonFee k a s b f' d (Fintype.card (Slip G S.ratio.count))* ‖U.main.acts c *ᵥ (spool G c x)‖^2:=by
       have h1:=zipFi S he U t h (P:=P) k a s f' b hy hs hr (soot_le_k _ b hk (by omega)) (soot_le_k _ f' hw (by omega)) x; have h2:=iceberg S he H U t h k a s b d f' hs hr hy hk hw hz x; unfold CostH; dsimp only; let u:ℝ:= c.val; let Q:=spool G c x; let P':= dance S he G (fieldT (cabin g) x); have hy : U.main.acts c *ᵥ Q=P':= (bounty S he U t h _).symm; let D:= narrate c (U.talo A.live A.clip P) Q - U.silo A.live A.clip P c ![Q,Q]; let R:=(skipH S he H G * Matter S he U t g A x).trace; change u^k* ‖D/8-R/16‖≤ _ *‖U.main.acts c*ᵥ Q‖^2
       have hp: u^k * ‖D/8-R/16‖≤u^k * ‖D‖ + u^k*‖R‖:=by rw [← mul_add]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg (show 0≤u from Nat.cast_nonneg _) _); apply (norm_sub_le ..).trans; norm_num [norm_div]; linarith [abs_nonneg D, abs_nonneg R]
       rw [hy]; unfold EonFee; rw [add_mul]; exact hp.trans (add_le_add h1 h2)
end YM.OPE.Cascade.Rill
