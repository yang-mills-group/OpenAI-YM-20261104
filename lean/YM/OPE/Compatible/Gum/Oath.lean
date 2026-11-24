import YM.OPE.Compatible.Gum.Policy
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
variable {s K' v':ℝ} (hσ:0<s) (hK:0≤ K') (hz:U.dot.strip s K')
lemma tourD (a b:Site n)(v:Kv): separation (decks v a) (decks v b)=separation a b:=by unfold decks affine;rw [separation_translate,separation_signed]
lemma paneBound (i j:Site c) (p q:Q!)(v:Kv)(hv:0≤v')(hp:Settle i j v'):
   let a:=HingeT S he G p
   let b:=HingeT S he G q
   let u:=HingeT S he G (Varp S he H G v p)
   (c.val:ℝ)≤4*v'*(1+(separation a i:ℝ)+ (separation b j:ℝ))*(1+(separation u b:ℝ)):=by
       intro a b u; have ha:=hp v; apply ha.trans; have he : (separation (decks v i) j) ≤ 2+separation a i+separation b j+separation u b:=by
           have he': separation (decks v a) u ≤2:=turnH S he H v p; have ht:=separation_triangle (decks v i) (decks v a) u; rw [tourD i a,separation_comm i a] at ht; have hp:=separation_triangle (decks v i) u j; have hh:=separation_triangle u b j; omega
       apply (mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ)|>.mpr he) hv).trans; push_cast; rw [mul_comm 4 v', mul_assoc v', mul_assoc v']; apply mul_le_mul_of_nonneg_left _ hv; nlinarith
include S H U t A L g G h hσ hK hz C hc
lemma spiral (k:ℕ)(a b:Site c)(hv:2≤v')(hp:Settle a b v'): Cold a b (Oriel C CAX) (cloudFee s K' (4*v') k) k :=by
       have hb:0≤ v':= le_trans (by norm_num) hv; have hy:= payD S he U t h s hz hK hσ k
       intro i j; have hg:0 ≤ StepN i.1 j.1 a b k * cloudFee s K' (4*v') k:=by unfold StepN cloudFee;have hh:= zero_le_one.trans (widthCost_ge hσ k); positivity
       rcases pile_or S he i with ⟨i,rfl⟩|⟨i,rfl⟩; · rw [(cam_nil S he H (C:=C) i j).1,norm_zero,mul_zero]; exact hg
       rcases pile_or S he j with ⟨j,rfl⟩|⟨j,rfl⟩; · rw [(cam_nil S he H (C:=C) j _).2,norm_zero,mul_zero]; exact hg
       rw [camIs S he H U t h hc]; let x:= HingeT S he G i; let y:= HingeT S he G j; let Q:= 1+(separation x a:ℝ)+(separation y b:ℝ); have hQ:0 ≤ Q:=by unfold Q; positivity
       change _≤ StepN x y a b k*_; exact (hoof S he H Finset.univ _ k hy _ _ (4*v'*Q) (by positivity) (fun v _=> paneBound S he H a b _ _ _ hb hp)).trans_eq (by unfold cloudFee StepN Q;rw [mul_pow]; ring)
lemma grainG (k:ℕ)(a: Site c)(hv:2≤v'): Fund k a (Piax S G U) C (fun i:ℕ=> cloudFee s K' (4*v') i) CAX :=by
       let p (k:ℕ):=(cloudFee s K' (4*v') k); have hp(i):cloudFee s K' 8 i≤p i:=by
            unfold p cloudFee; apply mul_le_mul_of_nonneg_right _ (mul_nonneg (zero_le_one.trans (widthCost_ge hσ i)) hK); gcongr; linarith
       constructor
       · refine ⟨?_,fun i=>?_⟩; change 0≤p 0; unfold p cloudFee; simp only [pow_zero]; have hv:= zero_le_one.trans (widthCost_ge hσ 0); positivity
         rcases pile_or S he i with ⟨i,rfl⟩|⟨i,rfl⟩
         · erw [(cam_nil S he H (C:=C) _ _).1,norm_zero]; change 0≤p 0; unfold p cloudFee; simp only [pow_zero]; have hv:= zero_le_one.trans (widthCost_ge hσ 0); positivity
         erw [camIs S he H U t h hc]; let P:=leanI S he H G; let Q(i):=HingeT S he G i; let b:= (c.val:ℝ); have hb:0≤b:=Nat.cast_nonneg _; have ht(i j:Q!)(k:Kv): b ≤ b * (1+(separation (Q (Varp S he H G k i)) (Q j):ℝ)):= le_mul_of_one_le_right hb (le_add_of_nonneg_right (Nat.cast_nonneg _))
         exact (show _ by simpa only [pow_zero,one_mul,mul_one,cloudFee,SUMp] using hoof S he H Finset.univ _ 0 (payD S he U t h s hz hK hσ 0) i i b hb (fun v _=> ht _ _ v))
       intro i hi x y; exact ((sameBias S he H U t h hc hσ hK hz a i) x y).trans (mul_le_mul_of_nonneg_left (hp i) (show 0≤ StepN x.1 y.1 a a i by unfold StepN; positivity))
end YM.OPE.Cascade.Rill
