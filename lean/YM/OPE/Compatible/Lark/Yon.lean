import YM.OPE.Compatible.Swoon.Clear
/-!
# Color trace of yy-charge exact vanish. Based on full-F Hess positive, all centers bought
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
abbrev Varp (G:Gauge)(k:Kv): (Active G (forest S.ratio he)) ≃ (Active G (forest S.ratio he)) := Equiv.prodCongr (fernV S he H k) (Equiv.refl _)
def leanI (G:Gauge)(k:Kv): Funds (Active G (forest S.ratio he)) := billsM (countingBasis X! G) (countingBasis X! G) (twirlF S he H k)
lemma leanGo (X: Z!)(j k): cash (countingBasis X! G) (twirlF S he H k X) j= if (axisK k).flip j.1.val.2 then -cash (countingBasis X! G) X (Varp S he H G k j) else cash (countingBasis X! G) X (Varp S he H G k j) :=by simp_rw [rangers_fee,spinF0]; split <;> rfl
lemma leanK (k:Kv)(x:Corn Q!)(p): (leanI S he H G k*ᵥ x) p= if (axisK k).flip p.1.val.2 then -x (Varp S he H G k p) else x (Varp S he H G k p):=by
     obtain ⟨u,rfl⟩:= (cash (countingBasis X! G)).surjective x;unfold leanI; rw [bill_at]; exact leanGo ..
lemma leanPa (k:Kv)(x y:Corn Q!): dotProduct (leanI S he H G k*ᵥ x) (leanI S he H G k *ᵥ y)=dotProduct x y:=by
     unfold dotProduct; -- reindex
     conv_rhs=>rw [← Equiv.sum_comp (Varp S he H G k)]
     exact Finset.sum_congr rfl fun i _=>by rw [leanK,leanK]; split; exact neg_mul_neg ..; rfl
lemma leanUnit (k:Kv): leanI S he H G k * leanI S he H G k=1:=by apply bill_eq (countingBasis X! G); intro x; unfold leanI; rw [← Matrix.mulVec_mulVec,bill_at,bill_at,spinF2,Matrix.one_mulVec]
lemma leanEq (k:Kv): (leanI S he H G k)ᵀ= leanI S he H G k:=by
     let L:=leanI S he H G k; have ht:Lᵀ*L=1:=testers fun x y=>by rw [←Matrix.mulVec_mulVec, transposes,leanPa S he H k,Matrix.one_mulVec]
     calc
        _= Lᵀ * (L*L):=by rw [show L*L=1 from leanUnit ..,mul_one]
        _=L:=by rw [← Matrix.mul_assoc,ht,one_mul]
lemma leanComm (k h:Kv): leanI S he H G k * leanI S he H G h =leanI S he H G (k+h):=by
    apply bill_eq (countingBasis X! G); intro x; unfold leanI; rw [← Matrix.mulVec_mulVec,bill_at,bill_at,bill_at]; apply congr_arg; ext1 i
    simp_rw [spinF0,show (trainV S he H k i).val.2=i.val.2 from ferry_axis .., ←trainW, add_comm h k]; by_cases hv:(axisK k).flip i.val.2<;> by_cases hz:(axisK h).flip i.val.2<;>simp [axisK_plus,Signed.mul_flip,axis_pin,hv,hz]
lemma lean0 : leanI S he H G 0=1:=by
    apply bill_eq (countingBasis X! G); intro x; unfold leanI; rw [bill_at,one_mulVec,show twirlF S he H 0 x=x from ?_]; ext1 i; simp [spinF0]
def SUMp (G:Gauge): Funds (Active G (forest S.ratio he)):=∑ k:Kv,leanI S he H G k
lemma ascSUM (v:Kv): (leanI S he H G v)* (SUMp S he H G)=SUMp S he H G:=by unfold SUMp; rw [Finset.mul_sum]; simp_rw [leanComm]; exact Equiv.sum_comp (Equiv.addLeft v) _
lemma sumH : SUMp S he H G*SUMp S he H G=(4:ℝ) • SUMp S he H G:=by
     nth_rw 1 [SUMp]; rw [Finset.sum_mul]; simp only [ascSUM, Finset.sum_const,Finset.card_univ,kvCard]; simpa using (Nat.cast_smul_eq_nsmul ℝ 4 (SUMp S he H G)).symm -- simp
end YM.OPE.Cascade.Rill
