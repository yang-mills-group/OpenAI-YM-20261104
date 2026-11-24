import YM.OPE.Compatible.Lark.Yon
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

def witV (G:Gauge)(i:Active G (forest S.ratio he)): Dual' (Keys G (Blocx S he H)) := (LinearMap.proj i).comp ((cash (countingBasis X! G)).toLinearMap.comp (EchoV S he H G).toLinearMap)
include S he H U h A G L g t
lemma leanKp (p:Kv): leanI S he H G p*FUND S he U= FUND S he U * leanI S he H G p:=by
     let q:= leanI S he H G p; let T:= FUND S he U; let A:= countingBasis X! G; let s:= viewer t h.2.1
     have hp(x: Z!): DoubleX S he H p (0,x)=(0,twirlF S he H p x):=Prod.ext (map_zero (AnalyticNext.QuarticMatch.Joint.shifts (G:=G) (axisK p) (offset p c))) rfl
     have hh:q * T*q=T:=by
         nth_rw 1 [show q=qᵀ from (leanEq ..).symm]; apply damage_eq A;intro x y; rw [both_cost]; erw [bill_at,bill_at,← tollY S he U h t,← tollY S he U h t]; exact (by rw [← hp,←hp]; exact bills_x S he H p h.1.cover t _ _ s.origin)
     change q*T=_; calc
        q*T=(q*T)*(q*q):=by rw [show q*q=1 from leanUnit .., mul_one]
        _=T*q:=by rw [←Matrix.mul_assoc,hh]
lemma leanKi (p:Kv): leanI S he H G p*(FUND S he U)⁻¹=(FUND S he U)⁻¹*leanI S he H G p:=by
     let T:=FUND S he U; let W:= leanI S he H G p; have hi:IsUnit T.det:=isUnit_iff_ne_zero.mpr (ulk_force S he U).det_pos.ne'; calc
         W*T⁻¹=(T⁻¹*T)*W*T⁻¹:=by rw [Matrix.nonsing_inv_mul T hi,one_mul]
         _=T⁻¹*W*(T*T⁻¹):=by rw [Matrix.mul_assoc T⁻¹ T W,← show W*T=T*W from leanKp S he H U t h p ,← Matrix.mul_assoc T⁻¹ W T, Matrix.mul_assoc]
         _=T⁻¹ * W:=by rw [Matrix.mul_nonsing_inv T hi,mul_one]
include C hc
lemma tradedCov: mount C (witV S he H G)= SUMp S he H G * (FUND S he U)⁻¹:=by
     let T:=SUMp S he H G; let M:=FUND S he U; let Z:= EchoV S he H G; let V:=witV S he H G; have hi:IsUnit M.det:=isUnit_iff_ne_zero.mpr (ulk_force S he U).det_pos.ne'
     let m:= countingBasis X! G
     have tv(k):leanI S he H G k*(T*M⁻¹)=T*M⁻¹:=by rw [← Matrix.mul_assoc,show leanI S he H G k*T=T from ascSUM ..]
     ext a b; let x:Corn Q!:=Pi.single b 1; let q:= (T*M⁻¹) *ᵥ x; let y:= (cash m).symm q; let v:= FetchS S he H G y
     have hZ: EchoV S he H G v=y:=by
        apply echoFetch; intro k; apply (cash m).injective; rw [← bill_at m m (twirlF S he H k) y, show cash m y=q from (cash m).apply_symm_apply q]; change leanI S he H G k *ᵥ q=q; unfold q; rw [Matrix.mulVec_mulVec,tv]
     have hw : cash m (Z v)=q:= hZ.symm ▸ (cash m).apply_symm_apply q
     have hx:M*(T*M⁻¹)=T:=by
         have hy:M*T=T*M:=by unfold T SUMp; rw [Finset.mul_sum,Finset.sum_mul];exact Finset.sum_congr rfl fun k _=>(leanKp S he H U t h k).symm
         rw [← Matrix.mul_assoc,hy,Matrix.mul_assoc, Matrix.mul_nonsing_inv M hi,mul_one]
     have hh : C.P v=V b:=LinearMap.ext fun i=>by
          rw [C.turns,hc]; change ((cash m (Z i)) ⬝ᵥ (M *ᵥ cash m (Z v)))/4= _; rw [hw,show M *ᵥ q= T *ᵥ x by unfold q; rw [Matrix.mulVec_mulVec,hx]]; unfold T SUMp; simp only [Matrix.sum_mulVec,dotProduct_sum] -- name
          have he₁(k:Kv): (cash m (Z i)) ⬝ᵥ (leanI S he H G k*ᵥ x)=V b i:=by
               nth_rw 1 [← leanEq]; rw [transposes]; unfold leanI; rw [bill_at,echoRot,dotProduct_single]; rw [mul_one];rfl -- shadow he
          simp_rw [he₁]; rw [Finset.sum_const,Finset.card_univ,kvCard,nsmul_eq_mul,Nat.cast_ofNat];ring
     change C.wick (V a) (V b)= (T*M⁻¹) a b; rw [wix_sym Wμ C]; change V a (C.inverse _) = _; rw [← hh, Law.solves]; change cash m (Z v) a=_; rw [hw,show q=_ from rfl]; change ((T*M⁻¹)*ᵥ Pi.single b 1) a=_; simp
end YM.OPE.Cascade.Rill
