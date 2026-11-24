import YM.RGComparison01.Sensor.Probe
import YM.RGComparison01.Sensor.Basin
/-! # Rank and simultaneous Grade at marked analytic calls
 q internal may be chosen larger than sum of ranks.Need prove using genuine
 b derivative grading. Inputs one-step. Normalization unchanged. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.Sensor
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat Deck
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Gauge
open AnalyticBridge VerifiedReset Collection Quotes Extra.Iteration Song Refrain Reserves OmitClusters
open Push.Uniform Fare Sienna Lapis Lotus Pledge Baked Merge Palette Team Pulse
open AuxFabric AuxPackage AuxConstant Metric Next.Fluctuations Bid
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace

variable {G : Gauge}
section lamps
variable {c f : Side}{S:StepData c f} (F:Forest S.ratio)(ρ: Bid.Dir G c →AxisChart G F)
    {R:RG.Rep G f} {ι:Type} (M:ι→ Leaf R)(g:ι→ℝ) (p:Finset ι)
local notation "X"=> Positions (Uniform.Primary c G)
local notation "Y"=> Poll.Body (Precision.Key F G)
variable (Q:ℕ)
variable (Z:ι→Poll.Body (Precision.Key F G)→ℝ×Positions (Uniform.Primary c G)→ℝ)
    (q:ℕ){P:BudgetPoint}{a B C d W β:ℝ}{k j:ℕ}
local notation "t"=>((sign M S))
def jumbo (F:Forest S.ratio)(Z:ι→Poll.Body (Precision.Key F G)→ℝ×Positions (Uniform.Primary c G)→ℝ): Poll.Body (Precision.Key F G)→ℝ×Positions (Uniform.Primary c G)→ℝ:= if Draft (sign M S) p then ((∏ i∈p,Z i)* (Sensor.spur _)^(Q-p.card*q)) else 0
local notation "J"=> Sensor.jumbo M p Q q F Z -- order check
local notation "f0"=> (Staircase.cardTest M g S p)
lemma joint_product (hp:Draft (Palette.sign M S) p)(U:Config G f): Staircase.cardTest M g S p U= ∏ i∈p,(M i).ingredient U * g i:=by -- syntax `∏ i∈p,(...) * g i`
   rw [Staircase.cardTest,dif_pos hp]; unfold Team.ingredients
   rw [Finset.prod_mul_distrib,show Finset.prod (team M _).own (fun i=>i.ingredient U)= _ from Finset.prod_image (fun i hi j hj h'=> hp hi hj (congr_arg (fun L:Lotus.Leaf R=> L.turn.badge S) h'))]

local notation "u"=> gStep β
lemma stockp (p0 : BudgetPoint) (β a D:ℝ)(hf : 0 < gStep β)(hp:p.card*q ≤ Q)(h:∀ i∈p, Render F ρ p0 β (fun y=> (M i).ingredient y*g i) (Z i) q a D 1): Render F ρ p0 β f0 J Q a D 1:=by
   by_cases hx: Draft (Palette.sign M S) p
   · let f i U:= (M i).ingredient U*g i
     have ht(y):Staircase.cardTest M g S p y= ∏ i∈p,f i y:= joint_product M g p hx y
     refine ⟨fun x U=>?_, ⟨?_,?_⟩,zero_le_one,fun y hy=> ?_,fun y hy z hZ hX=>?_⟩
     · rw [ht,ht]; exact Finset.prod_congr rfl fun i hi=> (h i hi).invariant ..
     · simp_rw [show f0= fun y=>_ from funext ht]; exact Finset.measurable_fun_prod p fun i hi=> (h i hi).safe.meas
     · -- purchase
       refine ⟨∏ i∈p,(M i).weight * |g i|,fun i=>?_⟩
       rw [ht]; rw [norm_prod]; apply Finset.prod_le_prod (fun _ _=> norm_nonneg _); intro j hj; unfold f; rw [norm_mul]; exact mul_le_mul_of_nonneg_right ((M _).earn _) (norm_nonneg _)
     · rw [ht]; rw [← Real.norm_eq_abs,norm_prod]; exact Finset.prod_le_one (fun i _=> norm_nonneg _) (fun i hi=> (h i hi).allReal y hy)
     rw [ht, jumbo, if_pos hx]; let y' := AuxMiles.tests F ρ β y z; let v:= gStep β
     rw [show ∏ i∈p,f i y'=∏ i∈p,v⁻¹ ^ q* Z i z (v,y) from Finset.prod_congr rfl fun i hi=> (h i hi).healthy y hy z hZ hX,prod_mul_distrib,prod_const,←pow_mul,Pi.mul_apply,Pi.mul_apply,Finset.prod_apply,Finset.prod_apply,Pi.pow_apply,Pi.pow_apply]
     change v⁻¹^(_ * _) * _= v⁻¹ ^ Q * (_* v^(Q-p.card*q)); let m:= Q-p.card*q; have ht' : Q= p.card*q + m:= by omega
     nth_rw 1 [show q*p.card=p.card*q from mul_comm ..] -- ht.Q may inside power.Use separately
     rw [show v⁻¹^Q=v⁻¹^(p.card*q)*v⁻¹^m from Eq.trans (congr_arg (v⁻¹ ^ ·) ht') (pow_add ..)]
     rw [inv_pow _ m]; change _=_ * (_* v^m); have hv (b d:ℝ) : b*d=b*(v^m)⁻¹*(d*v^m):=by rw [mul_assoc, mul_left_comm (v^m)⁻¹ d, inv_mul_cancel₀ (pow_ne_zero m hf.ne'),mul_one]
     exact hv _ _
   rw [jumbo,if_neg hx,show f0= 0 from funext (fun i=> dif_neg hx)]
   obtain ⟨hA,hB,hC,h,hX⟩:= AuxPackage.blank_render F ρ p0 β (q:=Q) (a:=a) (d:=D); exact ⟨hA,hB,zero_le_one,fun i hi=> (h i hi).trans zero_le_one,hX⟩
lemma grade (hq:p.card*q≤ Q)(he:Q ≤ k+1)(hd: d≤1)(hn:p.Nonempty)(H:∀ i∈ p, Probe (Z i) k j q d B (wage k Q)⁻¹ (wage k Q)⁻¹) : Probe (J) k (p.card*j) Q d B 1 1:=by
    unfold jumbo; split; next hz=> exact seasonal Z p Q hn hq he hd H
    exact Probe.trivial.raise zero_le_one zero_le_one le_rfl le_rfl
end lamps
section seats
variable {c f:Side} {S:StepData c f} {D W r H γ β σ C Λ:ℝ} {k j:ℕ} (T : Tube G S) (F:Forest S.ratio) (ρ:Bid.Dir G c→AxisChart G F)
    (X:Before G σ C S.patch.J S.kernel (k+3))
local notation "P'" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)
local notation "Ps" => (X.tables T.high S.patch)
variable (hE : X.Service F T.high T.up ρ)
variable (hq:Larger (G:=G) S) (hv:T.up.Bounds T.high σ C Λ)
variable (hb : (Fintype.card (Joint F G):ℝ)≤D) (hD : 1 ≤ D)
local notation "sT" => Before.Service.trailCost Ps (k+3)
local notation "u" => fun w:ℝ=> tally Ps D w X.Z k G
variable (Q:ℕ) (R:RG.Rep G f)(p:Pressure.Cell f)(n a:ℕ)(hn:2≤n)
local notation "J"=> Sensor.mark R n p hn a
local notation "g"=> gStep R.beta
local notation "Γ"=> γ • testF F ρ p
lemma wakes (h:‖γ‖*(lensWeight (gStep R.beta) (R.p.threshold))≤ 1) (Z:BudgetPoint)(he:Z=R.p): Render F ρ Z R.beta (fun y=> (J).ingredient y*γ) (γ • testF F ρ p) 2 r W 1:=by
   subst Z; refine ⟨fun x y=>congr_arg (·* γ) ((J).glows ..),⟨(J).borel.mul measurable_const,?_⟩,zero_le_one,fun V hv=>?_,fun y hy z hz hZ=>?_⟩ -- fix
   · refine ⟨1,fun i=>?_⟩; rw [norm_mul,mul_comm]; exact (mul_le_mul_of_nonneg_left ((J).earn _) (norm_nonneg _)).trans h
   · rw [← Real.norm_eq_abs,norm_mul,mul_comm]; exact (mul_le_mul_of_nonneg_left ((J).earn _) (norm_nonneg _)).trans h
   let L:= AuxMiles.tests F ρ R.beta y z; have hv' : Healthy R.p.threshold (neighbors n p.1) L:= by unfold Healthy; unfold L; rw [hZ]; simp
   change masked _ _ _ L * γ=_; rw [masked_eq _ _ _ _ hv']; change (g)⁻¹^ (2:ℕ)*_*γ = _* (γ * G.price (faceValue L p)); ring
include hE hq hv hb hD
lemma nights (he:r≤ (X.tables T.high S.patch).horizon) (ht:r≤1) (h: Before.Service.trailCost Ps (k+3)*r+r*W≤1) (hw:0≤ W) (hk:2 ≤ k+1)(hf: ‖γ‖ * (u W) ≤ (wage k Q)⁻¹): Probe (γ • Sensor.testF F ρ p) k k 2 r W (wage k Q)⁻¹ (wage k Q)⁻¹:= Probe.raise (boosts hk (portal T F ρ X hE hq hv hb hD p he ht h hw) γ) hf hf le_rfl le_rfl
end seats
end YM.RGComparison01.Sensor
