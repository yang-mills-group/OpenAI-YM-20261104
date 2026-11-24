import YM.Contacts.Junction.Wing
/-! # Kernel difference quals. Includes curvature comparison with only relative weights.
 Use generalized occupancy at interpolation points.Delta.Channel. Based Token + extended integrand.
 -/
noncomputable section
namespace YM.Contacts.Junction
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
open Function Filter Set Finset Metric Lattice RG Gauge Pressure Wilson PertExtension.Series MeasureTheory
open Radial Precision Matrix PhysicalNext.Repeat Bid Tree Tested PertExtension.Chart Lapis Milling
open YM.Stationary Milling.Forge Exterior Push.Uniform ConnectedActivityE6 Blaze Shield Poll Next.SectorChange Fare Model.Arbor
open scoped Topology ContDiff Pointwise BigOperators Matrix.Norms.Frobenius Classical NNReal
variable {G:Gauge} {P : ChartRatio G} {σ C e v d t K τ ω' s a R:ℝ}{n k j r i q:ℕ}
namespace Provision
open Ion House Lintel Lintel.Angle Cove Model Province.Costing Lumen Pulse Spine Steam
open Milling.Garf Loom Loom.Patch Meter Capture Buyer Push Current Milling.Spark
open Sienna Lantern Planned.JetPort Dew Uniform StagePort
open Push.AbsoluteSums SectorMeasure Presented Next.Fluctuations Next.Fluctuations.Sector
open Token
variable {U:Teller G} {L:Side} {M:Uniform.ChartPrices}{X:G.ColorIndex} {Φ:ℕ→StagePort G U P X k L σ C M n}
local notation "ι" => StagePort.dew ∘ Φ
local notation "E" => (fun i=> Dew.X (ι i))
local notation "Y" => (fun i=> Dew.Y (ι i))
local notation "μ" => (fun i=>StagePort.μ (Φ i))
local notation "γ" => γC (ι)
variable {N:Meter}{Q:ℝ→ℝ}
section global
variable {p:StagePort G U P X k L σ C M n}
local notation "D" => p.dew
local notation "Z" => prime G U.bind q v s p.dew.β R
variable (hh:Up p d a j)(he : (Fintype.card (Bond p.dew.c):ℝ)≤ R) (hb:∀ x:Config G p.dew.f, flags p.budget.threshold x=∅ → |p.poll x|≤1) (hz: PaintSupply G q v)(ht: Brush q s 1 Real.exp 0) (hx' : 0 ≤ Token.prime G U.bind q v s p.dew.β R)
include hh he hb hz ht hx'
lemma river_b (x:(D).X)(hx:‖x‖<1) : Brush q (Z*p.push x) 1 p.push x:= by
   let φ:=(D).S; let F:=(D).B; let Yp:=F.order G; have hR:=hh.truePE; have hG:=(hR.stitches.large).1; let M:= Pane.virgin (D).T p.budget (D).β; let f x y:=p.traceK x y; let Z':=Z; obtain ⟨a,ha⟩:= φ.density_bound hG (D).β; obtain ⟨b,hb'⟩:= ((M.envelope hR.intake.cap).mul (gates hh).1).cost; let B:=|a| * |b|;
   have hu x y: ‖f x y‖ ≤ B:= by
      let z:= F.drape y; let w:= Cove.ship x; let f':=(D).S.density (D).β z w; let p':=p.quake z; have hz :0≤ f':= by unfold f'; apply StepData.density_positive .. -- API
      unfold f traceK notion; rw [Fare.total, mul_assoc, norm_mul,Real.norm_of_nonneg hz]; exact mul_le_mul ((ha z w).trans (le_abs_self _)) ((hb' z).trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)
   have hF v (hv:‖v‖<1) y: Brush q (Z'*f v y) 1 (fun x=>f x y) v := by
      let z:= (p.dew.B.drape y); let P:=p.quake z; have hi:0≤P:= (Real.exp_pos _).le.trans (StagePort.qual p z).1; let E':= (fun x=> p.notion x y);
      have he := (Token.volumeQ F p.dew.T p.budget p.dew.β y hz he v hv.le ht).smul P; rw [Real.norm_of_nonneg hi,hR.intake.ready.knobs,mul_left_comm] at he
      refine (he.climb (?_) le_rfl).shimmy (?_); swap; exact Eventually.of_forall fun u=> mul_comm _ _; exact le_of_eq (congr_arg (Z'* ·) (mul_comm P (p.notion v y)))
   have hg v : Integrable (p.traceK v) (p.dew.B.order G):= ((StagePort.billsV hh v).2.integrable _); have hg' : Meristem f x Yp q:= (Meristem.points f Yp ⟨fun _=>Z'*B, integrable_const _, (continuous_norm.continuousAt.eventually (gt_mem_nhds hx)).mono fun y hy i=> (hF y hy _).climb (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hu y i)) hx') le_rfl⟩ (Eventually.of_forall fun _=> (StagePort.billsV hh _).2.meas)).1
   rw [funext (fun v=> StagePort.fiscal hh hb v)]; exact hg'.buds _ ((hg x).const_mul _) zero_le_one (MeasureTheory.integral_const_mul ..).le (Eventually.of_forall (hF x hx))
lemma riverLog (x:(D).X)(hx:‖x‖<1)(h:0<p.push x)(hp:Brush q K 1 Real.log 1) : Brush q (clump q Z K) 1 (fun y=> Real.log (p.push y)-Real.log (p.push x)) x := by
   have hx:= river_b hh he hb hz ht hx' x hx; let A:= p.push; let f y:=(A x)⁻¹*A y; have hv:f x=1:=inv_mul_cancel₀ h.ne'; have he': 0< (A x)⁻¹:= inv_pos.mpr h; have hh:= hx.smul (A x)⁻¹; erw [Real.norm_of_nonneg he'.le,mul_left_comm,inv_mul_cancel₀ h.ne',mul_one] at hh; apply (Lantern.composite (f:=f) hh (show Brush q K 1 Real.log (f x) from hv ▸ hp)).shimmy;
   filter_upwards [hx.smooth.continuousAt.eventually (lt_mem_nhds h)] with y hy; change _=Real.log (f y); unfold f; rw [ Real.log_mul he'.ne' hy.ne', Real.log_inv]; unfold A; ring -- syntax
end global
namespace Travel
open Loom.Patch
variable (p:Travel N Q Φ)(hk:2≤k)(hn:k≤n)(hG:G.Simple)(hp:LocalRatio P)(hd:0<d)
local notation "V" => (summitK Φ (d/2))
local notation "f" => (StagePort.flag ∘ Φ)
local notation "u" => (Dew.β ∘ StagePort.dew ∘ Φ)
local notation "P₀" => (Frame.Bank (fun i=> (Φ i).dew.X) (fun _=>1))
local notation "X₁" => Frame.Port (fun i=> (Φ i).dew.X) (fun _=>1)
include p hk
lemma natural_q (k:ℕ)(a:ℝ){f' : ℕ→ℝ}(h:N.Rush d f')(hd : 0≤d) : let L i:= clump k (f' i) a; N.Rush (d*k) L:= by
   unfold clump; simp_rw [mul_one]; exact ((((Meter.Rush.settle _).mono hd).blend (((Meter.Rush.settle _).mono hd).blend h)|>.powers _).multiplier _); -- implicit p.hk.T
lemma tithes : let K:=((q:ℝ)^2); N.Funds (fun i b=>let A:= Φ i; ∀ x:A.dew.X, ‖x‖<1 → 0<A.push x→ Brush q b 1 (fun y=>Real.log (A.push y)-Real.log (A.push x)) x) K:= by
    let n:=q; intro C₁; obtain ⟨R,hR⟩ := paint_supply G q; obtain ⟨C,hC,h⟩:= Brush.compact («f»:=Real.exp) (k:=q) (s:=({0}:Set ℝ)) (isCompact_singleton) fun i _=> Real.contDiff_exp.contDiffAt; obtain ⟨d,hd,hD⟩:= Brush.compact («f»:=Real.log) (k:=q) (s:=({1}:Set ℝ)) (isCompact_singleton) fun i h=> Real.contDiffAt_log.mpr ((Set.mem_singleton_iff.mp h) ▸ one_ne_zero);
    let D:= StagePort.dew ∘ Φ; let a(i:ℕ):= (Φ i).taxi * (Fintype.card Axis:ℝ); let s (i:ℕ):= prime G U.bind q R C (D i).β (a i); have hp :N.Rush (q:ℝ) s := by
       let t:= fun i=> (|(D i).β| * Token.sizeN G U.bind q (a i) R); have ht :N.Rush 1 t:= ((absolute (volume_count p.dawn p.scale p.plaza p.ferry|>.2.1)).times (((p.scale.bind ((Fintype.card Axis):ℝ)).multiplier U.bind.penalty).bind _) (add_zero _)); let u':= fun i=> t i+t i; have hU:= ht.blend ht; convert natural_q p hk q C hU zero_le_one using 1; rw [one_mul]; rfl
    let K i:= clump q (s i) d; have hK : N.Rush C₁ K:= by unfold C₁; rw [sq]; exact natural_q p hk q _ hp (Nat.cast_nonneg _)
    obtain ⟨d',a',j,_,_,H⟩:= p.ship; refine ⟨_, absolute hK,?_⟩; filter_upwards [H,p.quake_model hk] with i hi hx; refine ⟨abs_nonneg _, ?_⟩;  
    intro S x hh hp; let P':=Φ i; have he : (Fintype.card (Bond (D i).c):ℝ)≤ a i := by rw [Fintype.card_prod]; push_cast; apply mul_le_mul_of_nonneg_right (show (Fintype.card (Site (D i).c):ℝ)≤_ from hi.2.truePE.stitches.primary) (Nat.cast_nonneg _)
    exact (riverLog (p:=Φ i) hi.2 he hx hR (h _ (Set.mem_singleton _)) ((Token.primeN (G:=G) U.bind (n:=q) hi.2.truePE.intake.positive le_rfl hC.le hR.1.le ((Nat.cast_nonneg _).trans he)).1) x hh hp (hD _ (Set.mem_singleton _))).climb (le_abs_self _) le_rfl
end Travel
end Provision
end YM.Contacts.Junction
