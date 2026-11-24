import YM.OPE.Compatible.Ingle.Pax
/-! # determinant workload. All limits in one local selection h-branch. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Spells
open Function Filter Set Lattice Wilson RG MeasureTheory Matrix
open Pill Asymptotics
open scoped Topology BigOperators Classical ContDiff
variable {I X Y:Type*}{β β' T x g y:I→ℝ}{f:Filter I}{s:ℝ}
def Wickρ (β:I→ℝ)(f:Filter I)[Norm X](x:I→X):= Wick (Counters β) f x -- log speech
abbrev GripU (β:I→ℝ)(i:I):= Sparks β i * Real.exp ((Real.log (Counters β i))^2)
lemma Bram (h:Tendsto β f atTop) : RateIs f (Counters β) (GripU β) (-1/2):=by
      have hh:RateIs f (Counters β) (Sparks β) (-1/2):=by simpa only [mul_one] using! (canq h).rpow (-1/2)
      have hv:Tendsto (fun i=> Real.log (Counters β i)^2 / Counters β i) f (𝓝 0):=by
           have h := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (show (0:ℝ)< (1:ℝ) from zero_lt_one)).tendsto_div_nhds_zero.comp (carth h)
           convert! h using 1; funext i; simp
      simpa only [add_zero] using hh.mul (RateIs.exp' hv) -- simplification
lemma Whistle (h:Tendsto β f atTop)(hs: Pill.Shell β β' f): Wickρ β f (fun i=> Sparks β' i / GripU β i):=by
      obtain ⟨c,C,hc,hC,H⟩:=hs; let g:=(-1/2:ℝ); let v(i):=(β' i)^g/(β i)^g; have he: Receipt β f v:= Score.bound ((c:ℝ)^g) (carth h) (by
           filter_upwards [H,h.eventually_gt_atTop 0] with i h hi
           have hx:0<c*β i:= mul_pos hc hi; have hz:0<β' i:=hx.trans_le h.1; have ht:0<(β i)^g:=Real.rpow_pos_of_pos hi _; unfold v; rw[Real.norm_of_nonneg (by positivity),div_le_iff₀ ht, ← Real.mul_rpow hc.le hi.le]; exact Real.rpow_le_rpow_of_nonpos hx h.1 (show g ≤ 0 from by unfold g;norm_num))
      obtain ⟨a,hv⟩:=he; intro k; let Ztz (i):=Real.log (Counters β i); have hu:= (Wick_bill (carth h) (δ:=1) zero_lt_one (k-a)); refine (RateLE.congr (show RateLE f (Counters (Counters β)) (fun i=>v i*Burl 1 (Counters (Counters β)) i) k from by simpa only [add_sub_cancel,add_sub_cancel_left] using hv.mul hu) ?_); filter_upwards with i; unfold Burl GripU v; change ((_ :ℝ)/_) * Real.exp (-1* (Ztz i)^2)=_ / (_ * Real.exp ((Ztz i)^2)); rw [neg_one_mul, Real.exp_neg]; ring -- edit
lemma Wickρ.zero (p:Wickρ β f x)(h:Tendsto β f atTop): Tendsto x f (𝓝 0):=(p (-1)).tends (by norm_num) (carth (carth h))
lemma Wickρ.norm (p:Wickρ β f x):Wickρ β f (fun i=>‖x i‖):=fun a=> (p a).norm
lemma Wickρ.dot (h:Receipt β f x)(hp:Wickρ β f y):Wickρ β f (fun i=>x i*y i):=by
    obtain ⟨a,h⟩:=h; intro j; exact ((show a+(j-a)=j from by ring) ▸ RateLE.mul h (hp (j-a)))
lemma Wickρ.plus (h:Tendsto β f atTop)(hx:Wickρ β f x)(hg:Wickρ β f g): Wickρ β f (x+g):=fun a=> (hx a).add (hg a) (carth (carth h))
lemma downρ (h:Tendsto β f atTop)(hp:Wax β f x s)(hs:s<0):Wickρ β f x:=by
    have hv: Tendsto (fun i=> Real.log (Counters β i)/Counters β i) f (𝓝 0):=Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp (carth h)
    let z:= Counters (Counters β); intro k u hU; obtain ⟨t,ht,ht'⟩:= exists_between hs; have hz:Tendsto (fun i=>u*(z i /Counters β i)) f (𝓝 0):=by simpa only [mul_zero]  using! hv.const_mul u
    filter_upwards [(carth h).eventually_gt_atTop 0,hz.eventually (le_mem_nhds ht'),hp t ht] with i hi hg hk; have he:u*(z i / Counters β i)≥t:=hg; rw [← mul_div_assoc] at he; exact hk.trans (Real.exp_monotone ((le_div_iff₀ hi).mp he))
structure TuneUp (β:I→ℝ)(f:Filter I)(U:I→BudgetPoint) (ζ:I→ℝ) :Prop where
     opens : ∀ᶠ i in f,0 < ζ i
     Clock : Tendsto β f atTop
     fair : ∀ᶠ i in f,(U i).threshold=GripU β i
     heft : ∃ β', Shell β β' f ∧ ζ=ᶠ[f] Sparks β'
local notation "PΛ"=> Wax β f
section
variable {U:I→BudgetPoint} {p:I→ℝ} (h:TuneUp β f U p)
include h
lemma worthP : RateIs f (Counters β) p (-1/2):=by obtain ⟨v,hv,hp⟩:=h.heft; exact (surely h.Clock hv).congr hp.symm
lemma boltP : RateIs f (Counters β) (fun i=>(U i).threshold) (-1/2):= (Bram h.Clock).congr (EventuallyEq.symm h.fair)
lemma CalmP : RateIs f (Counters β) (fun i=>θh (p i) (U i)) 0:=by
     simpa only [sub_self,← div_eq_mul_inv] using! (worthP h).div (boltP h)
lemma πlag : Wickρ β f (fun i=> θh (p i) (U i)):=by obtain ⟨v,hv,H⟩:=h.heft; intro a; refine (Whistle h.Clock hv a).congr ?_; filter_upwards [h.fair,H] with i hi ha; change _ = p i*(U i).threshold⁻¹; rw[hi,div_eq_mul_inv,show p i= Sparks v i from ha]
lemma lagG : Wickρ β f (fun i=>(U i).threshold):= downρ h.Clock ((boltP h).pays (carth h.Clock)) (by norm_num)
end
end YM.OPE.Spells
