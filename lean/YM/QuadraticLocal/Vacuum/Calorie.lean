import YM.QuadraticLocal.Vacuum.Earn
/-!
# Return the tilted E cap and pay with this input budget

Post-block estimate on the difference lines of the vacuum log before final reset.
At δ=0 an arbitrary large multiplier is permissible; for δ>0 we mean the
constant `serving/δ` on every E index outside the model support. Activation works
pointwise at any tilted `δ` (not at slightly shrunk powers selected subsequently).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.High
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration PhysicalNext Repeat Height Time Supply Input Testing
open ConnectedActivityE6.Blaze Blaze.March Captain PriceCompiler Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {Q : YM.ConnectedActivityE6.Target G P} {μ a:ℝ}
local notation "Z" => betaF
open YM.AllOrder.Burn YM.AllOrder.Carillon.Cap
-- unit for `E` sale. fixed fraction in exponent between actual cap and log grant
abbrev attenuation (x:ℝ):= x ^ (-(1/80):ℝ)
def serving (x:ℝ):= x ^ (-(9/8:ℝ)+1/80)
lemma serving_pos (x:ℝ)(hx:0<x):0 < serving x:= Real.rpow_pos_of_pos hx _
lemma old_control (G:Gauge)(L:Side): ∀ᶠ x:ℝ in atTop, let t:=Z G x L; silver t + serving t ≤ (Real.sqrt t)⁻¹ ^ (11/5:ℝ):= by
 have hv: Rate G L (-(9/8:ℝ)+1/80) (fun x=> silver (Z G x L)+serving (Z G x L)) := (((Rate.power (G:=G) (L:=L) (a:=-(7/5:ℝ))).weaken (by norm_num)).add Rate.power ) -- cast?
 filter_upwards [hv _ (by norm_num : (-(9/8:ℝ)+1/80)< -(11/10:ℝ)),Delay.shift_pos G L] with x hh hs; refine (le_abs_self _).trans (hh.trans (le_of_eq ?_)); rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs.le, ← Real.rpow_mul hs.le]; exact congr_arg ((Z G x L)^·) (by norm_num : -(11/10:ℝ) = -(1/2:ℝ)*(11/5:ℝ))
-- native high cost in the usual currency.
lemma pen_eq (G:Gauge)(k:ℕ)(L:Side)(x:ℝ)(hx:0 < Z G x L):pen G L k x 0=(grow G L x^alt k)⁻¹:=by
 unfold pen Burn.credit grow; rw [← Real.rpow_mul_natCast hx.le, ← Real.rpow_neg hx.le]; apply congr_arg; push_cast; ring
lemma aroma (G:Gauge)(k:ℕ)(L:Side)(x:ℝ)(hx:1≤Z G x L) {δ:ℝ} (h:0≤δ) (hh:δ ≤ serving (Z G x L)) : ∃ (w:ℝ), 1≤w∧ w*δ ≤ serving (Z G x L) ∧
     (grow G L x ^ alt k)⁻¹+(grow G L x ^ 3*w)⁻¹ ≤ 2*pen G L k x 0 + attenuation (Z G x L) * δ:= by
 let z:= Z G x L; have he:= zero_lt_one.trans_le hx; let φ:= serving z; let D:= grow G L x; let q:= attenuation z; let η:= pen G L k x 0
 have hs:D≥1:= Real.one_le_rpow hx (by norm_num); have hf:0<φ:= serving_pos _ he; have hz:= zero_lt_one.trans_le hs; have ht:0< D^alt k:= pow_pos hz _
 rw [pen_eq G k L x he]
 rcases eq_or_lt_of_le h with rfl|h
 · refine ⟨D^alt k, one_le_pow₀ hs, ?_, ?_⟩; · rw [mul_zero]; exact hf.le
   change (D^_)⁻¹+_≤2*_+_; rw [mul_zero,add_zero,two_mul]; apply add_le_add le_rfl (inv_anti₀ ht (le_mul_of_one_le_left ht.le (one_le_pow₀ hs)))
 refine ⟨φ/δ,(one_le_div h).mpr hh, (div_mul_cancel₀ _ h.ne').le,?_⟩
 have hp:= le_add_of_nonneg_right (b:=(D^alt k)⁻¹) (a:=(D^alt k)⁻¹) (inv_nonneg.mpr ht.le)
 rw [two_mul]; refine add_le_add hp (le_of_eq ?_)
 have hφ: D^3 * φ = z ^ (1/80:ℝ):= by
   unfold D φ serving grow; rw [← Real.rpow_mul_natCast he.le,← Real.rpow_add he]; norm_num; rfl
 have heq:q=(z^(1/80:ℝ))⁻¹:= Real.rpow_neg he.le _
 change (D^3*(φ/δ))⁻¹=q*δ; rw [← mul_div_assoc,hφ,heq]; rw [inv_div, div_eq_mul_inv,mul_comm]; -- assoc orientation
-- post L pack all. residues and support cap. Reserve any additional k.C.
set_option quotPrecheck false
abbrev caloric (G:Gauge)(x:ℝ)(L:Side)(k:ℕ)(δ:ℝ):=2*pen G L k x 0 + attenuation (Z G x L) * δ
structure Meets (Q : YM.ConnectedActivityE6.Target G P) (π : ℕ) (L:Side) (X:Q.Expense) (W μ c : ℝ) (o:Target.Order G W) (j n:ℕ) (χ:Chi) (x:ℝ):Prop where
    renew : ∀ (c' f : Side) (S:StepData c' f) (T:Tube G S), Works P L x S T → Stamp T → ∀ (R:RG.Rep G f) (H:Cash W x μ L Q o c T R), ∀ (M:Set ℕ)(δ:ℝ), Candor R.p R.activities M (silver (Z G x L)) δ → δ ≤ serving (Z G x L) →
      ∃ (C' d v t A b r B q : ℝ) (k : ℕ) (N:Captain H j C' d v t A b r B q k χ), Ac.Hit (Captain.reachability (H:=H)) (radiusB x) (fun z=>if tiredT H (Burn.typeT M π) (Burn.alt π) z then N.markΦ z n else 0) X.earn ( caloric G x L π δ )
    eligible : serving ( Z G x L ) ≤ incomingE G L x
lemma allowsMultiplier (Q : YM.ConnectedActivityE6.Target G P) (π : ℕ) : ∃ m:ℕ, ∀ L:Side,m≤L.val → ∀ (X:Q.Expense) (W μ c : ℝ) (o:Target.Order G W),
    0<W → 0<μ → Q.rate < -(3/8:ℝ) → ∀ j n χ, ∀ᶠ x:ℝ in atTop, Meets Q π L X W μ c o j n χ x:=by
 obtain ⟨m,H⟩:=burnsWith Q π; refine ⟨m,fun L hm X W μ c o hw hμ hR j n χ=> ?_⟩
 filter_upwards [H L hm X W μ c o hw hμ hR j n χ, old_control G L, (YM.Work.E09.betaF_growth G L).eventually_ge_atTop 1] with x hx h hp
 have he:= zero_lt_one.trans_le hp; have hΞ:=h; constructor
 · intro c f S T hS hT R H M δ hδ hL
   obtain ⟨w,hw,hh,hr⟩:= aroma G π L x hp (show 0≤δ from budget_nonneg (hδ.sale.choose_spec.2 0).2) hL
   obtain ⟨a,b,c,d,e,f,r,A,K,k,N,hC,hq⟩:=hx c f S T hS hT R H (fund M w hw) (steward w hw H.laws.intake hδ (by rw [H.laws.data.funds.length_eq]; exact (add_le_add le_rfl hh).trans h)) -- collision
   refine ⟨_,_,_,_,_,_,_,_,_,k,N,fun y=>budget_loosen (hq w M hw ?_ y) hr⟩; intro i hi; change w ≤ if _ then _ else _; rw [if_neg hi]
 exact (le_add_of_nonneg_left (silver_pos _ he).le).trans h
end YM.AllOrder.High
