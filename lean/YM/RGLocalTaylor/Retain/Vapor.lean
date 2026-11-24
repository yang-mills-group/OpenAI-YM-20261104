import YM.RGLocalTaylor.Retain.Music
/-! # Re-expression support price on all fields, payment already for mark forecasts in Section.Motion
Uses two real rays of approach inside the SECOND log Spine to estimate every
Meter. Reader price includes ORBIT pulls from prior Bouquet/Brass, printed
matter. Allow Outdoors when not Healthy after subtract.Anonymous letter budget
requires Fintype. No measure truncation to earn either beam. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt Blaze.March
namespace Retain
open RG01.Survive Mayer goodK Trees Merge Palette Fort Laminate
namespace Mill
open Captain Ursell Gas
variable {m M :ℕ} {p':Molecule S}{e α β γ δ κ r' d' ρ:ℝ}
   {N : Captain H j C' d v Y A b r B q n χ}
   {ι:Type}[Fintype ι]
   {boxes coins:ι→ℕ}
   {f₁:H.ThinP→ι→ℝ}{g' : H.ThinP→ℝ}{Θ Θ': Scans ι H} (h : Verse H boxes coins Θ ρ κ v j f₁ g') (ht: Cooperates H boxes coins Θ Θ' ρ κ v j f₁ g' γ)
   (z:H.fragrances)(p:BudgetPoint)(u:lot z ι)
local notation "c'" => reachability (H:=H)
local notation "e'" => Laminate.Axle.radiusP (j:=j) (k:=k) p z
set_option quotPrecheck false
local notation "f₀" => Mill.printed Θ z
local notation "f'" => Mill.printed Θ' z
local notation "u'" => salary f₁ j z
local notation "U'" => H.smallAt
local notation "E!" => (ρ^(dots boxes z u) * κ^(dots coins z u))
local notation "dK" => LeafReady.allowance p z j k g'

include h
lemma ratesOn : ∑ u:lot z ι, salary f₁ j z u * (ρ^dots boxes z u * κ^dots coins z u) ≤ Ursell.clusters H.seam (fun i=>2^j*g' i) z.2 := by
   let Q i:=f₁ (z.2 i) ∘ id; let h' (i:ι):= ρ^boxes i * κ^coins i; let w i j:=(2:ℝ)*Q i j*h' j; let x:=‖Laminate.tax z‖; let C:ℝ:=(2:ℝ)^j
   -- scalar welfare per `BOOK`; clusters relation
   have ht:0≤ x:=norm_nonneg _; have hC:0≤C:=by unfold C; positivity
   have hv(u:lot z ι): u' u * (ρ^dots boxes z u * κ^dots coins z u)= x*∏ i,C*w i (u i):=by
      unfold salary meet_bill dots; rw [← prod_pow_eq_pow_sum,← prod_pow_eq_pow_sum,mul_assoc,← prod_mul_distrib,← prod_mul_distrib]; apply congr_arg (x*·); apply prod_congr rfl (fun i _=> mul_assoc C _ _)
   have hK:0≤ ρ:=zero_le_one.trans h.heft; have hβ:0≤κ:=zero_le_one.trans h.pays
   have hu i u:0≤w i u:=by unfold w; exact mul_nonneg (mul_nonneg zero_le_two (h.live _ _)) (mul_nonneg (pow_nonneg hK _) (pow_nonneg hβ _))
   have ht i: ∑ j,w i j≤ g' (z.2 i):=h.PriceBox _
   simp_rw [hv,← mul_sum]; rw [← Fintype.prod_sum (f:=fun i u=> C*w i u)]
   rw [show Ursell.clusters H.seam (fun i=>2^j*g' i) z.2=x* ∏ i,C*g' (z.2 i) from ?_]
   · simp_rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (prod_le_prod (fun i _=>mul_nonneg hC (sum_nonneg (fun j _=>hu i j))) (fun i _=> mul_le_mul_of_nonneg_left (ht i) hC)) (norm_nonneg _)
   unfold x Laminate.tax Ursell.clusters C; rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) _)]; ring
abbrev PriceA (ρ κ:ℝ)(n k:ℕ) := (ρ^n*κ^k)⁻¹

variable {r₁ r₂:ℕ} {w'S : Finset (lot z ι)} (hp:∀ u∈w'S,r₁≤dots boxes z u ∧ r₂ ≤ dots coins z u)
include hp
lemma countA : ∑ i∈w'S, salary f₁ j z i ≤ PriceA ρ κ r₁ r₂ * Ursell.clusters H.seam (fun i=>2^j*g' i) z.2:=by
   let e:=ρ^r₁*κ^r₂; have hP:1≤ρ:=h.heft; have hQ:1≤κ:=h.pays;have hE:0< e:=by unfold e; positivity
   unfold PriceA; rw [inv_mul_eq_div, le_div_iff₀ hE,Finset.sum_mul]
   have hy(i) :=salary_pos h z i;let f i:= κ^dots coins z i; let g i:= ρ^dots boxes z i
   refine (sum_le_sum (g:=fun i=>u' i*(g i*f i)) (fun i hi=>?_)).trans ((sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> by unfold f g; exact mul_nonneg (hy i) (by positivity))).trans (ratesOn h z))
   apply mul_le_mul_of_nonneg_left _ (hy i); unfold f g; exact mul_le_mul (pow_le_pow_right₀ hP (hp i hi).1) (pow_le_pow_right₀ hQ (hp i hi).2) (by positivity) (by positivity)
lemma picture : ∑ t∈w'S, e' * salary f₁ j z t ≤ PriceA ρ κ r₁ r₂ * dK:= by
   rw [← mul_sum]; exact (mul_le_mul_of_nonneg_left (countA h z hp) (pow_nonneg (zero_le_one.trans (Laminate.Axle.dmeter_pos ..)) _)).trans_eq (mul_left_comm ..)
omit hp

variable (h' : p.threshold=Pressure.temp s)(hj:p.order≤j)(hk:p.power≤k)(hl:p.B=radiusB s)
   (q:ℝ)(hq:0≤q)(hS:Sailor G p.threshold q j)(hv:j*q≤v)(hy:0<v)
include hj hk h' hl hq hS hv hy
omit h
variable {fT:Config G c → ℝ}
lemma regularTop {e:ℝ} (hf: LocalOn (reachability z) fT) (hm:Measurable fT)(hu:GaugeInvariant fT)
   (hO:∀ U:Config G c,Healthy (Pressure.temp s) (reachability z) U → Ore U fT v e j)(he:0≤e) : p.Regular (reachability z) fT ∧ ∀ x ∈ reachability z,p.supBounds x (reachability z) fT (e'*e):=by
   let Z:=c' z; have hT U (h:Healthy p.threshold Z U):= hO U (h' ▸ h)
   have hh U (he:Healthy p.threshold Z U):ContDiffAt ℝ (↑p.order) (fT ∘ increment U) 0 := (charted (hT U he) hy).of_le (by exact_mod_cast hj)
   let d:=Laminate.Axle.dmeter s p Z; have hd:1≤d:=Laminate.Axle.dmeter_pos ..
   refine ⟨⟨hf,hm,hu,hh,fun U h a ℓ e=> Next.Foundations.left_has a e (hh U h)⟩,fun x hx=>⟨mul_nonneg (pow_nonneg (zero_le_one.trans hd) _) he,fun U h ℓ hx' hD=>?_⟩⟩
   have h0:∀y∈Z,1+(separation y x:ℝ)≤d:=by
      intro y hy; have hv:= Corona.extent _ p.B hy hx; unfold d Laminate.Axle.dmeter shiftG;rw [← hl]; exact le_trans (show _≤1+(((coverNumber p.B Z*(4*p.B+2)+2*p.B:ℕ):ℝ)) by exact add_le_add_right (by exact_mod_cast hv) _) (by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) p.B,Nat.cast_nonneg (α:=ℝ) (coverNumber p.B Z)])
   apply (costsD hf hS hq x _ hv (hT U h) h0 hd _ (hx'.trans hj) hD).trans
   unfold Laminate.Axle.radiusP; rw [Nat.mul_comm p.power]; apply mul_le_mul_of_nonneg_right _ he; gcongr
include h
lemma salaryBill : p.Regular (reachability z) (f₀ u) ∧ ∀ x∈reachability z, p.supBounds x (reachability z) (f₀ u) (e'*u' u):= by
   obtain ⟨ht,hv',hx⟩:=reshaped h z u; exact regularTop z p h' hj hk hl q hq hS hv hy hx hv' ht (fun _=>paid_value h z u) (salary_pos h z u)

omit h
include ht
lemma defectC : p.Regular (reachability z) (Mill.printed Θ z u-Mill.printed Θ' z u) ∧ ∀x∈reachability z,p.supBounds x (reachability z) (f₀ u-f' u) (γ*(e'*u' u)):=by
   obtain ⟨hX,hZ,hx⟩:= reshaped ht.formalP z u; obtain ⟨hu,hB,hb⟩:=reshaped ht.realP z u
   rw [mul_left_comm]; refine regularTop z p h' hj hk hl q hq hS hv hy (fun t w q=> congr_arg₂ (·-·) (hx t w q) (hb t w q)) (hZ.sub hB) (fun t w=> congr_arg₂ (·-·) (hX t w) (hu t w)) (fun _=> meet_error ht z u) (mul_nonneg ht.profit (salary_pos ht.formalP z u))

omit ht hj hk hq hS hv hy h' hl
variable {w:ℝ} (hα:0≤a)(hA: d'≤a) (hδ:0<δ) (he:0≤e) -- delete typo
    (hY:Ready H.smallAt p.B (fun i=>2^j*g' i) (a+δ) α δ w)
local notation "T'" => (collars G δ s j k*(α*(1-w)⁻¹))
include hY hα hA hδ he
-- same coupon across BOTH visits (Read.Register,... etc)
lemma couponBudget : Ac.Hit (reachability (H:=H)) p.B (fun z:H.fragrances=>e*LeafReady.allowance p z j k g') d' (e*T'):=by
   intro x; have hκ:= hY.2.2.2.2.1
   have hz:=Ursell.log_hit_tail _ _ _ H.testS hY (add_nonneg hα hδ.le) 0 x; simp only [pow_zero,mul_one,Nat.zero_le,true_and] at hz
   let t:=collars G δ s j k
   have ht:0≤t:=by unfold t collars shiftG Reserves.polyPrice; positivity
   have hh :=budget_scale he (budget_scale ht hz); have hp:0 ≤ shiftG s:=by unfold shiftG; positivity
   refine budget_mono hh (fun z=>?_) fun z=> ?_
   · split
     next=> exact mul_nonneg (mul_nonneg he (mul_nonneg (pow_nonneg (zero_le_one.trans (Axle.dmeter_pos ..)) _) (clusters_nonneg _ hκ _))) (Real.exp_pos _).le
     exact le_rfl
   split
   next hy=>
     let g:ℝ:=coverNumber p.B (reachability z); let Hq:= clusters H.seam (fun i=>2^j*g' i) z.snd
     have hu':0≤Hq := clusters_nonneg _ hκ _; have he':0≤g:=Nat.cast_nonneg _
     rw [if_pos (show x∈unionOf H.smallAt z.2 from hy)]; change e*((shiftG s*(1+g))^(j*k)*Hq) * Real.exp (d'*g) ≤ e*(t*(Hq*Real.exp ((a+δ)*g)))
     unfold t collars; rw [Nat.mul_comm j k,mul_pow,add_mul a, Real.exp_add]
     have hF := polynomial_cost hδ he' (k*j)
     apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF (pow_nonneg hp _)) hu') he) (Real.exp_pos _).le)
     unfold Reserves.polyPrice
     nlinarith only [mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA he'))
      (show 0≤e*(((shiftG s)^(k*j)*(δ⁻¹^(k*j)* ↑((k*j).factorial) * Real.exp δ*Real.exp (δ*g)))*Hq) by positivity)]
   exact hh.1 z
end Mill
end Retain
end YM.RGLocalTaylor
