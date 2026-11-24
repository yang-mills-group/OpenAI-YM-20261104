import YM.RGLocalTaylor.Laminate.Switch

/-!
# Same-play data in the roster-H keeper. Charges BEFORE summing labels or
recharging torus/witness prices, after deciding post-address & actual `ρ`
can read `Axle.cashes`.

Based on our Read.Germ and the underlying Products of the Abe engine.
Keep budgets ON every assignment (including no current Ticket). Actual
nilpotent basis is priced later; reserve exponent sent all steps. 
-/
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


open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt
open Blaze.March Captain
namespace Laminate
open RG01.Survive Mayer Trees Merge Palette Gas Ursell Marker
variable {ι: Type} [Fintype ι] (M':ι→Leaf R) (rA:ι→ℝ) (N : Captain H j C' d v Y A b r B q n χ)
    {p:H.ThinP}(w:H.fragrances)
structure Axle (M j:ℕ) (H : Cash W s μ L Q o C T R) (v:ℝ) (χ:Chi) (u:H.ThinP→ VoucherL M' S M →ℝ) (g: H.ThinP→ℝ) (ρ :ℝ): Prop where
  pos i p : 0 ≤ u i p
  strong : 1 ≤ ρ
  rent i : ∑ p, u i p * ρ ^ (p.2.val:ℕ) ≤ g i
  cost i U p (_:Healthy (Pressure.temp s) (H.smallAt i) U): Ore U (fun V=> mint M' rA (χ:=χ) i V p) v (u i p) j

variable {M:ℕ} {ρ e uJ α a w' η θ:ℝ} (hP:Plot M' H rA)
namespace Airs
abbrev aP (i:H.ThinP) (u:VoucherL M' S M):= packPrice rA u.1.val*((ρ^u.2.val)⁻¹*invoice (team M' u.1) i.val N.conduit θ ρ α uJ e M l)
abbrev gP (i:H.ThinP) := (↑(M+2:ℕ):ℝ)*launchFoot M' rA N.conduit i.val θ ρ α uJ e M l

variable (h: Airs N l M e uJ θ ρ α a w' η)
include h hP
lemma grants : Axle M' rA M j H v χ (aP M' rA N (e:=e) (uJ:=uJ) (θ:=θ) (ρ:=ρ) (α:=α) (l:=l)) (gP M' rA N (e:=e) (uJ:=uJ) (θ:=θ) (ρ:=ρ) (α:=α) (l:=l) (M:=M)) ρ:= by
  have hc i:0 ≤ packPrice rA i:= prod_nonneg fun i _=> hP.live i; have hg:=zero_lt_one.trans_le h.scale
  refine ⟨fun i p=>mul_nonneg (hc _) (mul_nonneg (by positivity) (h.plus ..)), h.scale,fun i=> ?_,fun i V u hx E _ _ _ U t hv ht=>?_⟩
  · let g p:=packPrice rA (p:Tickets (Palette.sign M' S)).val*invoice (team M' p) i.val N.conduit θ ρ α uJ e M l
    let f p := aP M' rA N (M:=M) (e:=e) (uJ:=uJ) (α:=α) (θ:=θ) (ρ:=ρ) (l:=l) i p
    have he(u: VoucherL M' S M): f u * ρ^u.snd.val=g u.1:=by unfold g f aP; field_simp
    change ∑ u:VoucherL M' S M,f u * ρ^u.2.val≤ _; simp_rw [he]; rw [Fintype.sum_prod_type]; simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fin,← mul_sum]; exact le_rfl
  simpa only [Real.norm_of_nonneg (hc u.fst.val)] using! ((h.tells (team M' u.1) i u.2 V hx E U t hv ht).smul (packPrice rA u.fst.val)) -- check
end Airs
namespace Axle
variable {M' rA} {b' : BudgetPoint} (x:Site c) (hx : x∈reachability w)
    {u : H.ThinP → VoucherL M' S M→ℝ}{g:H.ThinP→ℝ}(he:Axle M' rA M j H v χ u g ρ)
    (t:Flight M' w M)

abbrev dmeter (s:ℝ) (P:BudgetPoint) (X:Support c) : ℝ:= shiftG s*(1+ ↑(coverNumber P.B X))
abbrev radiusP (b' : BudgetPoint) (w:H.fragrances):=dmeter s b' (reachability w)^(j*k)
-- Receipts per individual labels
abbrev meters (j:ℕ) (u : H.ThinP →VoucherL M' S M→ℝ) (t:Flight M' w M):= ‖tax w‖*Products.atPrices (fun i=>u (w.2 i)) j t
abbrev brands (b' : BudgetPoint) (u : H.ThinP →VoucherL M' S M→ℝ) (t:Flight M' w M):= radiusP (j:=j) (k:=k) b' w*meters w j u t
set_option quotPrecheck false
local notation "t'" => columnKey M' rA w (χ:=χ)
local notation "Z" => reachability w
lemma dmeter_pos (s:ℝ) (P:BudgetPoint) (X:Support c):1 ≤ dmeter s P X:= by
  unfold dmeter shiftG
  nlinarith [Nat.cast_nonneg (α:=ℝ) (coverNumber P.B X), Nat.cast_nonneg (α:=ℝ) (radiusB s)]
include he
lemma meter_pos : 0 ≤ meters w j u t:= mul_nonneg (norm_nonneg _) (prod_nonneg (fun i _=> mul_nonneg (by positivity) (he.pos ..)))
lemma brand_pos (b' : BudgetPoint) (k:ℕ) : 0 ≤ brands (j:=j) (k:=k) w b' u t:= mul_nonneg (pow_nonneg (zero_le_one.trans (dmeter_pos ..)) _) (meter_pos w he t)
lemma located (U:Config G c) (hU: Healthy (Pressure.temp s) (reachability w) U):
    Ore U (t' t) v (meters w j u t) j:= by
  intro E _ _ _ V m ht hh
  let f (i:Option (Fin w.fst)) (t:VoucherL M' S M) (k:E):= mint M' rA (w.2 i) (χ:=χ) (V k) t
  have hf i : Healthy (Pressure.temp s) (H.smallAt (w.2 i)) U := Finset.disjoint_of_subset_left (subset_biUnion_of_mem (H.smallAt ∘ w.2) (mem_univ i)) hU
  exact (Products.earns f (fun i=>u (w.2 i)) (fun i t=> he.cost _ _ t (hf i) E _ _ ht hh) t).smul (tax w)
variable (ht : b'.threshold=Pressure.temp s) (hj : b'.order≤j) (hp:b'.power≤k) (hB:b'.B=radiusB s)
  (q:ℝ) (hq:0≤q) (hS:Sailor G b'.threshold q j) (hv : j*q≤v) (hr:0<v)

include ht hj hp hB hq hx hS hv hr
lemma atSizes : b'.Regular (reachability w) (t' t) ∧ b'.supBounds x Z (t' t) (brands (j:=j) (k:=k) w b' u t):= by
  have hz U (H : Healthy b'.threshold Z U):= located w he t U (ht ▸ H)
  have hL i: H.smallAt (w.2 i) ⊆ reachability w:= subset_biUnion_of_mem (H.smallAt ∘ w.2) (mem_univ i)
  have hl i:= rector_shape χ H M' rA (w.2 i) (t i)
  let f:= t' t
  have ha: LocalOn Z f := fun U V hu => congr_arg (tax w * ·) (prod_congr rfl fun i _=> ((hl i).2.2 U V (agrees_mono hu (Finset.coe_subset.mpr (hL i)))))
  have hh U (hU: Healthy b'.threshold Z U) : ContDiffAt ℝ (↑b'.order) (f ∘ increment U) 0:= (charted (hz U hU) hr).of_le (by exact_mod_cast hj)
  refine ⟨⟨ha,measurable_const.mul (Finset.measurable_fun_prod _ (fun i _=> (hl i).2.1)),?_,hh,fun U h a ℓ e=> Next.Foundations.left_has a e (hh U h)⟩,⟨brand_pos w he t b' k,fun U h ℓ he' hD=>?_⟩⟩
  · intro k U; unfold columnKey; exact congr_arg _ (prod_congr rfl fun i _=> (hl i).1 k U)
  let d:=dmeter s b' Z; have hF:1 ≤ d:=dmeter_pos ..
  have h0:∀y∈Z,1+(separation y x :ℝ)≤d:= by
    intro y hy
    have hf := Corona.extent Z b'.B hy hx
    unfold d dmeter shiftG; rw [← hB]
    exact le_trans (show _ ≤ 1+(((coverNumber b'.B Z)*(4*b'.B+2) +2*b'.B:ℕ):ℝ) by exact add_le_add_right (by exact_mod_cast hf) _) (by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) (coverNumber b'.B Z),Nat.cast_nonneg (α:=ℝ) b'.B])
  apply (costsD (p:=b') ha hS hq x _ hv (hz U h) h0 hF ℓ (he'.trans hj) hD).trans
  unfold brands radiusP; rw [Nat.mul_comm b'.power]; apply mul_le_mul_of_nonneg_right _ (meter_pos w he t); gcongr
omit ht hj hp hB hq hx hS hv hr in
lemma nodeCosts (J : Finset (Flight M' w M)) (p:ℕ) (hp:∀ t∈J,p≤ salary M' w t):
    ∑ t∈J, meters w j u t ≤ (ρ^p)⁻¹ * clusters H.seam (fun i=>2^j*g i) w.snd := by -- missing 2^j
  let g' i:= (2^j:ℝ)*g i; let c:=‖tax w‖; have hc:0≤c:=norm_nonneg _; have hr:0<ρ:=zero_lt_one.trans_le he.strong
  have he':=Products.booked (fun i=>u (w.2 i)) (fun i=>g (w.2 i)) ρ (fun _ p=>p.snd.val) j hr.le (fun i t=> he.pos (w.2 i) t) (fun i=> he.rent (w.2 i))
  have hu : clusters H.seam g' w.2=c*(∏ i, g' (w.2 i)):= by unfold c tax Ursell.clusters; rw [Real.norm_eq_abs,abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (w.1+1).factorial)]; ring
  rw [mul_comm (_⁻¹),←div_eq_mul_inv,le_div_iff₀ (pow_pos hr _),hu, Finset.sum_mul]
  refine le_trans (sum_le_sum (g:= fun i=> meters w j u i * ρ^salary M' w i) (s:=J) fun i hi=> mul_le_mul_of_nonneg_left (pow_le_pow_right₀ he.strong (hp i hi)) (meter_pos w he i)) (le_trans (Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>?_)) ?_)
  · exact mul_nonneg (meter_pos w he i) (pow_nonneg hr.le _)
  convert! mul_le_mul_of_nonneg_left he' hc using 1; rw [mul_sum]; exact sum_congr (by congr!) fun i _=> mul_assoc ..

variable {p:ℕ} (keep : H.fragrances→ℕ→Prop)
    (h:∀ (z:H.fragrances) (d:ℕ), keep z d → p ≤ d)
local notation "w!" => LeafReady.allowance b' w j k g
local notation "u'" => brands (j:=j) (k:=k) w b' u
omit ht hj hp hB hq hx hS hv hr
include h
lemma rents : (∑ t∈ univ.filter (passenger M' w keep), u' t) ≤ (ρ^p)⁻¹ * LeafReady.allowance b' w j k g:=by
  unfold brands; rw [← mul_sum]; apply le_trans (mul_le_mul_of_nonneg_left (nodeCosts w he _ p (fun i hi=>h _ _ (mem_filter.mp hi).2.2)) (pow_nonneg (zero_le_one.trans (dmeter_pos ..)) _)); unfold dmeter LeafReady.allowance; exact (mul_left_comm ..).le
end Axle
end Laminate
end YM.RGLocalTaylor
