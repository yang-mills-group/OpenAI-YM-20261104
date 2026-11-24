import YM.LocalTaylorR2.Marker.Pigtail
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Rising
/-!
 # Price single Mark: post-K
 Uses from Daisy.Clutch.central. Signs untouched, inventory projected only once.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Marker
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Leaf R) (X:Coat T F) (H:Cash W x μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G}

local notation "i₀" => M.turn.badge S
open Port Charge
open Reserves Tender Gas Ursell Trees Mixed
variable {j k n l : ℕ} {v₀ r d A D x' C' ζ η c' y: ℝ} {χ : Chi} (Ξ:Utopia H j v₀ d r C' χ)
open Candle Daisy.Charity
open scoped Classical
variable {b B ρ q:ℝ}{a d a' : H.ThinP→Orders l→ℝ}{σ σ':H.ThinP→ℝ}
variable {k₁ :ℝ} (h:Mind H M χ l v₀ j a a' σ ρ k₁) (z:H.fragrances) (take:H.fragrances→ℕ→Prop)
variable {A : BudgetPoint} {u₀ η:ℝ} (hb:A.B=radiusB x) (hv:A.threshold=Pressure.temp x)(hr:A.order≤j) (hq:0≤q)(ht:Sailor G A.threshold q j) (hm:j*q≤ v₀) (hp:0<v₀)
    (hδ:0<η)(he:Ready H.smallAt (radiusB x) (fun i=>2*(2^j*σ i)) (u₀+η) w η (1/2))
open LeafReady

include h
set_option quotPrecheck false
local notation "zK"=> (clusters H.seam (fun i=> 2*(2^j*σ i)) z.2)
-- uniform regulator price; explicit collar.Note no Candidate.K.
def brushPrice (j:ℕ) (σ:H.ThinP→ℝ) (p u:ℕ)(k₁ ρ:ℝ) (o:Site c):= if speaks M H z then flareC (x:=x) (j:=j) u (locus M H o z)*(k₁*(ρ^p)⁻¹*(clusters H.seam (fun i=> 2*(2^j*σ i)) z.2)) else 0
include hv hr hq ht hm hp
lemma grips (o':Site c)(hy:o'∈ M.crest.image S.ratio.parent)(r:ℕ)(hs:∀ q,take z q→ r≤q): let f := subtensor M H z take χ l; let Z:= locus M H o' z; let u:= brushPrice M H z j σ r A.power k₁ ρ o'
    A.Regular Z f ∧ A.supBounds o' Z f u:=by
    intro f Z u; unfold Z u brushPrice; by_cases hx:speaks M H z
    swap; · unfold f; rw [censored M H z take χ l hx,if_neg hx]; exact ⟨AnalyticBridge.VerifiedReset.reg_const (p:=A) 0,by simpa only [abs_zero] using! (AnalyticBridge.VerifiedReset.sup_const (p:=A) (G:=G) (X:=Z) (o:=o') 0)⟩
    have hy':= seatY M H o' hy z
    unfold locus at hy' ⊢; rw [if_pos hx] at hy'; simp_rw [if_pos hx]; let Z:= H.bookFoot (.inr z)
    have hw:=h.thought.scale; have hΔ:=h.good; have hσ i : 0≤2*(2^j*σ i):=by have hh:=budget M H h i; positivity
    have hb:= mul_nonneg (mul_nonneg hΔ (by positivity : 0≤(ρ^r)⁻¹)) (clusters_nonneg H.seam hσ z.snd)
    obtain ⟨hi,hM,hL,hP⟩:= tensor M H h z take r hs
    have ha V (hl: Healthy A.threshold Z V) : Ore V f v₀ (k₁*(ρ^r)⁻¹*zK) j:= hP V (hv ▸ hl)
    have hh V (ht : Healthy A.threshold Z V) : ContDiffAt ℝ (↑A.order) (f ∘ increment V) 0 := (charted (ha V ht) hp).of_le (Nat.cast_le.mpr hr)
    let z':ℝ:= coverNumber (radiusB x) Z; let t:ℝ:=shiftG x*(1+z')
    have hu':0≤z':=Nat.cast_nonneg _
    have hpos:1≤t:=one_le_mul_of_one_le_of_one_le (by unfold shiftG; linarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]) (le_add_of_nonneg_right hu')
    refine ⟨⟨hL,hM,?_ ,hh,fun V h A l hl=> Next.Foundations.left_has A hl (hh V h)⟩,mul_nonneg (pow_nonneg (zero_le_one.trans hpos) (A.power*j)) hb,fun V hv l hl h=>?_⟩
    · assumption
    apply costsD hL ht hq o' _ hm (ha _ hv) (Y:=t) ?_ hpos l (hl.trans hr) h
    intro i he; have hf : (separation i o':ℝ) ≤ z'*(4*(radiusB x:ℝ)+2)+2*(radiusB x:ℝ) := by unfold z'; exact_mod_cast Lattice.Corona.extent Z (radiusB x) he hy'
    unfold t shiftG; nlinarith [Nat.cast_nonneg (α:=ℝ) (radiusB x)]
include hb hδ he
omit hv hr hq ht hm hp
lemma aged (o':Site c) (hy:o'∈ M.crest.image S.ratio.parent)(hA:A.supportExponent+2 ≤ u₀) (p:ℕ) :
    SumBudget (fun z=> Push.Local.reservedMass A (locus M H o' z) (brushPrice M H z j σ p A.power k₁ ρ o'))
       ((k₁*(ρ^p)⁻¹)*(collars G η x j A.power * (w*(1-1/2)⁻¹))):=by
    have hv:=h.thought.scale
    have hz:=Ursell.log_hit_tail _ _ _ H.testS he (show 0≤u₀+η from by linarith only [A.exponent_pos,hA,hδ]) 0 o'
    simp only [pow_zero,mul_one,Nat.zero_le,true_and] at hz
    have hp:0 ≤ shiftG x:=by unfold shiftG; positivity
    have hu := mul_nonneg h.good (show 0 ≤ (ρ^p)⁻¹ by positivity); have hσ i : 0≤2*(2^j*σ i):=by have hh:=budget M H h i; positivity
    let v:= collars G η x j A.power; have ht:0≤v:=by unfold v collars Reserves.polyPrice; positivity
    have hx(z:H.fragrances):0 ≤ clusters H.seam (fun i=> 2*(2^j*σ i)) z.2 := clusters_nonneg _ hσ _
    have hh := budget_scale hu (budget_scale ht hz)
    refine budget_mono hh (fun z=> mul_nonneg (Real.exp_pos _).le ?_) fun z=> ?_
    · change 0 ≤ brushPrice M H z j σ p A.power k₁ ρ o'; unfold brushPrice; split
      · exact mul_nonneg (by unfold flareC; positivity) (mul_nonneg hu (hx z))
      exact le_rfl
    unfold Push.Local.reservedMass brushPrice; split
    next he' =>
      let e := locus M H o' z; let Z := reachability z; have hh' : o'∈ unionOf H.smallAt z.snd:=by
        have hf:= seatY M H o' hy z; rw [locus,if_pos he'] at hf; exact hf
      have hs : locus M H o' z=Z:= if_pos he'; let t:ℝ:=coverNumber (radiusB x) Z
      let Hq:= clusters H.seam (fun i=> 2*(2^j*σ i)) z.2; let u:= k₁*(ρ^p)⁻¹; let p':=A.power
      have hH:0≤Hq :=hx z
      have ht:0≤t:=Nat.cast_nonneg _; rw [if_pos hh',hs,hb,mul_comm]; change (shiftG x*(1+t))^(p'*j)*(u*Hq) * Real.exp (_*t) ≤ u*(v*(Hq*Real.exp ((u₀+η)*t)))
      unfold v collars; rw [mul_pow,add_mul u₀,Real.exp_add]
      have hp' := polynomial_cost hδ ht (p'*j)
      apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp' (pow_nonneg hp _)) (mul_nonneg hu hH)) (Real.exp_pos _).le)
      unfold Reserves.polyPrice; change ((shiftG x)^(p'*j) * (_*_*_*_))*(u*Hq)* _ ≤ u*( (shiftG x^(p'*j)*(_*_*_))*(Hq*(_*_)))
      nlinarith only [mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA ht))
        (show 0≤u*(((shiftG x)^(p'*j)*(η⁻¹^(p'*j)* ↑((p'*j).factorial) * Real.exp η*Real.exp (η*t)))*Hq) by positivity)]
    rw [mul_zero]; exact hh.1 z
end YM.LocalTaylorR2.Marker
