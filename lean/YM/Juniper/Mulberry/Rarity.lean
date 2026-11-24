import YM.Juniper.Mulberry.Feral
/-!
 # Actual F-tilted regime scaled log comparison. From rule_it & E2.
 No mask discarded on output. Logs at same true β path throughout. Allows
 E price on all support-real sections. This will be booted cross
 normalization queries; do NOT supply conclusions by other Lens convention.
 -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Mulberry
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Sienna Token Analysis
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f:Side} {S : StepData c f} (F:Forest S.ratio) (T: Tube G S) {r t v u s:ℝ}
    (B : BudgetPoint) (β:ℝ) (O:ChartRatio G) (k:S.Choices) (ρ : Bid.Dir G c→ AxisChart G F)
    {D : ℝ} {j:ℕ}
local notation "X"=>Positions (Uniform.Primary c G)
local notation "A"=> Pane.virgin T B β
local notation "Y"=> Poll.Body (Precision.Key F G)
local notation "M"=> (Fintype.card (Site f):ℝ)
variable (P: Activities G f)
local notation "U*"=> fleece T B β P
local notation "Yu"=> fun x:X=> represent (tint G _ x)
local notation "V'"=> Lapis.orbit F ρ
local notation "p"=> Lapis.table F k T.up T.high
local notation "q"=> Lapis.mist F O T.up
local notation "K"=> Lapis.gram F T.up T.high ρ k
local notation "X₀"=> closedBall (0:Poll.Body (Precision.Key F G)) D
local notation "ε"=> (adjustment F ρ P)
local notation "Ω"=> (Lantern.grace p q V' K + adjustment F ρ P)
local notation "Ω'"=> (gStep β)
variable (h : P.Valid B r v) (hp: title P) {J:Teller G} (ht: Intake J T t (Pane.virgin T B β))
    {c' a:ℝ}
local notation "σK"=> Env.along
local notation "Q'"=> (tempered F T B β P)
local notation "K*"=> (fun x:X=> solar F O β * Real.exp (-coverLog F T O k ρ β x))
local notation "r*"=> cut (sweep (K 0)⁻¹) X₀ Ω
variable (H : Golf (Lapis.table F k T.up T.high) (Lapis.mist F O T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ k) j D u u c')
    {x : Positions (Uniform.Primary c G)} (hx:‖x‖< u) (hr:gStep β < u) (ho: LocalRatio O)
local notation "V₀"=> staying F (V' x) (gStep β) D (Yu x)
local notation "a*"=> ratify p q V' K D
-- adaptation of Sienna.rule_it & use genuine conditional normalizers
structure Clearance (t:ℝ) (x:X) (D:ℝ): Prop where
   inside (z:Y) (hj:‖z‖≤ D) : flags B.threshold (shadeShift F ρ z x (gStep β))=∅
   rooms (z:Y)(hj:‖z‖≤ D) : windmill F (V' x+gStep β • z) ∈ mouth O
   settled (z:Y)(hj:‖z‖≤ D)(l:S.Choices) : Lapis.table F l T.up T.high (x,V' x+gStep β • z) = Lapis.table F k T.up T.high (x,V' x+gStep β • z)
   daylight : S.push β (Pane.virgin T B β).eval (Yu x) - K* x * (ratify (Lapis.table F k T.up T.high) (mist F O T.up) (Lapis.orbit F ρ) (Lapis.gram F T.up T.high ρ k) D (gStep β,x)) ≤ K* x* t

variable {Ψ:ℝ} (hc : Clearance F T B β O k ρ Ψ x D)
include H hx hr ho hc ht h hp
lemma overhang (hM:M*r≤1) : S.push β (U*).eval (Yu x)-K* x*r* (gStep β,x)∈ Set.Icc 0 (K* x*(Real.exp 1*Ψ)) := by
   let Y':= V₀; let V:= Yu x; let Ω₀:= K* x; let M₀:= Q' V; let d':= Fare.overall F T B β V; have h₀:= Fare.staying_meas F (V' x) Ω' D V
   obtain ⟨hM₀,hT⟩:= amt F T B β t J ht V; have hβ:0<β:= ht.positive; obtain ⟨hm,hQ⟩:= fulling F T B β P h hp ht V
   have he:= central F T B β O k ρ P h hp ht H hx hr ho hc.inside hc.rooms hc.settled
   have hs:= Fare.pricing F T O k ρ B β D H hβ hr (ht.ready.knobs.symm ▸ ht.ready.kernel) hx hc.settled ho hc.rooms hc.inside hM₀.meas.stronglyMeasurable
   let J':= a* (gStep β,x); have ha:0≤Ω₀:=mul_nonneg (Fare.sun F O β hβ ho |>.le) (Real.exp_pos _).le
   have hv : ∫ y in (Y')ᶜ, d' y ∂ F.order G ≤ K* x * Ψ:= by
      have hy:= hc.daylight; change S.push β (A).eval V-Ω₀*J' ≤ _ at hy
      rw [show S.push β (A).eval V=Ω₀ * J'+ ∫ y in (Y')ᶜ,d' y ∂ F.order G from (by rw [hT,show Ω₀ * J'= _ from hs.symm]; exact (integral_add_compl h₀ (hM₀.integrable _)).symm)] at hy; -- rw with V definition fails. 
      rw [add_sub_cancel_left] at hy; exact hy
   have hh : S.push β (U*).eval V= K* x * r* (gStep β,x) + ∫ y in (Y')ᶜ, M₀ y ∂ F.order G:= by
      rw [hQ, ←he]; exact (integral_add_compl h₀ (hm.integrable _)).symm
   change S.push β (U*).eval V-_ ∈_ ; rw [hh,add_sub_cancel_left]; have hz (x):0 ≤ M₀ x:= mul_nonneg (Fare.rays F T B β x _) (Real.exp_pos _).le
   constructor
   · exact setIntegral_nonneg h₀.compl (fun i _=> hz i)
   refine le_trans (b:=∫ y in (Y')ᶜ, Real.exp 1 * d' y ∂ F.order G) (setIntegral_mono_on (hm.integrable _ |>.integrableOn) (((hM₀.integrable (F.order G)).const_mul _).integrableOn) h₀.compl (fun y _=>?_)) ?_
   · rw [mul_comm (Real.exp 1) (d' y)]; refine mul_le_mul_of_nonneg_left (Real.exp_monotone (le_trans (b:=‖P.additive B (F.drape y)‖) ?_ ((stipend B P h.boundE _).trans hM))) (Fare.rays F T B β y _); exact neg_le_abs _ -- tiltF
   rw [integral_const_mul]; exact (mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le).trans_eq (mul_left_comm ..)

omit H hx hr ho hc ht h hp
def crestF (x:X):= S.push β (U*).eval (Yu x)
def veilF (x:X):= Real.log (crestF T B β P x)
def cutLog (D : ℝ) : X→ℝ:= (sampleLog (sweep (K 0)⁻¹) (closedBall (0:Y) D) Ω) ∘ (arc (gStep β))
def lacking (D:ℝ) (x:X):= veilF T B β P x - Real.log (solar F O β) + coverLog F T O k ρ β x - cutLog F T β O k ρ P D x
include H hx hr ho hc ht h hp
lemma allegiance (hM:M*r≤1)(ha:0<a)(hz:a ≤ r* (gStep β,x)): 0<crestF T B β P x ∧ |lacking F T B β O k ρ P D x| ≤ (Real.exp 1*Ψ)/a:= by
   let i:= solar F O β; let s:= coverLog F T O k ρ β x; have hi:0 < i:= sun F O β (ht.positive) ho
   have hk : K* x = Real.exp (Real.log i-s):= by rw [sub_eq_add_neg,Real.exp_add,Real.exp_log hi]
   obtain ⟨hk,hΦ,hB⟩:= Token.twist (mul_pos hi (Real.exp_pos (-s))) ha hz hk (overhang F T B β O k ρ P h hp ht H hx hr ho hc hM); exact ⟨hk,hB⟩
end YM.Juniper.Mulberry
