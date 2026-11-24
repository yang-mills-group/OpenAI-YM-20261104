import YM.RG01Estimate.ConditionalBasic
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Canvas
/-!
# Separate an exact weighted analytic chart interior from the actual K. Small tori.

Sienna's stays include the seams (`≤`). We work with the all-fields kernel.
Local inputs E*, source-density coefficients (ALL monomials) on an auxiliary torus can be
priced by these bills when all fields of that auxiliary vacuum are globally good. The measure's
complement includes fields at which participating mask queries are not certified, not an
analytically continued discontinuous function. We apply the estimates also to enough *nearby*
coarse configs to bound derivatives without differentiating these regions.

Unused tag choices of the small germ retain their actual total mass. If using this for
source products the argument supplied to `prices` must multiply the vacuum's same input,
not a separately normalized kernel. The pure vacuum here has flags vanishing; weigh by the
other intended short analytic packets (seed-free sector), not an identity with a full main-torus
marked output polynomial until **locality and reconstruction** adapters apply. This file does
not impose or pay the volume costs or choose any history. Consume at the same auxiliary K
purchased as part of a Gauge's Family setup, never asserting compatibility automatically.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Courtyard
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented PhysicalNext.Repeat
open PhysicalNext.Repeat.Lapis PhysicalNext.Repeat.Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums PhysicalNext.Repeat.Fare Sienna
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (F : Forest S.ratio) (T : Tube G S) (O : ChartRatio G) (k : S.Choices)
local notation "X" => Positions (Uniform.Primary c G)
local notation "K" => Precision.Key F G
local notation "Y" => Poll.Body K
variable (ρ : Bid.Dir G c→AxisChart G F) (B : BudgetPoint) (β D : ℝ) {p a s u v ε: ℝ} {j : ℕ}
local notation "M" => Lapis.gram F T.up T.high ρ k
local notation "A" => Lapis.table F k T.up T.high
local notation "μ" => Poll.sweep (M 0)⁻¹
local notation "H₀" => mist F O T.up
local notation "G₀" => Lapis.orbit F ρ
local notation "V" => (fun x : X=> represent (tint G _ x))
local notation "d" => gStep β
local notation "R₀" => Pane.virgin T B β

def price (x : X) := solar F O β * Real.exp (-coverLog F T O k ρ β x)

def field (x : X) (z : Y) := F.drape (draw F (V x) (G₀ x+d • z))

-- All decisions and geometric constraints certified at the actual V x and same parameters.
structure Interior (x : Positions (Uniform.Primary c G)) (u p ε : ℝ) (j : ℕ) : Prop where
  calcJ : Golf A H₀ G₀ M j D u u p
  rays : S.patch.Branches S.kernel G
  room : 0<β ∧ gStep β < u
  center : ‖x‖< u
  voteMass : ∀ z:Y, ‖z‖≤ D→ ∀ l:S.Choices, Lapis.table F l T.up T.high (x,G₀ x+d • z)=A (x,G₀ x+d • z)
  opens : LocalRatio O
  inside : ∀ z:Y, ‖z‖≤D → windmill F (G₀ x+d • z) ∈ mouth O
  mask : ∀ z:Y, ‖z‖≤D → flags B.threshold (field F ρ β x z)=∅
  unmarked : S.push β (R₀).eval (V x)- price F T O k ρ β x* ratify A H₀ G₀ M D (d,x)∈
      Set.Icc 0 (price F T O k ρ β x*ε)

section vector
variable {P : Teller G} (Zh : Intake P T s (Pane.virgin T B β))
variable {x : Positions (Uniform.Primary c G)} (hx : Interior F T O k ρ B β D x u p ε j)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
local notation "sB" => closedBall (0:Poll.Body K) D
local notation "sW" => staying F (G₀ x) d D (V x)
local notation "U" => Pane.virgin T B β
local notation "J" => overall F T B β (V x)

def direct (f : Config G f → E) (x : X) (z : F.Slice G) :=
    S.density β (F.drape z) (V x) • f (F.drape z)

-- indicator for central weight
def restricted (z : Y→ E) (w : ℝ×X) (y : Y) := ballots A H₀ G₀ M D w y • z y
variable {f₁ : Config G f → E} (g : Poll.Body (Precision.Key F G) → E)
    (he : StronglyMeasurable f₁) (hI : Integrable (restricted F T O k ρ D g (gStep β,x)) (Poll.sweep (Lapis.gram F T.up T.high ρ k 0)⁻¹))
    (hG : GaugeInvariant f₁) (hv : ∀ u, ‖f₁ u‖ ≤ a*((Pane.virgin T B β).eval u))
    (hR : ∀ z:Poll.Body (Precision.Key F G), ‖z‖≤ D → f₁ (field F ρ β x z)= (Pane.virgin T B β).eval (field F ρ β x z) • g z)
include hx
omit hx [CompleteSpace E] in
include hv in
lemma direct_le : ∀ i, ‖direct F β f₁ x i‖ ≤ a*J i:= by
  intro i; unfold direct; rw [norm_smul, Real.norm_of_nonneg (StepData.density_positive ..),Fare.total]
  rw [mul_left_comm a]; exact mul_le_mul_of_nonneg_left (hv _) (StepData.density_positive ..)
omit [CompleteSpace E] in
include he in
lemma direct_measured : StronglyMeasurable (direct F β f₁ x):= by
  have hm := (S.density_meas hx.rays β).comp (F.continuous_drape.measurable.prodMk (measurable_const (a:=V x)))
  exact hm.stronglyMeasurable.smul (StronglyMeasurable.comp_measurable he F.continuous_drape.measurable)

include hv he Zh hR hI
lemma fixed_ball_price :
    (∫ i in sW, direct F β f₁ x i ∂F.order G) = price F T O k ρ β x •
    (∫ y, restricted F T O k ρ D g (d,x) y ∂ Poll.sweep (M 0)⁻¹) := by
  let s:= direct F β f₁ x; let G':= restricted F T O k ρ D g (d,x)
  have hm := direct_measured F T O k ρ B β D hx he
  have he' : Integrable s (F.order G):= (((amt F T B β _ P Zh (V x)).1.integrable _).const_mul a).mono'
      hm.aestronglyMeasurable (Eventually.of_forall (direct_le F T B β (x:=x) hv))
  apply (SeparatingDual.eq_iff_forall_dual_eq (R:=ℝ)).mpr
  intro L; change L (∫ i in _, s i ∂_)=L (price F T O k ρ β x • ∫ i,G' i ∂μ)
  rw [← L.integral_comp_comm he'.integrableOn, L.map_smul, ← L.integral_comp_comm hI]
  change (∫ i in _, L (s i) ∂_) = price F T O k ρ β x* ∫ i,L (G' i) ∂μ
  have hQ : (M 0).PosDef:= (hx.calcJ.gram 0 (by simp [hx.calcJ.pos])).1
  rw [cubits F O _ _ _ _ (fun i=>L (s i)) (gS β hx.room.1).1 hx.opens hx.inside (L.continuous.comp_stronglyMeasurable hm), ← integral_const_mul,← integral_indicator measurableSet_closedBall, Blaze.Shield.recommends _ hQ.inv,← integral_const_mul]
  apply integral_congr_ae; filter_upwards with z
  by_cases H:z∈ sB
  · let B₀ := V x; let X₀:= field F ρ β x z
    let w:= G₀ x+d • z; let R:= draw F B₀ w
    have he : s R = J R • g z := by
      have hf : f₁ X₀=(R₀).eval X₀ • g z:= hR z (mem_closedBall_zero_iff.mp H)
      change S.density β X₀ B₀ • f₁ X₀=_; rw [hf,Fare.total,smul_smul]; rfl
    have hy: G' z=Real.exp (grace A H₀ G₀ M z (d,x)) • g z:= by unfold G' restricted ballots; rw [indicator_of_mem H]
    rw [indicator_of_mem H]
    have hv : d^ Fintype.card K*(pay O (windmill F w)*J R)= _ := Fare.reserves F T O k ρ B β D hx.calcJ hx.room.1 hx.room.2 hx.rays hx.center hx.voteMass hx.opens hx.inside hx.mask z H
    change d^ Fintype.card K*(pay O (windmill F w)* L (s R))=price F T O k ρ β x* (Shield.lens₀ _ z* L (G' z))
    rw [hy, he, L.map_smul, L.map_smul,smul_eq_mul,smul_eq_mul, ← mul_assoc (pay ..),← mul_assoc, hv]
    unfold price; ring
  have hg: G' z=0:= by unfold G' restricted ballots; rw [indicator_of_notMem H, zero_smul]
  rw [indicator_of_notMem H]; simp [hg]

include hG
lemma prices (ha : 0≤a) :
    ‖S.push β f₁ (V x) - price F T O k ρ β x • (∫ y, restricted F T O k ρ D g (d,x) y ∂μ)‖ ≤
       a * (price F T O k ρ β x * ε) := by
  let s:= direct F β f₁ x; let t:= price F T O k ρ β x
  have hg (θ:Config G f): ‖f₁ θ‖ ≤ a * (R₀).eval θ:= hv _
  have h : AEStronglyMeasurable f₁ (prior G f):= he.aestronglyMeasurable
  have hh := direct_le F T B β (x:=x) hv
  rw [F.pushing (S.isKernel hx.rays β) _ _ hG ((((R₀).envelope Zh.cap).integrable _|>.const_mul a).mono' h (Eventually.of_forall hg)) (fun t U'=> S.covary hx.rays t β U' _), ← fixed_ball_price F T O k ρ B β D Zh hx g he hI hv hR]
  change ‖(∫ i, s i ∂_)-(∫ i in sW,s i ∂_)‖ ≤ _
  have hm:= direct_measured F T O k ρ B β D hx he
  let shi := amt F T B β _ P Zh (V x)
  have hJ := shi.1.integrable (F.order G)
  have hi := ((hJ.const_mul a).mono' hm.aestronglyMeasurable (Eventually.of_forall hh))
  have hS:MeasurableSet sW:= staying_meas ..
  change Integrable s _ at hi
  have hm:= integral_add_compl hS hi
  rw [show (∫ i, s i ∂F.order G)=_ from hm.symm,add_sub_cancel_left]; apply (norm_integral_le_integral_norm _).trans
  have hk: (∫ i in sW,J i ∂F.order G)=_ := Fare.pricing F T O k ρ B β D hx.calcJ hx.room.1 hx.room.2 hx.rays hx.center hx.voteMass hx.opens hx.inside hx.mask (shi.1.meas.stronglyMeasurable)
  have hP: (∫ i in sWᶜ,J i ∂F.order G) ≤ t*ε:= by
    have hW:= hx.unmarked.2; rw [shi.2] at hW
    have hW' := integral_add_compl hS hJ; rw [hk] at hW'; unfold price at hW; rw [← hW', add_sub_cancel_left] at hW; exact hW
  have hz : a*(∫ i in sWᶜ,J i ∂F.order G) ≤ _:=mul_le_mul_of_nonneg_left hP ha
  rw [← integral_const_mul] at hz; exact (setIntegral_mono hi.integrableOn.norm (hJ.const_mul a|>.integrableOn) hh).trans hz
end vector
end YM.RG01Estimate.Courtyard
