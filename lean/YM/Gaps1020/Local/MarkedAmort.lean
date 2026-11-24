import YM.Gaps1020.Local.MarkedReaches
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open March Next.Foundations YM.GapsLocal.ExpShares
open PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {j n k M : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {R : Rep G f}
variable {X : Coat T F} {I : Finset (Bond f)} {η r q Y W A B A' a β b p v d t γ C s C' μ g ρ ℓ : ℝ} {l:ℕ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi} {Ñ : ChartRatio G}
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
variable {z : Air f G} {V:E→ Config G c}{x:E}

variable {H : Cash W s μ L Q o C T R}

open PhysicalNext.Repeat.Lotus

open YM.RG01.Survive
variable {ι:Type}[Fintype ι]
open Merge Palette PhysicalNext.Repeat.Daisy
open Push.AbsoluteSums.Mixed Push.AbsoluteSums.Reserves
variable (N:Captain H j C' d v Y A b r B q k χ)(U:ι→Team R)(M':ι→Leaf R)
    (rA:ι→ℝ)(X:Utopia H j v d r C' χ)
local notation "I'" => Tickets (Palette.sign M' S)
open Marker Merge.Switch Gas Ursell Captain Push.GridApprox.Nil
-- Assemble *all* angular derivative costs, including every mark mode, on
-- the actual E dictionary at the same support exponent. Each Forecast basis
-- carries shared ticket/marker indices. (proof model as RG01.Survive.LeafReady.)
open Trees
variable (rV:ι→ℝ) {V':Type}[DecidableEq V']{E':Marker.Census V'} (g:ι→Poly E')
    (z:H.fragrances) (sP:ℕ→Prop)

local notation "R0" => horizonRadius G L s
variable (w:V'→ℝ) (hv:∀ i,0<w i)(hx:∀ i, Poly.price w (g i) ≤ 1) (h : Thermal.BuysMix M' H rA)
variable (M:ℕ)(Γ:Target.Expense Q)(P':BudgetPoint)(hj:P'.order=j)(hs:P'.B=radiusB s)
    (hF:WarnBudget (ρ^(M+1)) N.conduit)(hρ:2 ≤ρ)(hB:Bikes Q L μ s Γ.earn (Height.asset Γ) B j k)(hd:degreePrice (radiusB s) (ρ*(swing Q L μ 1 s 0).rootHit) Q.δ≤1/2)(ht: degreePrice (radiusB s) (Shared.value Q L μ s B ρ k j M) (Height.asset Γ)≤1/2)
include hv hx h hF hρ hB hd ht hs
local notation "η0" => Height.asset Γ
lemma cappedPrices (i:ℕ)(h':∀ j,sP j→ i≤ j) (a:ℝ)(hb:a≤Γ.earn) : Ac.Hit (reachability (H:=H)) P'.B (fun z=> wordsPrice w (priceAt N M' rA g z sP ρ M P')) a ((ρ^i)⁻¹ * (collars G η0 s j P'.power*(Shared.value Q L μ s B ρ k j M*(1-1/2:ℝ)⁻¹))) :=by
    intro x
    have hR:0<ρ:=by linarith
    let E':= reachability (H:=H); let c₀ i:= combined N M' rA M ρ (ρ^(M+1)) i; let g' z:= clusters H.seam (fun i=>2^j*c₀ i) (z:H.fragrances).2; let a':=(ρ^i)⁻¹
    have hy:= readyLog N M' rA ρ M hF (by linarith) Γ hB hd ht h
    have hz:=Ursell.log_hit_tail _ _ _ H.testS hy (add_nonneg hB.posts hB.allow.le) 0 x
    simp only [pow_zero,mul_one,Nat.zero_le,true_and] at hz
    have he0:0 < η0 := Height.asset_pos Γ
    have hp:(0:ℝ) ≤ a':=by unfold a'; positivity
    have ht':0 ≤ shiftG s:=by unfold shiftG; positivity
    have hα:0≤ collars G η0 s j P'.power:=by unfold collars Reserves.polyPrice; positivity
    have hw := budget_scale hp (budget_scale hα hz)
    refine budget_mono hw (fun z=>?_) (fun z=>?_)
    · dsimp only; split
      next h'=> exact mul_nonneg (sum_nonneg fun i _=> mul_nonneg (Poly.worth hv _).le (price0 N M' rA g z sP h M P' i hR.le)) (Real.exp_pos _).le
      next=>rfl
    dsimp only; split
    next ha=>
      have he:= amortized N M' rA g z sP w hv hx h hρ P' M i h' -- order check
      let Y:ℝ:= coverNumber P'.B (E' z); have hY:0≤Y:=Nat.cast_nonneg _
      rw [if_pos (show x∈ unionOf H.smallAt z.2 from ha), ← hs]; apply (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le).trans
      have hu:0 ≤ g' z:= clusters_nonneg _ (fun i=> hy.2.2.2.2.1 i) _
      change (sidecost z j P') * (a'*g' z) * Real.exp (a*Y) ≤ a'*(collars G η0 s j P'.power * (g' z * Real.exp ((Γ.earn+η0)*Y)))
      have hc:sidecost z j P'≤ collars G η0 s j P'.power* Real.exp (η0*Y):=by unfold sidecost; rw [mul_pow]; exact (mul_le_mul_of_nonneg_left (polynomial_cost he0 hY _) (pow_nonneg ht' _)).trans_eq (mul_assoc ..).symm
      apply le_trans (mul_le_mul (mul_le_mul_of_nonneg_right hc (mul_nonneg hp hu)) (Real.exp_monotone (mul_le_mul_of_nonneg_right hb hY)) (Real.exp_pos _).le (mul_nonneg (mul_nonneg hα (Real.exp_pos _).le) (mul_nonneg hp hu))) (le_of_eq ?_); rw [add_mul, Real.exp_add]; ring
    next h'=> exact hw.1 z
end YM.ConnectedActivityE6.Blaze.Thermal1020.Shared
