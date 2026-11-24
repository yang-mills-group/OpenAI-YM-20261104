import YM.LocalTaylorR2.Reset.Docket
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Beam.Docket
/-!
 # Hit before rotating & moving Posts. Uniform across all alliance-anchor choices.

 Same support (and incoming/Fragrance cooking from step H), post-anchor
 MAY MOVE. Use hit at all x to get anchored invoice for Beam. Later the
 path-threshold reinterpretation can use only these regular addresses.
 Fee already charged with the intended rotation prices of per-block contour
 $j,v$ and stiffness. Keep support arrays. This version of Unroll.clearing costs
 nothing extra at the new site. Keep the grade filter identical over the
 whole contour, i.e. do not form derivatives ignoring labels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n j : ℕ} {R : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}

open YM.RG01.Survive

namespace ReadyAll
open LeafReady
variable {K M : ℕ} {l : ℝ} {y : Expansions H M} {v ρ : ℝ} {u : H.ThinP→Orders M→ℝ} {g:H.ThinP→ℝ}
    (h : ReadyAll χ y v j u g ρ) (take:H.fragrances→ ℕ → Prop)
    (z:H.fragrances)

include h
theorem hit_panel (b:BudgetPoint) (w δ β:ℝ)(a:ℝ)
    (hs:b.threshold=Pressure.temp s)(hB:b.B=radiusB s) (hj:b.order≤j) (n:ℕ)(hn:b.power≤n)
    (q:ℝ)(hq:0≤q)(hS:Sailor G b.threshold q j)(hr:j*q≤v)(hv:0<v)
    (hA: AnalyticBridge.VerifiedReset.Quotes.preExponent b ≤ a)
    (hδ:0<δ)
    (hY:Ready H.smallAt b.B (fun i=>2^j*g i) (a+δ) w δ β)
    (r:ℕ)(he:∀ z n,take z n → r ≤ n):
    ∀ x : Site c, SumBudget (fun z:H.fragrances=> if x∈ reachability z then ((ρ^r)⁻¹*allowance b z j n g)*Real.exp (AnalyticBridge.VerifiedReset.Quotes.preExponent b*coverNumber b.B (reachability z)) else 0)
      ((ρ^r)⁻¹*(collars G δ s j n*(w*(1-β)⁻¹))) :=by
  let Z:=reachability (H:=H)
  let u:= (ρ^r)⁻¹; have hu:0<u:=by unfold u; have hf:=zero_lt_one.trans_le h.scale; positivity
  have hp:0 ≤ shiftG s:=by unfold shiftG; positivity
  have hg i : 0≤g i:=nonneg_of_mul_nonneg_right (hY.2.2.2.2.1 i) (by positivity : (0:ℝ)<2^j)
  have hx z:= h.germs take z b hs hj hB q hq hS hr hv n hn (Song.locate H z).site (Song.locate H z).anchor r (he z) hg
  intro x
  have hK:0≤a+δ:= add_nonneg ((show (0:ℝ)≤AnalyticBridge.VerifiedReset.Quotes.preExponent b from by unfold AnalyticBridge.VerifiedReset.Quotes.preExponent; have h:=b.exponent_pos; positivity).trans hA) hδ.le
  have hz:=Ursell.log_hit_tail _ _ _ H.testS hY hK 0 x
  simp only [pow_zero,mul_one,Nat.zero_le,true_and] at hz
  let v:= collars G δ s j n
  have ht:0≤v:=by unfold v collars Reserves.polyPrice; positivity
  have hh := budget_scale hu.le (budget_scale ht hz)
  refine budget_mono hh (fun z=>?_) fun z=> ?_
  · split
    next=> exact mul_nonneg ((hx z).2.1) (Real.exp_pos _).le
    exact le_rfl
  split
  next hy=>
    have hv: x∈ Z z:=hy
    let t:ℝ:=coverNumber b.B (Z z)
    let Hq:= clusters H.seam (fun i=>2^j*g i) z.snd
    have hu':0≤Hq := clusters_nonneg _ (fun i=>mul_nonneg (by positivity) (hg _)) _
    have he':0≤t:=Nat.cast_nonneg _
    rw [if_pos (show x∈unionOf H.smallAt z.2 from hv)]; change u*((shiftG s*(1+t))^(j*n)*Hq) * Real.exp (_*t) ≤ u*(v*(Hq*Real.exp ((a+δ)*t)))
    unfold v collars
    rw [Nat.mul_comm j n,mul_pow,add_mul a, Real.exp_add]
    have h := polynomial_cost hδ he' (n*j)
    apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (pow_nonneg hp _)) hu') hu.le) (Real.exp_pos _).le)
    unfold Reserves.polyPrice
    nlinarith only [mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hA he'))
      (show 0≤u*(((shiftG s)^(n*j)*(δ⁻¹^(n*j)* ↑((n*j).factorial) * Real.exp δ*Real.exp (δ*t)))*Hq) by positivity)]
  exact hh.1 z
end ReadyAll
end YM.LocalTaylorR2
