import YM.RGLocalTaylor.Post.Paid
import YM.RGLocalTaylor.Consumer.MilestoneOne

/-! # Lease work on physical spring. Actual post and pre estimates
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Post
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open UVNext UVNext.CouplingReset Input PriceCompiler Rain Mallow Spring
open Progress.DirectedRecipe Averaging RGLocalTaylor.Read Leasing
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {X: Metals G} {D : Rolls X.p} {A: Alloy X D} {R:Factor A} {l v:ℝ}
    {m N n : ℕ} {Q : UVNext.CouplingReset.In A.B.a m n} (H:Spring R N m n l v Q) (x:ℝ)(hX:x∈ Icc l v)
set_option quotPrecheck false
local notation "I" => A.B.a.S.side m n
local notation "y" => A.B.a.clock.hatBeta m
local notation "B" => (A.B.a.budget m)
local notation "bᵥ" => A.B.a.clock.hatBeta (m+1)
local notation "J" => A.B.a.clock.J (m+1)
local notation "L₀" => D.L J
local notation "s₀" => (A.B.a.params m)
local notation "clip'" => (A.B.a.params m).clip
local notation "c'" => A.B.a.clock.allowance m
local notation "t'" => A.B.a.clock.forcedAllowance m
local notation "b'" => (Q x).beta
local notation "g'" => (Real.sqrt (Q x).beta)⁻¹
local notation "k" => Rain.lint R.target A m
local notation "α" => A.B.kin.alpha N m
local notation "Z" => H.result x
local notation "Z'" => (H.result x).activities
local notation "p'" => Time.forecastE A.B.a m
local notation "q'" => Time.forecastK A.B.a m R.scout (Q x).beta
set_option quotPrecheck false
local notation "Y" => (H.X'.reg)
local notation "W" => (A.B.kin.path N m)
local notation "ρ" => (Mayer.arcRadius G L₀ y)

namespace Worker
variable (M : ℕ)
local notation "D₁" => ρ ^ (M+1)
local notation "D₂" => (H.V' x)
local notation "d!" => (design H x M)
local notation "e!" => (blanks H x M)
local notation "z!" => t'

open UVExtension Oasis Mast RG01
private lemma grantK (p j:ℕ) (hG:G.Simple) :
    ∃ c:ℝ, 0≤c ∧ ∀ m:ℕ, ∀ u:ℝ, u∈ RG.Shoot.band A.B.a (m+1) → 0<u → let w₀:=A.B.a.clock.forcedAllowance m
      A.B.a.clock.hatBeta (m+1)^j*(w₀/Real.sqrt w₀) ≤ c* (Real.sqrt u)⁻¹^p:= by
  obtain ⟨c,hc,h⟩:= Vacuum.Flat.currency A.B.a hG p j
  refine ⟨c,hc,fun m u hv hu=>?_⟩; let w:= A.B.a.clock.forcedAllowance m; have hw : 0<w:=Real.exp_pos _
  intro w₀; rw [show w₀/Real.sqrt w₀=Real.sqrt w₀ from (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hw))).2 (Real.mul_self_sqrt hw.le).symm]; exact h m _ hu (Or.inl hv.2)

-- order convention and exact cost, stamp. W0 K unconditional using Valid at this price.
include hX
lemma powered (d p:ℕ) (hd: M=d+2) (hp:8*p ≤ 7*d) (hG:G.Simple) (h: Mallow.RG12.Earned (Leasing.receipt G) R.shape A.delay)
    (hm : m<N) (hK:M ≤ A.B.a.clock.J (m+1)) : StepCosts H x M ((Real.sqrt 2)^p*g'^p):=by
  apply (souvenirs H x hX h hm hK hG).weaken
  have hv : bᵥ=betaF G y L₀:= PriceCompiler.beta_eq A.B.valid m
  have ht:(Q x).beta∈ RG.Shoot.band A.B.a (m+1):= (H.knows x hX).2
  have hh :1<bᵥ:= A.B.a.fits.delayed _; have hθ:0< (Q x).beta:= by linarith [ht.1]
  unfold finalPrice Mayer.arcRadius; rw [←hv, show M+1=d+3 from by omega, pow_add]
  let v:= bᵥ^Mayer.height; have hΩ:0<v:=Real.rpow_pos_of_pos (zero_lt_one.trans hh) _
  rw [_root_.mul_inv_rev,←mul_assoc,mul_inv_cancel₀ (show v^ (3:ℕ)≠0 from by positivity), one_mul]; exact Mayer.pay_extra hh.le hθ ht.2 hp

end Worker
end YM.RGLocalTaylor.Post

namespace YM.RGLocalTaylor.Consumer
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling
open Extra.Iteration RG.Shoot Push.SectorMeasure Supply Input Testing Push.PriceCompiler Org
open ConnectedActivityE6.Blaze Blaze.March Captain Silica PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Height Refrain Song
open PhysicalNext.Repeat.Greenbelt Match Roof Roost Geo Time Opera PhysicalNext.Repeat.Legato
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RG01 RG01.Survive Daisy.Charity.RG12 Post Post.Worker Mallow
open Progress.DirectedRecipe UVExtension Spire Orchard Mast Oasis
variable {G : Gauge} {X : Metals G} {D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
   {hG:G.Simple}

-- Any horizon O provisioning herein. Actual history cutoff index & band values
-- including Rose(C). Replay estimate on Rose without modifying the family!
-- (C path convention at canonical 0 only in consumer public.)
set_option quotPrecheck false
structure Obligates (S : Uses R hG) : Prop where
  commits (p d K:ℕ) (hp:8*p≤7*d): ∃ C:ℝ,0≤ C ∧
    ∀ (m N n:ℕ) (hm:m<N) (_hV:d+2≤A.B.a.clock.J (m+1)) (b:Rose S),
      let H:= (Orchard.ray S N n m b hm).body
      let V:= S.realBeat b.val N n (m+1); let U:= S.realBeat b.val N n m; let g:= (Real.sqrt V.beta)⁻¹
      0< V.beta ∧ 0<g ∧
      U=H.result Orchard.beam0 ∧
      A.B.a.clock.hatBeta (m+1)^K*((A.B.a.clock.forcedAllowance m)/Real.sqrt (A.B.a.clock.forcedAllowance m)) ≤ C*g^p ∧
      StepCosts H Orchard.beam0 (d+2) (C*g^p)

lemma constructed (S : Uses R hG) (h : Mallow.RG12.Earned (Leasing.receipt G) R.shape A.delay) : Obligates S:= by
  constructor
  intro p d K hp; obtain ⟨c,hc,hK⟩:= Post.Worker.grantK (A:=A) p K hG
  let C:=Real.sqrt 2^p; have hC:0≤ C:= by unfold C; positivity
  refine ⟨C+c,add_nonneg hC hc,fun m N n hm hM b=>?_⟩; intro H V U g
  have ht:V= S.realBeat b.val N n (m+1):=rfl
  have hθ := H.knows Orchard.beam0.val Orchard.beam0.2|>.2
  change V.beta∈band A.B.a (m+1) at hθ; have hu : 0<V.beta:= by linarith [A.B.a.fits.delayed (m+1), hθ.1]
  have hg : 0<g:= by unfold g; positivity
  refine ⟨hu,hg,ponds ..,(hK m _ hθ hu).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC) (pow_nonneg hg.le _)),?_⟩
  exact (powered H Orchard.beam0 Orchard.beam0.2 (d+2) d p rfl hp hG h hm hM).weaken (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hc) (pow_nonneg hg.le _))
end YM.RGLocalTaylor.Consumer
