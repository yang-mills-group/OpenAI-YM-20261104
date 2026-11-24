import YM.RGLocalTaylor.Post.Voucher
import YM.RGLocalTaylor.Post.Combine
import YM.RGLocalTaylor.Post.Turns
/-!
# At the actual `Spring.result`

This is a quantitative re-expression estimate specifically in the supported
`E`, `K`, β and scalar channels after TRUE kinetic extraction. Pricing of
shared sources to be done separately (preserve every Wings Holder etc).
Includes actual covariance in the sense of `Valid`, and return-density factor exact
(even if nonempty dirty flags & no ratio claim). The `stamps` estimates are
powered directly with admitted `cutoffOrder` enlarged. Forgetting the model
parameter in any application risks hiding losses from imposing other costs.
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
def sculpture : glyph G (I) := Anchor.central W clip' B H.X' d! α
def effigy : glyph G (I) := Anchor.central W clip' B H.X' e! 0

def estimateBeta : ℝ := predictor A.B N Q x + Averaging.delta (H.X'.read d!)
def estimateScalar : ℝ := Collection.vac d! (stance H x M)

private def preco := (D₁)⁻¹+turnFee B* Read.Pane.locator k B (D₁)⁻¹
abbrev finalPrice (_X:Factor A)(m M:ℕ):=(Mayer.arcRadius G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m) )^(3:ℕ)* (((Mayer.arcRadius G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m))^(M+1))⁻¹)
variable {M}

-- Same listing all the way through Projection and merging.
structure StepCosts (H: Spring R N m n l v Q) (x:ℝ) (M:ℕ) (z : ℝ) : Prop where
  kinetic : |(H.result x).beta-estimateBeta H x M|≤ z
  scalar : |(H.result x).v-estimateScalar H x M|≤ z
  assembled : (H.result x|>.activities.E)=sculpture H x M+effigy H x M
  acceptsMain : (imprint (H.result x).activities (sculpture H x M)).Valid (A.B.a.budget m) (A.B.a.clock.allowance m+z) (A.B.a.clock.forcedAllowance m)
  acceptsTail : (imprint (H.result x).activities (effigy H x M)).Valid (A.B.a.budget m) z (A.B.a.clock.forcedAllowance m)
  link : A.B.Move N m n (H.result x) (Q x)
  pricedPrint : (H.V' x).logRead=(design H x M).logRead+(blanks H x M).logRead ∧
    Local H.X' B (design H x M) (Time.forecastE A.B.a m+z) (Time.forecastK A.B.a m R.scout (Q x).beta) ∧ Local H.X' B (blanks H x M) z (Time.forecastK A.B.a m R.scout (Q x).beta)

namespace StepCosts
variable {H x} {z z':ℝ}
lemma weaken (h:StepCosts H x M z) (ht:z≤z'):StepCosts H x M z':= ⟨h.kinetic.trans ht,h.scalar.trans ht,h.assembled,
  { h.acceptsMain with boundE:= VerifiedReset.Time.E_rises h.acceptsMain.boundE (add_le_add_right ht _) }, { h.acceptsTail with boundE := VerifiedReset.Time.E_rises h.acceptsTail.boundE ht }, h.link, h.pricedPrint.1, redeem h.pricedPrint.2.1 (add_le_add_right ht _), redeem h.pricedPrint.2.2 ht ⟩ where
    redeem {f : Collection.Source G (I)}{a b c:ℝ}(h:Collection.Local H.X' B f a c)(ht:a≤b):Collection.Local H.X' B f b c:={ h with cheap:=by obtain ⟨g,hg,hU⟩:=h.cheap; exact ⟨g,hg,fun i=> budget_loosen (hU i) ht⟩ }

-- Explicit decomposition of the same unnormalized density at all U, also
-- those with nonempty flags. Applying an integrator/predictor to this requires
-- extra cost comparisons to be proved for that integrator/predictor; the one-step
-- adapter already includes the actual identity and aligned-family estimates.
lemma evaluation (h:StepCosts H x M z) :
    (A.B.a.clock.op m n).push (Q x).beta (Q x).eval = (Z).eval ∧
      ∀ V, (Z).eval V = Real.exp (descending Z (effigy H x M) (estimateBeta H x M) (estimateScalar H x M) V) * (template Z (sculpture H x M) (estimateBeta H x M) (estimateScalar H x M)).eval V :=
  ⟨h.link.ident.symm,fun V=> template.recovers _ _ h.assembled (h.link.bundle.point.symm ▸ h.acceptsMain) (h.link.bundle.point.symm ▸ h.acceptsTail) V⟩
end StepCosts

variable (hs : Mallow.RG12.Earned (Leasing.receipt G) R.shape A.delay)(hm:m<N)(hM:M≤ A.B.a.clock.J (m+1))
    (hG:G.Simple)
include hs hm hM
local notation "ℓ" => (licensePrice s₀ k y)
local notation "v₀" => preco (R:=R) (m:=m) M -- arg order check
omit hm hM in
private lemma funding :
    let D':=(D₁)⁻¹
    let t:= finalPrice R m M
    Mallow.RG12.Earned (Mayer.decal G) R.shape A.delay ∧
      0≤ D' ∧ (B).threshold^2>0 ∧
      ((B).threshold^2)⁻¹*v₀ ≤ t ∧
      (Animals.ballCost (Meadow.studio k (radiusB y)):ℝ)*D'+v₀ ≤ t ∧
      regularNeed G B (s₀).clip (s₀).width (s₀).paths 0 v₀ ≤ t :=by
  intro D' u
  have he : VerifiedReset.Time.Same s₀ B:= ⟨rfl,rfl,rfl⟩
  have hEq:s₀=X.p.profile (A.B.a.clock.J m):= params_eq A.B.valid m
  have hf' : turnFee B=Height.away s₀:=rfl
  have H:= (hs J y (A.B.valid.pays m) (A.B.a.clock.J m) (step_paid A.B.a m)).2
  obtain ⟨hY,hQ⟩:= (show 0< y ∧ regulator G (X.p.profile (A.B.a.clock.J m)) k y ≤ ρ^(3:ℕ) from H)
  rw [← hEq] at hQ
  obtain ⟨hf,hL,hQ,hO⟩:= Leasing.settles (L:=L₀) (p:=B) (G:=G) (X:=s₀) (j:=k) (b:=y) he rfl rfl hf' hY hQ
  have hx: bᵥ=betaF G y L₀:=PriceCompiler.beta_eq A.B.valid m; have hr:0< betaF G y L₀ := hx ▸ (zero_lt_one.trans (A.B.a.fits.delayed (m+1)))
  have hu:0≤D':=by unfold D' Mayer.arcRadius; positivity
  have hP : v₀= ℓ * D':= by unfold preco; rw [hf, orientExact s₀ k y he rfl, orientExact s₀ k y he rfl 1]; change D'+ _*(_*D')=_; ring
  rw [hP,projectionFee _ he, ←mul_assoc, ←add_mul, ← mul_assoc (VerifiedReset.Time.base ..)]
  exact ⟨fun i x0 H j Hj=> (hs i x0 H j Hj).1,hu,pow_pos (B).threshold_pos _, mul_le_mul_of_nonneg_right hL hu, mul_le_mul_of_nonneg_right hQ hu,mul_le_mul_of_nonneg_right hO hu⟩

include hG hX
-- Customers never apply through a merely predicate-equal volume.
set_option maxHeartbeats 800000 in
lemma souvenirs : StepCosts H x M (finalPrice R m M) := by
  let f:= preco (R:=R) (m:=m) M; let v':= finalPrice R m M
  obtain ⟨ht,hNN,hξ,hg,hJ,hP⟩:= funding (M:=M) (m:=m) (R:=R) hs
  have hZ := earrings H x ht hM hm; have ha:= letters H x ht hM hm
  have hc:= H.core hm x hX; have hy:= H.owns hG hm hX
  have hp:= (R.machine.passes hm H.knows).1
  have hx : (s₀) =X.p.profile (A.B.a.clock.J m):= PriceCompiler.params_eq A.B.valid m
  let HH x:= (H.V' x).logRead
  have hd : orient B Y (HH x) p':= by obtain ⟨f,hf,h⟩:= hc.cheap; exact ⟨f,h,fun i=> ⟨hc.smooth i,hf i⟩⟩
  let A':= (imprint Z' (sculpture H x M)); let A0:= (imprint Z' (effigy H x M))
  have hW:= A.B.support.cap N m hm.le; have hT := Return.enough_room A.B m n
  have hh:= (H.moves hG hm).2 x hX|>.1
  have Hδ : Averaging.delta (H.X'.read D₂) = Averaging.delta (H.X'.read d!)+ Averaging.delta (H.X'.read e!) := Anchor.kinetic hG ha hd hZ
  have hs' := Anchor.residual_balance (p:=B) ha hd hZ
  have hB:Local H.X' B d! (p'+f) q':= Anchor.civilized (v:=H.V' x) (a:=d!) rfl (fun s b=> transfixed H x M hm s b hX) hs' hc
  have h₀:Local H.X' B e! f q':= Anchor.civilized (v:=H.V' x) (a:=e!) rfl (fun s b=> transfixed_tail H x M hm s b hX) hZ hc
  have hA:(Z').Valid B c' t':= by rw [← hh.bundle.point]; exact hh.bundle.valid.labels
  have hz:(Z').reg=(drawer G I).reg:= by rw [hy]; rfl
  have hu := Anchor.central_add W clip' α hG ha hd hZ
  have hu' : (Z').E=sculpture H x M+effigy H x M:= by rw [hy]; exact hu
  have ht₁:=Anchor.transplant hG hs' hW hp.decent hT α hz hp.width
  obtain ⟨hR,ht'⟩:= Anchor.transplant hG hZ hW hp.decent hT 0 hz hp.width
  have hM' : A0.EBound B v':= VerifiedReset.Time.E_rises ht' hP
  have hR' : A0.RegularFamily B:= hR
  have hc : f≤v' := by
    apply le_trans (b:= _ ) _ hJ
    exact le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hNN)
  refine ⟨?_,?_,hu',template.inheritance (sculpture H x M) hA ht₁.1 (template.part hu' hR' hA.regular hM' hA.boundE) (fun s b=> Anchor.replicate _ s b hG hB hW hp.decent hT hz rfl (hA.moves s b) α), template.inheritance (effigy H x M) hA hR hM' (fun s b=> Anchor.replicate _ s b hG h₀ hW hp.decent hT hz rfl (hA.moves s b) 0),hh,ha,
    Anchor.civilized (v:=H.V' x) (a:=d!) rfl hB.transforms (orient.widen hs' (add_le_add_right hc _)) (H.core hm x hX), Anchor.civilized (v:=H.V' x) (a:=e!) rfl h₀.transforms (orient.widen hZ hc) (H.core hm x hX)⟩
  · rw [hy]; change |predictor _ _ _ _+Averaging.delta _ - (predictor _ _ _ _+Averaging.delta _)| ≤ _; rw [Hδ,← add_assoc, add_sub_cancel_left]
    have ht:=Averaging.delta_bound hG (Anchor.projection_cap hZ); apply le_trans _ hg; rw [inv_mul_eq_div,le_div_iff₀ hξ,mul_comm]; exact ht
  rw [hy]; exact (Anchor.vacuum_delta ha hd hZ (H.τ x) (stance H x M)).trans ((add_le_add_left (rent H x ht hM hm) _).trans hJ)
end Worker
end YM.RGLocalTaylor.Post
