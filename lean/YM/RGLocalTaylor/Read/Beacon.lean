import YM.RGLocalTaylor.Read.Cleared

/-!
# Quantitative Taylor after the paired masks and tracking local pullback

Use the auxiliary-torus Gram/log argument in the output E bounds (`PNRepeat`).
Here it allows a direct estimate, charging all of the representation change,
as a full germ at each field in the *actual* local mask (no need to enforce
`Sunny` emission on the translated field, even taking its derivatives right
at the cutoff). Work on the projected reg support weights.
Proof adapted/simplified from the bounds Trio.{Weld,..}, Rain.Glazing.
Costs paid only for regular packets after localization; does NOT take those
Taylor coefficients as functions to insert into a recomputed `Rep` with its
own K/sector companions. Instead our approximation to the regular cost always
keeps the final exact K with its supports and stencil.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Read.Pane
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L:Side} {j i m n w r k l:ℕ} (B : BudgetPoint) {Y:Stars→Side}
open Trio

section morph
variable {q: Stars→ℝ} (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (z:ℕ) (f' f₁ f₂: ∀ i:Stars,Trio.Offer G (Y i))
-- Freely admit the advertised family of materials.
lemma ornament_add : Trio.ornament (c:=c) Q (fun i=> f₁ i+f₂ i) = Trio.ornament Q f₁ + Trio.ornament Q f₂ := by
  ext i V; unfold Trio.ornament Trio.beacon Trio.unit Trio.rip stillA; simp_rw [Pi.add_apply,add_sub_add_comm,sum_add_distrib,mul_add,sum_add_distrib]

lemma traveler (hp : ∀ i:Stars, PanelQuality B (f' i) (q i)) (ht : w+4≤z) (x:Site c):
    B.Regular (neighbors z x) (Trio.ornament Q f' x) ∧ B.supBounds x (neighbors z x) (Trio.ornament Q f' x) (oroW B z (fun i=>2*q i)):= by
  rw [Trio.orchard]; let p i:= Boulevard.stillA (Trio.froth (f' i))
  have hh i:B.Regular univ (p i):= CouplingShape.reg_sub (hp i).1 (CouplingShape.reg_const _)
  have hz i (j:Site (Y i)): separation x (Slide.sites (Trio.pad Q i) x j)≤z:= (Slide.village (C:=Y i) (w:=w+i.val) (Q i).ge _ _).trans (by have hk := i.isLt; omega)
  have hR i := CouplingShape.reg_scale (Slide.ray i) (Slide.regular (pad Q i) x (hh i) fun j=> ((neighbors_mem ..).2 (hz i j): _∈ neighbors z x))
  refine ⟨Meadow.regularA _ (fun i _=> hR i), Trio.sup_S B _ _ _ _ x (fun i _=>hR i) ?_⟩
  have hu {c:Side}:flags B.threshold (1:Config G c)=∅:= smoky (P:=B) (by intro i; simpa [Gauge.chord,faceValue,square,travel,Lattice.Step.read, posDir, negDir] using B.threshold_pos)
  intro i _; apply CouplingShape.sup_scale _
  have hv: ‖Trio.froth (f' i) 1‖≤ q i:= (hp i).2 1 hu [] (Nat.zero_le _) (by simp)
  have hq:0≤ q i:= (norm_nonneg _).trans hv
  refine ⟨mul_nonneg (by unfold Trio.tilt; positivity) (by positivity),fun V hY l he hd=>?_⟩
  let U := Slide.shape (pad Q i) x V; have hK:= Trio.hint Q z V i ht x hY
  have hW: Healthy B.threshold univ U:= by unfold Healthy; rw [show flags B.threshold U=∅ from hK]; simp
  apply Slide.stalled (pad Q i) x (p i) (hz i) l V he hd ((hh i).smooth _ hW)
  let f'':= Trio.froth (f' i); let g (_ : Config G (Y i)):= f'' 1
  intro v hv' hZ; change ‖leftDerivs (f''-g) v U‖≤ _
  rw [VerifiedReset.left_sub ((hp i).1.smooth _ hW) ((show B.Regular univ g from CouplingShape.reg_const _).smooth _ hW) hv']
  have ho : ‖leftDerivs g v U‖≤ q i:=by
    cases v <;> simp only [g,Work.G07.left_const]; · exact hv
    simpa using hq
  exact (norm_sub_le ..).trans ((add_le_add ((hp i).2 U hK v hv' hZ) ho).trans_eq (two_mul _).symm)
end morph
set_option quotPrecheck false
local notation "b!" => Trio.tent k B.B
local notation "d!" => Trio.base k B.B
local notation "c!" => Trio.fence k B.B
def locator (b:ℕ)(P:BudgetPoint) (w:ℝ):= oroW P (Trio.base b P.B) (fun i=>2*((Fintype.card (Site (Trio.fence b P.B i)):ℝ)*w)) * Real.exp (preExponent P*coverTicket b)

lemma prayer {w:ℝ} (Q:∀ i:Stars,(c! i).val=2*(b!+i.val)) (f':∀ i:Stars,Trio.Offer G (c! i)) (hp:∀ i:Stars,PanelQuality B (f' i) ((Fintype.card (Site (c! i)):ℝ)*w)) :
    Meadow.Budget B (Marlin.leap d!) (Trio.ornament (c:=c) Q f') (locator k B w):= by
  let v i:=2*((Fintype.card (Site (c! i)):ℝ)*w); let p:=oroW B d! v
  have hh (x:Site c):= traveler B Q d! f' hp (show b!+4≤d! from by unfold Trio.base; omega) x
  have h : 0 ≤ p:= (hh 0).2.1
  refine ⟨fun _=>p,fun i=>?_,hh⟩; apply budget_finite
  · intro i; split; exact mul_nonneg h (Real.exp_pos _).le; rfl
  rw [Finset.sum_eq_single i]; rw [if_pos (show (Marlin.leap d! i).site=i from rfl)]
  · apply mul_le_mul_of_nonneg_left _ h; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ (headline B|>.exponent_pos.le); unfold coverTicket; apply Nat.cast_le.mpr; apply (Trio.scaleMeters k B.B B.B_pos i d! (by omega)).trans; rw [two_mul]
  · intro j hj he; exact if_neg he
  simp
end YM.RGLocalTaylor.Read.Pane
