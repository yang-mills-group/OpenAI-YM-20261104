import YM.RGLocalTaylor.Laminate.Edit
import YM.MergeProof.Garden
/-!
# Purchase on actual Volant Plot. No stricter cost on user Hats than need
 through the certified path. Same exponent and support totals at output in
 health, and real estimates on marked Hats (incl coincident stretches) before
 any switch or derivative queries. -/
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
open Blaze.March
namespace Laminate
open RG01.Survive Mayer Trees
open YM.Merge Palette

variable {ι: Type} [Fintype ι] (M':ι→Leaf R) (rA:ι→ℝ) (Ξ : Utopia H j v d r C' χ) (hP:Palette.Plot M' H rA)
    {α ρ e uJ vJ discount θ K : ℝ} {p : Molecule S}
set_option quotPrecheck false
local notation "X₁" => Q.costs L μ R.beta s C'
local notation "Y₁" => Daisy.swing Q L μ R.beta s C
local notation "G'" => H.birth
local notation "d!" => ConnectedActivityE6.lengths T R

-- controlling not only all Pitch marks but also all analytic moments with envelope `Ξ`. reuse full reserve `η` before paying geometry. unchanged battery powers size of support.
def banks (Q:ConnectedActivityE6.Target G P) (L: Side) (μ R s C:ℝ): Mixed.Costs:=
  let c:=Q.costs L μ R s C
  let d:=(swing Q L μ R s C).optionalHit
  { c with optionalHit := c.optionalHit+d, rootHit := c.rootHit+d, q:=1/2 }
local notation "X" => banks Q L μ R.beta s C'

def projected (H' : Utopia H j v d r C' χ) (i : ConnectedActivityE6.Alphabet c f) := H'.flair i + Tickets.extra (Palette.mark M' (c:=c)) (Palette.wages M' rA) i

def projectedWeight (H' : Utopia H j v d r C' χ) (i : Head S) := H'.fare i+Tickets.extra (Palette.sign M' S) (Palette.wages M' rA) i

lemma stepsWeight : projectedWeight M' rA Ξ=Mixed.costs S Q.halo (radiusB s) (steamP S X₁) (projected M' rA Ξ) := by
  funext i; unfold projectedWeight; rcases i with i|i
  · rw [show Tickets.extra _ _ (Sum.inl i)=_ from (show Tickets.extra (Palette.sign M' S) (Palette.wages M' rA) (Sum.inl i)=0 from ?_),add_zero]; · rfl
    unfold Tickets.extra; refine sum_eq_zero (fun j _=>?_); rw [if_neg]; exact fun hh=> by have hk := (Daisy.sparkPath (M' j).turn S).trans hh; contradiction
  change Ξ.flair i + _=projected M' rA Ξ i; unfold projected; congr 1
  unfold Tickets.extra Palette.sign Palette.mark; simp_rw [← Daisy.sparkPath]; simp only [Sum.inr.injEq]

include hP
lemma wage_pos (i:ι):0≤ Palette.wages M' rA i:= mul_nonneg (hP.live _) (M' i).profit
lemma ticket_pos {i}:0 ≤ Tickets.extra (Palette.sign M' S) (Palette.wages M' rA) i:=
    Finset.sum_nonneg (fun j _=> by split; exact wage_pos M' rA hP _; rfl)
lemma projected_pos (i): 0 ≤ projectedWeight M' rA Ξ i:= add_nonneg (Ξ.fares i) (ticket_pos M' rA hP)

lemma qualifies : Mixed.Accounts S Q.halo (radiusB s) X H.birth (projected M' rA Ξ) d! (steamP S X₁) := by
  let F:= Tickets.extra (Palette.mark M' (c:=c)) (Palette.wages M' rA); let X0:=X
  have hp (i:ConnectedActivityE6.Alphabet c f):0≤ projected M' rA Ξ i:= by
    have hh:=projected_pos M' rA Ξ hP (Sum.inr i); rw [stepsWeight] at hh; exact hh
  refine ⟨Ξ.accrues.packetBound,hp,Ξ.accrues.extra,?_⟩
  intro i; have hv:=budget_plus (Ξ.accrues.pays i) (hP.pays.pays i); refine budget_mono hv (fun j=>?_) fun j=>?_
  · split; exact mul_nonneg (mul_nonneg (hp _) (Real.exp_pos _).le) (Real.exp_pos _).le; rfl
  split
  next hg=>
            unfold Reserves.tariff
            let d(j:ConnectedActivityE6.Alphabet c f):= H.opt j
            let t:= Real.exp (2*Q.ε*(d! j)+0); let a:= Real.exp ((X0.head)*coverNumber (radiusB s) (H.birth j))
            change (Ξ.flair j+F j)*t*a≤ Ξ.flair j*t*a+(H.opt j+F j)*t*a
            have h:0≤ H.opt j*t*a:=mul_nonneg (mul_nonneg (H.earns _) (Real.exp_pos _).le) (Real.exp_pos _).le
            linarith only [h]
  next hg=> simp only [add_zero,le_refl]

include Ξ
omit hP in
lemma cashier (h: degreePrice (radiusB s) (X).rootHit Q.δ ≤ 1/2) : (X).Buy S.patch.L Q.halo (radiusB s):=
  { Ξ.lives with
    γ := Ξ.lives.γ.trans_le (le_add_of_nonneg_right (add_nonneg (Daisy.arable H).le (mul_nonneg (Daisy.arable H).le (Real.exp_pos _).le)))
    combined:= (Eq.le (add_assoc ..).symm).trans (add_le_add_left Ξ.lives.combined _)
    trees:=h
    grows:=by change (1/2:ℝ)<1; norm_num }

abbrev width (Q:ConnectedActivityE6.Target G P)(μ : ℝ)(L: Side)(s: ℝ):= (banks Q L μ 1 s 0).rootHit
lemma rich (h : degreePrice (radiusB s) (width Q μ L s) Q.δ ≤ 1/2) : Ready H.supportP (radiusB s)
    (Reserves.tariff (projectedWeight M' rA Ξ) (Mixed.lengths S X₁ d!) (fun i=>Q.mark L μ s * Mixed.shares S i) Q.ε) (Q.exp+2*Q.ε)
    (width Q μ L s) Q.δ (1/2):= by
  rw [stepsWeight]; exact Mixed.ready_vertices S Q.halo (radiusB s) X G' (projected M' rA Ξ) d! _ (cashier Ξ h) (qualifies M' rA Ξ hP)
end Laminate
end YM.RGLocalTaylor
