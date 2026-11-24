import YM.QuadraticLocal.Lane
import YM.QuadraticLocal.Glow
import YM.RemainderComparison.Creek.Icing
import YM.RemainderComparison.Denom.Release
/-!
Same-vacuum raw marked step. Supply unmarked reclosure's mass identity (any
particular pre-Rep or after extending `ReadZone` across exact flag mergers), positive actual path
and no holes in construction-History; then no need to recover precise kinetic/scalar/extraction
alignment at each tidying operation ALTHOUGH it has been done by the unmarked supplier. Bind
factor unambiguously by the actual pushed unmarked term, **not a C bound**, since gas at this point
won't vanish anywhere for use along trajectory. For the more general one-step proposition even
without History positivity use exact exponent identities instead.

This focuses on the SAME vacuum here, throughout flag passages later in particular. Integrability
used for the harmless quiet projection, then only on actual coupling with actual vacuum. The sector
conditional analytic denominator in the Fk terms is separate.

RemainderComparison.Lane.Gas after two mergers isn't picked anew by this lemma; its weights need to
stay within true construction and mark budgets. These rates are on `Gallery`; FullBudget and masks
with repeatedly updated K and regular packet discrepancies still required, and mark inputs need to
be encoded. The projection positivity trick in `upkeep` doesn't pay any estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {V ι T0 T' : Type*} [DecidableEq V] {G:Gauge}{n:Side}{R:Census V}{o: V→Site n}
variable {p : BudgetPoint} {A:Activities G n}{x y μ σ a b δ k W : ℝ}{w:V→ℝ}

section Arches
open Fusion.Attached
variable (t:T0)(F:Config G n→Poly R)(K : Hard T0 p A.forced A.K o R) (L:Lamps T0 ι G p o R)
variable [Fintype V]
/-- A known scalar multiple; all mask moves paid at E/B and K levels separately.
Output for all unit tests, multiplier can be probed per U. `upkeep` recovers him using the
*actual vacuum term*, not Taylor-expanded or an arbitrary envelope. -/
def ReadZone (T0:Type*) (p:BudgetPoint) (A:Activities G n) (K:Hard T0 p A.forced A.K o R)
    (F:T0→ Config G n→Poly R)(log:T0 → Config G n→Poly R) :Prop:=
 ∀ t U, Summable (packet A p (K.hard t) U) ∧
   ∃ v:ℂ,F t U= v • (Poly.pass (log t U)* ∑' i,packet A p (K.hard t) U i)

variable (F:T0→ Config G n→Poly R)

lemma upkeep (X:Rep G n) (L:Lamps T0 ι G X.p o R) (K:Hard T0 X.p X.activities.forced X.activities.K o R)
    (hs:L.Paid w X.p.B a b)(ha:0≤a)(hw:∀ v,0<w v)(h:ReadZone T0 X.p X.activities K F L.log)
    (hx:∀ t U,(F t U).part R.quiet = ↑(X.eval U))(hy:∀ U,X.eval U≠0):
      (∀ t,F t=(Gallery.mk L K|>.density t)) := by
   intro t; funext U; obtain ⟨hb,v,h'⟩:=h t U
   let g : Poly R:= ∑' i,packet X.activities X.p (K.hard t) U i
   have he := hx t U; rw [h',Poly.part_smul,Poly.quiet_mul,
       Poly.pass_part _ (Lamps.quiet_of_hasSum t U (hs.sums ha hw t U)),Hard.packet_of_quiet _ t U hb,Rep.eval, Complex.ofReal_mul,one_mul] at he
   have hn: ((X.activities.gas X.p U:ℝ):ℂ)≠0:= Complex.ofReal_ne_zero.mpr (right_ne_zero_of_mul (show Real.exp _ * X.activities.gas X.p U ≠0 from hy U)); have Hv : v = ((Real.exp (X.exponent U)):ℂ):= mul_right_cancel₀ hn he
   rw [Hv] at h'; exact h'

open Ovens Ovens.Pipes Progress.DirectedRecipe RG3.Letters
variable (log:T0→ Config G n→Poly R)
variable {X:Pipes G n} {d:Tap G n}
/-- Across an **unmarked** exact flag merger. Every Quiet and nonquiet key rides. -/
lemma bridge (e:ℕ≃X.Pellet) (L:Hard T0 p X.kernel d.forced o R) (h:Hard.Soft X d p)
    (hK:L.Paid w p.B (a+1) μ)(hS:Hard.SoftPrice X d p.B (a+1) b)(hB:Payments.Rates p.B W μ b k)
    (hw:∀ i,0<w i)(ha:0≤a)
    (hZ:ReadZone T0 p (X.pours d) L F log) :
    let L':Hard T0 p (fused e p d).forced (fused e p d).K o R := (L.transport e h)
    L'.Paid w p.B a W ∧ ReadZone T0 p (fused e p d) L' F log :=by
   intro L'; refine ⟨L.paid e h hw ha hK hS hB, fun t U=>?_⟩
   obtain ⟨hx,e',H'⟩:= hZ t U; obtain ⟨hX,HH⟩:= L.carries e h hw ha hK hS hB t U
   let a' := (Real.exp (∑' i,d.logarithm i U):ℂ); have he (y:ℂ) (w:Poly R) : (y/a') • (a' • w)= y • w := by rw [smul_smul,div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))]
   refine ⟨HH.summable,e'/a',?_⟩; unfold L'; rw [HH.tsum_eq,H', mul_smul_comm]; exact (he _ _).symm

lemma passed {X Y:Activities G n}(K:Hard T0 p X.forced X.K o R){f g:ℕ ↪ ℕ}(hP:Readdress p f g X Y)
    (hZ:ReadZone T0 p X K F log) : ReadZone T0 p Y (K.readdress hP) F log:=by
    intro t U; obtain ⟨hb,u,h⟩:=hZ t U; have he:= K.readdressGas hP t U hb.hasSum; rw [he.tsum_eq]; exact ⟨he.summable,u,h⟩
end Arches
end YM.QuadraticLocal

namespace YM.QuadraticLocal.Lanes
-- Use same M and data throughout. Countable ι handles address combinations per load.
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic RemainderComparison.Muse RemainderComparison.Sleet RemainderComparison.Serif RemainderComparison.Typeface RemainderComparison.Flues
open GridRenewal.Rain
open Marker Mallow Ovens Progress.DirectedRecipe
variable {ι V' : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
variable (U:Pad H j χ) {τ κ K Y γ V T0:ℝ}
variable (M:ι→Portrait R α) (x' y:α) (l:ι→ℝ)
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto (brand M x') l 0 H τ K Y I)
local notation "Vx"=> brand M x'
local notation "Vy" => brand M y
variable {R':Rep G f} (H':Cash W x μ L Q o C T R')(D:Match.Alliance H' H 1 0)
    (P':BudgetPoint)(hp : P'.B=radiusB x) (ht:P'.threshold=Pressure.temp x)
    (E₀:ℕ→RegularAddress c)(V₀:ℕ → Config G c→ℝ)
variable [DecidableEq V']{Jm:Marker.Census V'}
local notation "Φ" => Poly Jm
variable (z:ι→Marker.Poly Jm) {gP:V'→ℝ} (hZ : Chorus Jm gP Set.univ z k)
local notation "Z"=> (Set.univ:Set ι)
local notation "F'"=> TuneR (brand M y) Z l 0 z S
-- extend Denom.Read_zero to every supported choice (not Passion orientation conditioned)
include h hh hZ
lemma quiet_tune (V: Config G f): (F' V).part Jm.quiet=(R.eval V:ℂ) :=by
    let v i:= (raw Vy (i:Drums Vy S)).paint Z (sits Z l 0) z V
    have hb:Summable v:= (Serif.input_pay Vy H χ Z l 0 U h (Typeface.outputs H M x' y l 0 hh) z hZ).summable V
    let i:= Tickets.none (Palette.sign Vy S); rw [TuneR, Poly.share hb, tsum_eq_single i] -- syntax
    · unfold v Verse.paint; rw [Poly.part_smul,Flues.cold (Set.univ) z _ (show Verse.load Set.univ (raw Vy i).letters=0 from by unfold Verse.load; rw [show (raw Vy i).letters=0 from rfl]; simp)]; simp only [Poly.one_part,if_true,mul_one]; congr 1
      rw [Verse.emit,Verse.stock,show (raw Vy i).letters=0 from rfl]; simp only [Multiset.map_zero,Multiset.prod_zero,one_mul]; exact Canon.emptyWeight Vy i rfl _
    intro j hj; unfold v Verse.paint; rw [Poly.part_smul]; suffices h : ∀ s:Multiset ι,s≠0→ (Verse.controls Z z s).part Jm.quiet=0 by
      rw [h _,mul_zero]; intro he; apply hj; apply Subtype.ext; change j.val=∅; apply Finset.card_eq_zero.mp; exact Multiset.card_eq_zero.mpr he
    intro s; cases s using Multiset.induction_on with
    | empty=> simp
    | cons k s => intro _; simp [Verse.controls,silent z hZ]

local notation "A₁"=> Creek.theater H χ M x' l Set.univ 0
local notation "Rt"=> Flues.candle M x' S
local notation "Ac₁"=> Creek.Academy H χ M x' l Set.univ 0 k
variable (h₁:P'.order≤j)(h₂:P'.power≤J)(h₃:P'.supportExponent≤a)
open RemainderComparison.WickReps
include h₂ h₁ ht hp
omit [DecidableEq V'] hZ in
lemma academy : Manor.Spinal A₁ Ac₁ Rt P' a (Y^k*γ):= by
   have h0:= Creek.mass₀ H χ U M x' l Z 0 h hh P' hp ht h₁ h₂
   have hL := Creek.mass₁ H χ U M x' l Z 0 h hh P' hp ht h₁ h₂
   exact (h0.swell hL).skim (fun i hi=> Creek.monastery H χ M x' l Z 0 hi) (by simp) le_rfl

variable {o' : V'→ Site c}
local notation "XA"=>Refrain.read H' D χ E₀ V₀
local notation "Λ"=> academy H χ U M x' l h hh P' hp ht h₁ h₂ -- note order auto-include hZ,z?
local notation "Ɓ"=> QuadraticLocal.Pane.printBulbs (R:=Jm) o' A₁ Set.univ z Ac₁ Rt Λ
variable (hc:∀ i, Push.Corrected.Width.LocalCharge (G:=G) P' o' (Flues.candle M x' S i) (fun _=> z i)) [Countable ι] [Fintype V']
local notation "P0"=> layoutK H χ U M x' l h hh H' D P' hp ht E₀ V₀ z hZ hc
include hc h₃
lemma takes (A:Tree.Forest S.ratio) : (Ɓ).Paid gP P'.B a (Y^k*γ) ∧
    ReadZone α P' XA P0 (fun t=> S.push R.beta (TuneR (brand M t) Set.univ l 0 z S)) (Ɓ).log := by
    refine ⟨ QuadraticLocal.Pane.lightsPaid _ A₁ Z z Ac₁ Rt Λ hZ, fun t W'=>?_⟩
    let g i:= Serif.glyph (brand M t) H χ Z l 0 z i W'
    have hℓ:GridRenewal.Rain.fresh (∑' i,g i)=(Ɓ).log t W':= by
       rw [QuadraticLocal.Pane.lit o' A₁ Z z Ac₁ Rt Λ hc t W' hZ h.price.visit.posts, WickReps.Manor.basin,tsum_subtype_eq_of_support_subset]
       · exact congr_arg _ (tsum_congr fun i=> (Creek.stony H χ M x' t l Z 0 z P' i W' ht).symm)
       exact fun i hi=> (show i∈ Ac₁ from by_contra fun hh=> hi (Creek.onCampus H χ M x' t l Z 0 z hZ P' i W' hh))
    let b:= overhead (prism T x χ o.K W' A) R Q.table
    let a:= (∑' i,g i).part Jm.quiet
    let v: Poly Jm:= ∑' i,Fusion.Attached.packet XA P' ((P0).hard t) W' i
    obtain ⟨hB,hL⟩:= Lanes.carries H χ U M x' l h hh H' D P' hp ht E₀ V₀ z hZ hc h₁ h₂ h₃ A W' t -- ht shadow
    refine ⟨hB,(b:ℂ)*Complex.exp a,?_⟩
    change S.push R.beta (TuneR (brand M t) Set.univ l 0 z S) W'= _; rw [hL]; change (b:ℂ) • (GridRenewal.Rain.cyclone (∑' i,g i) * v)=_
    rw [GridRenewal.Rain.power,hℓ]; rw [mul_assoc]; simp only [GridRenewal.Rain.bead, Poly.product_bead,smul_smul]; rfl

omit hc ht hp h₂ h₃ h₁
omit [Fintype V'] in
lemma tunePush (V:Config G c):
    (S.push R.beta (TuneR (brand M y) Z l 0 z S) V).part Jm.quiet= (↑(S.push R.beta R.eval V :ℝ):ℂ):=
 Denom.from_base S R.beta _ V (quiet_tune H χ U M x' y l h hh z hZ) ((Serif.ingress Vy H χ Z l 0 U h (Typeface.outputs H M x' y l 0 hh) z hZ).1) (S.isKernel (funds_branch H.laws.intake.ready) _)
end YM.QuadraticLocal.Lanes
