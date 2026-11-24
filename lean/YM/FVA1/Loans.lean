import YM.FVA1.CashRun
import YM.FVA1.Reprice
import YM.FVA1.Widen

/-! Consumer at the post-block expenses (supportExponent+1 at physical ledger
level; does not assert canopy receipts at independently chosen exponents).
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA1
open ConnectedActivityE6 Shell Blaze
open Thermal1020 Shared
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
open Marker Push.GridApprox.Nil Merge.Photo MergeProof Accent
open Overlay.GapsLocal Trees Captain
variable [DecidableEq ι](M':ι→Leaf R)(rA:ι→ℝ) 

set_option quotPrecheck false
local notation "E'"=> FreeCensus ι
local notation "b'" => (ink (ι:=ι))
local notation "w'" => (1:ι→ℝ)
local notation "ρ'"=> horizonRadius G L s
local notation "Y'"=> fun i=> (M' i).crest.image S.ratio.parent
set_option quotPrecheck false
variable (H:Cash W s μ L Q o C T R)(E0: RG.Rep G c)(K: ℝ→Finset ι→Ovens.Code G c)
  (m:ℕ)(levels:ℕ→Prop)

local notation "Y0"=> cards (χ:=Chi.canonical) M' rA H K m levels
variable {B b d a C' v Y r q :ℝ}{Γ:Target.Expense Q}{F':RG.Stage}
    (N:Captain H (F':RG.Stage).order C' d v Y a b r B q k Chi.canonical)
    {dk ex:ℝ}(h:Photo.Usable M' H Chi.canonical E0 rA K dk ex (PhysicalNext.Repeat.Mallow.straw μ L G s))
    (hc:Palette.Thermal.BuysMix M' H rA) (ht:Thermal1020.Shared.MixReceipt Γ F' m N)
include M' rA h N hc ht
lemma margin_loan (hf:ℕ)(he:∀ i,levels i → hf ≤ i)(hP:E0.p.B=radiusB s)(hR:E0.p.order ≤ F'.order)
    (hJ:E0.p.power=F'.power) (hB:E0.p.supportExponent+1 ≤ Γ.earn)
    (hZ:Motion.Pays E0.activities (Marlin.raiser E0.p) K (PhysicalNext.Repeat.Mallow.straw μ L G s) (E0.p.supportExponent+1)) :
    (Y0).Lent E0 w' (E0.p.supportExponent+1) ((ρ'^hf)⁻¹) (PhysicalNext.Repeat.Mallow.straw μ L G s):=by
    have he': Sailor G E0.p.threshold q F'.order:= ⟨fun i v hv=> N.weigh.stroke i v (hv.trans (h.temp.symm ▸ N.talent))⟩
    have hV(i:ι): 0 < (w') i:=zero_lt_one
    have hw(i:ι):Poly.price w' (ink i)≤1:=by unfold ink; rw [Poly.solo,Poly.solo_toll,norm_one]; exact (mul_one (1:ℝ)).le
    refine ⟨hV,le_add_of_nonneg_right zero_le_one,⟨fun i=>priceAt N M' rA b' i levels ρ' m E0.p,fun i z=> price0 N M' rA b' i levels hc _ _ z ((by norm_num: (0:ℝ)≤ 2).trans ht.large), ?_,?_⟩,Photo.flag_K (P:=Marlin.raiser E0.p) E0 K E' b' w' hV hw hZ (add_nonneg E0.p.exponent_pos.le zero_le_one)⟩
    · intro x
      refine budget_loosen (cappedPrices N M' rA b' levels w' hV hw hc m Γ E0.p hP ht.Warn ht.large ht.book ht.meet ht.funds hf he _ hB x) ?_
      apply mul_le_of_le_one_right (by have hz:=ht.large; positivity)
      rw [hJ]; exact ht.expCredit
    intro i z x hx
    change E0.p.supBounds x (reachability i) (if _ then _ else _) _; split
    next hz=>
      have hy:0≤priceAt N M' rA b' i levels ρ' m E0.p z:=price0 N M' rA b' i levels hc m E0.p z ((by norm_num: (0:ℝ)≤2).trans ht.large)
      have hz':= regular_bound_sum (G:=G) (P:=E0.p) (s:=reachability i) (o:=x) (∅:Finset Unit) 0 0 (fun i hi=> False.elim (notMem_empty _ hi))
      have hv:E0.p.supBounds x (reachability i) (0 : Config G c→ℂ) 0:=by simpa only [sum_empty] using hz'.2
      exact ⟨hy,fun U hu l hl hh=> (hv.2 U hu l hl hh).trans hy⟩
    next _=> exact (premium N M' rA b' i levels hc ht.shared ht.turns ht.large ht.chargeFits E0.p h.temp hR hP he' x hx m z).2
end YM.FVA1
