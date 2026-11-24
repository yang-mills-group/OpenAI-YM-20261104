import YM.LocalLTE.MarkPT.Gent
/-! Orbit-shared explicit mark proposal. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalLTE.Fan
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open ConnectedActivityE6 ConnectedActivityE6.Blaze Blaze.March Captain Mask Raw Matter Frond Coat Vine
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Gate Scroll Vine Tablet Metric Poll Flux Shield Pond Raw
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
open Brush Foramen
variable {v z r W w s t y η γ B a μ: ℝ} {j n m : ℕ} {Q: YM.ConnectedActivityE6.Target G P}{o: Target.Order G W}{R:Rep G f}
open PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open FrameBox Pastel Merge Merge.Palette

open Merge.Palette Gas Ursell Bakers
open Greenbelt
set_option quotPrecheck false
attribute [local instance] Gauge.frobInner
variable {ι:Type}(M:ι → Lotus.Leaf R) (φ:ι→ Config G f→ℝ) (H:Cash W t μ L Q o a T R)(χ:Chi)
-- Every label.Energy in θ ledger same geometry.T.Z.T.Tag projection Ward.
local notation "Oz"=> Merge.Tickets (Merge.Palette.sign M S)
local notation "Y₀"=> radiusB t
variable (z:H.fragrances)(D:Captain.Oscars M z) {θ ι' J:ℕ}
-- parity.Y allele tall cone factor.Deferred.B.Gouge.
local notation "Ux"=> (fun k=> z.snd k)
local notation "U₀"=> Captain.reachability (H:=H) z
local notation "M₀"=> (fun i=> East.docket H z i)
local notation "q₀"=> (fun k=> Captain.quietR M (z.2 k) (D k))
variable {α C B' v₁ d v₀ e A β κ :ℝ}(q n k :ℕ)(r₀:ℕ→ℕ)(A':ι→Prop)(hx:Candor M z D q n r₀ A')
variable (Φ:ℕ→ℝ→ Config G f→ℝ)(Ψ:ι→ℝ→ Config G f→ℝ)
open Weft
open East FrameBox
-- once planning.L. $radius.A.Messages. Photo rebate. anchored per-slot. No adapters lean type.This supply supports ANY derived petals. Calendar explicit strong.Q.P
open AnalyticBridge VerifiedReset Collection Price
variable {κ K v:ℝ}
variable (l:ℕ)(X:(i:Stars H M)→Grove (origin M H i))(hp:2*(2*(East.stagnate q Q.halo*radiusB t))≤ c.val) (hX: East.stagnate q Q.halo*radiusB t < l*radiusB t)
variable (ε:ℝ)(w:ι→ℝ)(p:BudgetPoint) (s:ℝ) (d m Pk:ℕ)
-- Full native denominators. supplies
local notation "U'"=> East.stagnate q Q.halo*radiusB t
local notation "Z'"=> sitesP M H q n r₀ A' l
local notation "Y'"=> betaF G t L
-- while using forecasts, can charge ``blank`` K coefficients, *NOT THE ACTUAL K*.
open Merge.Photo Merge.Motion Marker Overlay Next.Foundations Progress.DirectedRecipe
variable {E:Type}[DecidableEq E] (Qt: Marker.Census E) [Fintype ι] (kp:ι→Poly Qt)(wp:E→ℝ) (hw:∀ i,0<wp i)
    (hc:∀ i,Poly.price wp (kp i)≤1) (b:E→Site c) (i:E) (P:Rep G c)
local notation "X0"=> sitesP M H q n r₀ A' l
local notation "QX"=> ghost M H q n r₀ A' w l P Qt kp b i
local notation "T" q=> (QX q)
variable (f': Stars H M→ Config G c →ℝ)
variable {U V ν:ℝ}
local notation "ℓ"=> (Fan.offerC M H X0 Qt b)
local notation "r"=> (Fan.tapsC Qt)
open Overlay Marker
variable (κ:ℝ) (K:ℕ) (u:E→ℂ)
local notation "F!"=> (portfolio M H χ q n r₀ A' Φ Ψ l X hp m d K κ hX)
local notation "TX"=> East.stagnate q Q.halo*radiusB t
include hX
omit hX [Fintype ι] in
private lemma bonusQ {α:Type} (x:Stars H M) (z:ℕ)(F:Finset α){x':α→ Config G c→ℝ}(hp:∀ i∈F,Replicated (X x) (TX) κ (z+1) (x' i)) : Replicated (X x) (TX) κ (z+1) (∑ i∈F,x' i):=by
   induction F using Finset.induction_on with
   | empty=> exact rp_zero _
   | insert i F he ih=> rw [Finset.sum_insert he]; exact rp_add _ (hp i (mem_insert_self ..)) (ih (fun j hj=> hp j (mem_insert_of_mem hj)))
lemma focusG (p':ℕ)(z x:ℕ)(hv: d≤ p'+1) (ht:l*radiusB t≤ z): Port.Shine Qt (Port.augment (T (F! s x)) u) p' z κ:=by
    constructor; intro j; let a:= F! s x; let c0 := QX a
    change c0.H j≠0→ _; intro hi
    let Sz:=X0; let v:= offerC M H Sz Qt b
    have hj:j∈Set.range v:=by by_contra H; exact hi (by dsimp only [c0,ghost,opalescence]; exact Progress.DirectedRecipe.blank _ _ H)
    obtain ⟨j,rfl⟩:= hj; let P':= (fun (_:ℝ) (_:Finset ι)=> (0: Ovens.Code G c))
    obtain ⟨hh,-,hY⟩:= Fan.shelf M H w a X0 Qt kp b i P P' j
    let J':= j.val.1; let sZ:= origin M H J'; let VZ:= X J'
    let Z:= Fan.chimes M H w a Qt kp j.val.1 j.val.2
    have hy: c0.H (v j)=Z:=hY
    have hx:a J' ≠ 0:= by
       intro hx; rw [hy] at hi; apply hi; unfold Z Fan.chimes; rw [show a (j.val.1)=0 from hx, show Complex.ofReal ∘ (0:Config G c→ℝ)=0 from funext (fun _=> Complex.ofReal_zero),smul_zero]
    have hh':fitsP M H q n r₀ A' J' ∧ Fan.Enter M H J':=by unfold a portfolio at hx; split at hx; assumption; exact False.elim (hx rfl)
    let S0:=l*radiusB t; have hS: (Port.augment (T (F! s x)) u).support (v j)=neighbors S0 sZ:= hh.trans (if_pos hh'.1)
    let T0:= TX; have hcT: Replicated VZ T0 κ (p'+1) (a J'):=by
        unfold a portfolio; rw [if_pos hh']; unfold coverPT; apply bonusQ -- binder order!
        intro i hi; exact rp_scale _ _ (Price.rp_raise _ (show Price.Replicated VZ T0 κ (i.2.val+1) _ from ⟨_,rfl⟩) (le_trans (show i.2.val+1≤d from i.2.isLt) hv))
    rw [hS]; refine ⟨sZ,(neighbors_mem ..).2 (by rw [separation_self]; omega),fun i hi=> (neighbors_mem ..).2 (((neighbors_mem ..).1 hi).trans ht),T0,hX.le.trans ht,VZ,fun i=>?_⟩
    change ∃ S,Port.scaleQ i ∘ (c0.H _)=_
    rw [hy]; let W:=(Fan.barry M H w Qt kp J').part j.val.2
    have he: Port.scaleQ i ∘ Z=(Port.scaleQ i W) • (a J'):= by funext U; change Port.scaleQ i (W*(↑(a J' U):ℂ))=_; cases i<;>simp [Port.scaleQ,Complex.mul_re, Complex.mul_im]
    rw [he]; exact Price.rp_scale _ _ hcT
end YM.LocalLTE.Fan
