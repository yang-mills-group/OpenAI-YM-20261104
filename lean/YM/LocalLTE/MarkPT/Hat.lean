import YM.LocalLTE.MarkPT.Sale
import YM.LocalLTE.Port.Gems
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
variable (κ:ℝ)(v:ℝ)(K:ℕ)(hk:Reliable G κ v)
-- coefficient piece from localized stencil. Kept if actually profitable. ordinary (all U.W.Wt as inserted).
local notation "F₀"=> forecastPT M H χ q n r₀ A' Φ Ψ X hp κ m d
local notation "X'"=> (fun i:Stars H M=> Fan.frontArtPT M H q l X i hX)
local notation "T!"=> fitsP M H q n r₀ A'
include hX
noncomputable def resMode (hX: East.stagnate q Q.halo*radiusB t < l*radiusB t) (u:Weft.J K × Fin d)(i: Stars H M):Pot G c:=
    if T! i ∧ Fan.Enter M H i then Price.banner (frontArtPT M H q l X i hX) (F₀ i) κ u.1 u.2 else 0
-- check include hX.D.Order; API.
noncomputable def stdMode (hX:East.stagnate q Q.halo*radiusB t < l*radiusB t) (s:ℝ)(u:Weft.J K × Fin d) (i:Stars H M): Pot G c:= Weft.mark K u.1 s • resMode M H χ q n r₀ A' Φ Ψ l X hp d m κ K hX u i
local notation "Z₁"=> resMode M H χ q n r₀ A' Φ Ψ l X hp d m κ K hX
local notation "μ'"=> stdMode M H χ q n r₀ A' Φ Ψ l X hp d m κ K hX
variable {U D₁:ℝ} (hQ: PlumPT M H χ q n r₀ A' Φ Ψ l X hp hX ε w p s d m K κ U D₁) (hP:p.B=radiusB t)
local notation "Υ"=> Weft.J K × Fin d
-- does not need truth Φ-evaluated except separate; all sectors ≤p. actual contributions with **full padded roster** same.K power after exponent.Normal.$ identify K.D.
def pegCost (u:Weft.J K ×Fin d):= ((K:ℝ)-(u.1.val:ℝ)- (u.2.val:ℝ))/2
local notation "t'"=> (1+(l*radiusB t:ℕ):ℝ)^(p.power*p.order)
include hk hQ
lemma modeSum (s':ℝ)(hs:s'∈Weft.clip) : (fun i=> F₀ i s') = ∑ i: Υ, μ' s' i:=by
    funext i; rw [Finset.sum_apply]; by_cases he: T! i ∧ Fan.Enter M H i
    · obtain ⟨a,ha,hA⟩:= hQ.receipts; have hx:= ((hA i).2 he).isScene
      have hu: ((fun v:Υ=> μ' s' v i))=fun v:Υ=> Price.stub (X' i) (F₀ i) s' κ v :=funext fun v=> (by unfold stdMode resMode; rw [if_pos he]; rfl)
      have he' v (hv:v∈Weft.clip): p.Regular ((locationPT M H l i).support) (F₀ i v):=by unfold forecastPT; rw [if_pos he]; exact VerifiedReset.reg_larger (FrameBox.legal _ _ hk _ p) (Price.color_site (X' i))
      rw [← hu.symm,Fintype.sum_prod_type]; exact Price.advance (X' i) p (F₀ i) hk he' hx hs -- rewrite?
    rw [sum_eq_zero]; · exact if_neg he
    intro j _; unfold stdMode resMode; rw [if_neg he,smul_zero]
local notation "X!"=> portfolio M H χ q n r₀ A' Φ Ψ l X hp m d K κ hX
omit hk hQ
lemma segment (x:ℕ) : X! s x= ∑ i∈ (Finset.univ: Finset Υ).filter (fun i=> Price.genre i≤ K+x), μ' s i:=by
     funext i; rw [Finset.sum_apply]; unfold portfolio; split
     next hh=>
        unfold Price.coverPT; apply Finset.sum_congr rfl; intro j h; unfold stdMode resMode; rw [if_pos hh]; rfl
     next hh=>rw [sum_eq_zero]; intro j _; unfold stdMode resMode; rw [if_neg hh,smul_zero]
include hk hQ hP
lemma treetop (u:Υ): let t:= Y'^(pegCost d K u+ε); let C:=(t*t')*D₁; let f:= μ' s u; GrowsP M H p Z' w U C f Z'∧(Price.genre u<K→ Z₁ u=0):=by
    intro t0 C f'; obtain ⟨a,hA,h⟩:= hQ.receipts
    let W':= t0*t'; have hw:0≤ W':=mul_nonneg (Real.rpow_nonneg (show 0≤Y' from ?_) _) (by positivity) -- hP from hQ? β≥1 not hyp.need input
    · let X0:= (univ:Finset (Weft.J K × Fin d)); let F(i:Stars H M): Prop:= T! i ∧ Fan.Enter M H i
      have hx (i:Stars H M)(hi:F i): p.supBounds (locationPT M H l i).site (locationPT M H l i|>.support) (f' i) (a i * t0):=by
          unfold f' stdMode resMode; rw [if_pos hi]; exact (((h i).2 hi).rebates u.1 u.2|>.2)
      refine ⟨⟨fun i=>W'*a i,fun i=>mul_nonneg hw ((h i).1),fun i=>?_,fun i=>?_⟩, ?_⟩
      · by_cases ht:F i
        · let X0:= Z' i; have hy: Z' i= (locationPT M H l i|>.support):= if_pos ht.1; have hP: p.Regular (Z' i) (f' i) := by unfold f' stdMode resMode; rw [if_pos ht,hy]; exact AnalyticBridge.CouplingShape.reg_scale _ (play_cost _ p hk _)
          refine ⟨hP,fun j hj=>?_⟩; rw [hy] at hj⊢; have hh:= Fan.spokeR p (b:=(1+(l*radiusB t:ℕ):ℝ)) (y:=j) (o:=origin M H i) (by gcongr; exact (neighbors_mem ..).1 hj) (hx i ht)
          exact sup_le hh (le_of_eq (by unfold W'; ring))
        rw [show f' i=0 from (by unfold f' stdMode resMode; rw [if_neg ht, smul_zero])]; exact ⟨reg_const _,fun _ _=> sup_le (sup_const 0) (abs_zero.trans_le (mul_nonneg hw (h i|>.1)))⟩
      · rw [hP]; convert budget_scale hw (hA i) using 1; funext i; split <;> ring
      intro ht; funext i; unfold resMode; split
      next hv=> exact Price.quota _ _ _ _ _ ((h i|>.2 hv|>.rebates u.1 u.2).1 ht)
      next=> rfl
    have hz:= H.laws.intake; have ht:0 < R.beta:=hz.positive; have hβ:=hz.window.2; rw [H.laws.data.funds.length_eq] at hβ; linarith
end YM.LocalLTE.Fan
