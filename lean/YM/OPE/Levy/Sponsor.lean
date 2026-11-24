import YM.MergeProof.North.Bardo
import YM.OPE.Columns.Bank
import YM.OPE.Levy.Lodging
import YM.MergeProof.West.Commerce
/-! Adapted from `YM.MergeProof.East.sponsored`, see East.Gran. Adds the receipts of `Levy.Lodged`. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open PhysicalNext.Repeat.Legato.Bandage
open Org Spec Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}{C:Family G}{d n D k N p m:ℕ} {W:Bid.Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
open Supply Accent
variable {T : Sheet G}{D': Rolls T} {E : Protection D'} {T' : Delays E}{K : Bar T'}
lemma sponsored_plus (hG:G.Simple)(B:MapPrices)(O:HaarBudget G)(J:ChartRatio G)(hx:LocalRatio J) (u:ℕ→ℕ)(h:RelayP T B u) (hu:∀ i,u i ≤ (D'.L i).val) (U:Wait K) :∃ V:Wait K, U.minLength ≤ V.minLength∧U.readyHere ≤ V.readyHere ∧ U.window ≤ V.window ∧ ∀ C:Family G,Paid V C.path.levels→∀ H: Binding C,H.prices=B→ C.Makes→ParadeX C→∀ (W : Worth)(a b c e r L),Scrim C W a b c e (fly C.path.levels) r L→∀ F,_root_.YM.OPE.Levy.Stocked C F:=by
    obtain ⟨b,P,ht,hP,hK⟩:=h.buys
    let Z j:= ∑ i∈Finset.range (j+1),Accent.generator G i
    have he(i):0 ≤ Accent.generator G i:=by unfold Accent.generator; positivity
    have ho i: 2 ≤ trays i:= Nat.le_add_left ..
    obtain ⟨V,P',h1,h2,h3,hC,hA,hB⟩:= y_stead B O J hG hK (μ:=Z) (fun i=>Finset.sum_nonneg fun j _=> he j) ho hu hx U hP
    refine ⟨V,h1,h2,h3,fun C hL H hz hM hu W a b c e r L hE f N D R hT hS hR=>?_⟩
    let d:= max N D
    have he':∀ i≤d,generator G i≤Z d:= fun i hi=>Finset.single_le_sum (fun j _=> he j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    obtain ⟨c',ht⟩:= ht d; rw [hC,hC,hC] at ht
    have hv : ∃ᶠ j in atTop,∃ Y, Poised (P' d) H hM O J (trays d) (Z d) j Y := by
       refine ((hB C hL H hz d).and_eventually (staging (n:=trays d) (z:=Z d) (P' d) H hM O J hG 0 hu (hA d 0))).mono fun i h => h.2 h.1.limit h.1.aisle
    obtain ⟨V,hV,hV'⟩:= _root_.YM.OPE.Levy.receipt (F:=f) (P' d) H hM hG hE O J _ he' (ho d) R hR hT hS ht hv
    exact _root_.YM.OPE.Levy.shrink_witness V hS f hV (le_max_right ..) ((le_max_left ..).trans (Nat.le_add_right ..)) hV'
end YM.MergeProof.East
