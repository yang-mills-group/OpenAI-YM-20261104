import YM.RG12SharpGram.Weak.Plateau
import YM.MergeProof.East.Gran

/-!
# Nearby-scale rank allocation

Combining the actual Poised-station producer with the new plateau lemma.
No need for a forecast from *beyond* the initial cutoff. The resulting
stations will also be used in cost estimates on the actual UV path.
-/
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
open Supply Accent
variable {G:Gauge}

structure RG12Relay (X : Supply.Sheet G)(B:MapPrices)(k:ℕ→ℕ) : Prop where
   buys : ∃ b:ℕ→Finset ℕ, ∃ Y:∀ d,Fin 3→ Tapes.Panel d,
     (∀ d, ∃ ξ, Checks (Y d 0).arc (Y d 1).arc (Y d 2).arc ξ (trays d) d) ∧
     (∀ d,∀ᶠ i in atTop,d∈ b i)∧Fortified X B trays Y b k
lemma rg12_posters (X:Supply.Sheet G)(B:MapPrices)
    (ht:Tendsto (fun i=>(X.profile i).order) atTop atTop):∃ k,RG12Relay X B k:=by
    choose a ha hp using fun d=>raises d (trays d)
    obtain ⟨k,N,P,hK,hV,hB⟩:= y_poster X B a ha _ (fun _=> Nat.le_add_left ..) ht
    refine ⟨N,⟨k,P,fun i=> ?_,hK,hB⟩⟩
    have h := hp i; simp only [hV]; exact h

variable {T : Sheet G}{D : Rolls T} {E : Protection D} {T' : Delays E}{K : Bar T'}

abbrev ParcelPrice (G:Gauge)(z:ℕ):= ∑ i∈Finset.range (z+1), generator G i
lemma parcelCost (i d:ℕ)(hi:i≤d): generator G i ≤ ParcelPrice G d:=
    Finset.single_le_sum (f:=generator G) (fun _ _=> by unfold generator; positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

-- Additional small-kinematics purchase. Before and after UV supply estimates use existing
-- orders/maps. Extras built on posterior wait as it only concerns fixed-stage inputs recognized.
abbrev DoorRate (X:Stage)(L:ℕ) := (L:ℝ)+X.paths+X.width⁻¹+X.clip.relaxation+X.clip.linear⁻¹+X.clip.direct+X.supportExponent+X.drift+X.columns
structure Evident (A:Levels G):Prop where
   wheel : ∀ᶠ k:ℕ in atTop, DoorRate (A.params (k+1)) (A.S.block k).val ≤ Real.log (Real.log (A.clock.hatBeta k))
private lemma pay_evident (hG:G.Simple)(U:Wait K): ∃ V:Wait K, U.minLength ≤ V.minLength∧U.readyHere ≤ V.readyHere ∧ U.window ≤ V.window ∧ ∀ A:Levels G,Paid V A→ Evident A:=by
   have hp:Tendsto (Ship.preHat K) atTop atTop:= Filter.tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (Gauge.slopeConstant_pos hG))
   choose x hx using fun j=> eventually_atTop.mp ((Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp hp)).eventually_ge_atTop (DoorRate (T.profile j) (D.L j).val))
   let V:Wait K:={ U with readyHere:= fun i=>max (U.readyHere i) (x (i+1)) }; refine ⟨V,le_rfl,fun _=>le_max_left ..,le_rfl,fun A hPaid=> ⟨?_⟩⟩
   filter_upwards [A.fits.deep.eventually_gt_atTop T.first] with k hk; let j:= A.clock.J (k+1)-1
   have hz:T.first < A.clock.J (k+1):=hk.trans_le (A.fits.mono k.le_succ)
   have hq:j+1=A.clock.J (k+1):=by unfold j; omega
   obtain ⟨i,hT,hB,hI⟩:= hPaid.run j (by omega)
   have hj: A.clock.J i=j:=hI _ (Nat.sub_le ..) (by omega)
   have hi:i ≤ k := Nat.le_of_not_gt fun hu=>by have he:=A.fits.mono (show k+1 ≤ i from hu); omega
   let s:=A.S.scale k
   have ht : Ship.preHat K s=A.clock.hatBeta k:=by unfold Ship.preHat Calendar.hatBeta; rw [hPaid.bar]
   have he:= (A.fits.sameFactor k).symm.trans (congr_fun hPaid.lengths _)
   change DoorRate (A.clock.stage _) _ ≤ _; rw [hPaid.stage,he,← ht,← hq]; exact hx (j+1) s (((le_max_right ..).trans hT).trans ((OPE.scale_mono A.S).monotone hi))

variable {C:Family G}
structure RG12Supply (B:Binding C)(H:C.Makes)(O:HaarBudget G)(J:ChartRatio G) : Prop where
   paid : Evident C.path.levels
   thin : ∀ᶠ k:ℕ in atTop, ((C.S.block k).val:ℝ) ≤ C.path.levels.clock.hatBeta k ^ Soft.RG12.dialPower (C.path.levels.clock.J (k+1))
   covers (d:ℕ) : ∃ P:Fin 3→Tapes.Panel d,
     (∃ ξ:ℝ,Checks (P 0).arc (P 1).arc (P 2).arc ξ (trays d) d) ∧
     ∀ n:ℕ, ∀ᶠ k in atTop, ∃ i:ℕ,n ≤ i ∧ i ≤ k ∧ C.S.a i/C.S.a k ≤ C.path.levels.clock.hatBeta k^(2*Soft.RG12.dialPower (C.path.levels.clock.J k)) ∧
       ∃ t, Poised P B H O J (trays d) (ParcelPrice G d) i t

lemma RG12Supply.complete {B:Binding C} {O:HaarBudget G} {J:ChartRatio G}
    {H:C.Makes} {W : Worth} {a b c e r L}
    (h:RG12Supply B H O J) (hG:G.Simple)
    (hS:Scrim C W a b c e (fly C.path.levels) r L)
    (F:Extraction.Order) : CompleteWeak C F := by
  intro N D R hR hsm hsp
  let d:=max N D
  obtain ⟨P,⟨ξ,hξ⟩,hP⟩:= h.covers d
  have he: ∃ᶠ j in atTop,∃ t, Poised P B H O J (trays d) (ParcelPrice G d) j t:=by
    refine frequently_atTop.mpr fun n=>?_
    obtain ⟨_,i,hi,-,-,hM⟩:= (hP n).exists
    exact ⟨i,hi,hM⟩
  obtain ⟨V,hV⟩:= podium P B H hG hS O J _ (fun i hi=>parcelCost i d hi) F (Nat.le_add_left ..) R hR hsm hsp hξ he
  exact reduce_wave V hsp F hV (le_max_right ..) ((le_max_left ..).trans (Nat.le_add_right ..))

lemma rg12_sponsor (hG:G.Simple)(B:MapPrices)(O:HaarBudget G)(J:ChartRatio G)
    (hx:LocalRatio J) (u:ℕ→ℕ)(h:RG12Relay T B u)(hu:∀ i,u i ≤ (D.L i).val) (U:Wait K) :
    ∃ V:Wait K, U.minLength ≤ V.minLength∧U.readyHere ≤ V.readyHere ∧ U.window ≤ V.window ∧
      ∀ C:Family G,Paid V C.path.levels→∀ H: Binding C,H.prices=B→ ∀ hM:C.Makes,ParadeX C→RG12Supply H hM O J:=by
    obtain ⟨b,P,hξ,hP,hK⟩:=h.buys
    let Z:=ParcelPrice G
    have h(Z0:ℕ):0 ≤ Z Z0:= Finset.sum_nonneg fun _ _=> by unfold generator; positivity
    obtain ⟨V,P',h1,h2,h3,hArc,hθ,h0⟩:=rg12_y_tour B O J hG hK h (fun _=>Nat.le_add_left ..) hu hx U
    obtain ⟨W,hL,hW,hW',hs⟩:= w_bound V hG
    let B'(j s):= ∀ d∈ b j, ∀ χ, Ship.benchCost K (P' d χ).arc j s ≤ Soft.RG12.dial K j s
    have hf(j):∀ᶠ s in atTop,B' j s:=by
      exact (eventually_all_finset _).2 (fun d _=>eventually_all.mpr (fun χ=>Soft.RG12.dial_reserve hG j (P' d χ).arc (by linarith only [(P' d χ).huge,Nat.cast_nonneg (α:=ℝ) d])))
    choose A' hA' using fun j:ℕ=> eventually_atTop.mp (hf j)
    obtain ⟨Q,hQ,HQ⟩:= Soft.RG12.raiseR K (A'⊔ W.readyHere) hG
    obtain ⟨Y',hw1,hw2,hw3,hY⟩:= Soft.RG12.stops W HQ hG
    obtain ⟨Y,hh1,hh2,hh3,hY'⟩:=pay_evident hG Y'
    refine ⟨Y,h1.trans (hL.trans (hw1.trans hh1)),h2.trans (hW.trans (hw2.trans hh2)),h3.trans (hW'.trans (hw3.trans hh3)),fun C hPaid' H hB hm hX=> ?_⟩
    let L:= C.path.levels
    have hPaid: Paid Y' C.path.levels:= retains_budget hh1 (fun i=>⟨hh2 i,hh3 i⟩) hPaid'
    have hv:Paid W C.path.levels:= retains_budget hw1 (fun i=>⟨hw2 i,hw3 i⟩) hPaid
    have ht:=eventually_all.mpr (fun χ=> (rg12_print B O J (h0 χ) W hL hW hW').rent C hv H hB)
    refine ⟨hY' _ hPaid', (hY _ hPaid).1,fun d=>⟨P' d,?_,?_⟩⟩
    · simpa only [← hArc] using hξ d
    intro n
    have h :∀ᶠ i in atTop,T.first < L.clock.J i → Soft.RG12.Indexed K Q C.path.levels i →
       ∃ t, Poised (P' d) H hm O J (trays d) (Z d) i t:=by
      filter_upwards [ht,staging (n:=trays d) (z:=Z d) (P' d) H hm O J hG 0 hX (hθ d 0),
        L.fits.deep.eventually (hP d)] with i ht hu hk hi hh
      let j:=L.clock.J i; let s:=L.S.scale i
      have hS:W.readyHere j ≤ s:= ((le_max_right ..).trans (hQ j)).trans hh.ready
      apply hu (hs L hv i hS)
      intro χ
      have hT: Ship.benchCost K (P' d χ).arc j s ≤ Soft.RG12.dial K j s:=
         hA' j _ (((le_max_left ..).trans (hQ j)).trans hh.ready) d hk χ
      exact ht χ hi hS d hk (hT.trans hh.bench) (fun k ha hb=> hh.pad _ ((Nat.sub_le_sub_left hT i).trans ha) hb)
    obtain ⟨k,hk⟩:=eventually_atTop.mp h
    filter_upwards [(hY L hPaid).2 (max k n)] with i ⟨m,hm0,he,hq,h_1,h_2⟩
    exact ⟨m,(le_max_right ..).trans hm0, h_1,h_2,hk m ((le_max_left ..).trans hm0) he hq⟩
end YM.MergeProof.East
