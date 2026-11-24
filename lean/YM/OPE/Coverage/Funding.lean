import YM.OPE.Coverage.Producer
import YM.MergeProof.North.Bardo

/-! ## Fund Poised on a dense log calendar before choosing later waits
The pre-stage boards are adapted from `MergeProof.East.sponsored` and
`y_poster`; only one Wilson family consumes these receipts below. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.East
open Function Filter Set MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open PhysicalNext.Repeat.Legato.Bandage
open Org Spec Next.Rank Next.Rank.Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift Glimmer Analysis Next.UVStress Climb Ward
open _root_.YM.OPE.Coverage PriceCompiler
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open Supply Accent
variable {G:Gauge}{C:Family G}{ι:Type}[Fintype ι]
variable {T : Sheet G}{D': Rolls T} {E : Protection D'} {T' : Delays E}{K : Bar T'}
-- same choices via Y.Gede.
structure Hotline (T:Sheet G)(B:MapPrices)(u:ℕ→ℕ) : Prop where
   buys : ∃ b:ℕ→Finset ℕ, ∃ Y:∀ d,Fin 3→ Tapes.Panel d, (∀ d, ∃ ξ, Checks (Y d 0).arc (Y d 1).arc (Y d 2).arc ξ (trays d) d) ∧
     (∀ d,∀ᶠ i in atTop,d∈ b i)∧Fortified T B trays Y b u
lemma hotlines (X:Supply.Sheet G)(B:MapPrices) (ht:Tendsto (fun i=>(X.profile i).order) atTop atTop):∃ k,Hotline X B k:=by
    choose a ha hp using fun d=>raises d (trays d)
    obtain ⟨k,N,P,hK,hV,hB⟩:= y_poster X B a ha _ (fun _=> Nat.le_add_left ..) ht
    refine ⟨N,⟨k,P,fun i=> ?_,hK,hB⟩⟩
    have h := hp i; simp only [hV]; exact h

variable {b:ℕ→Finset ℕ}{U:Wait K}
private theorem stationed_at (hG:G.Simple)(B:MapPrices)(O:HaarBudget G)(J:ChartRatio G){T:Sheet G}
   {D':Rolls T}{E : Protection D'}{T':Delays E}{K:Bar T'}{U:Wait K}(P:∀ d,Fin 3→ Tapes.Panel d)(μ:ℕ→ℝ)
   (ht:∀ d,∀ᶠ i in atTop,d∈ b i)(he:∀ i,∀ d,d ≤ i → generator G d ≤ μ i) (h':∀ d, ∃ ξ, Checks (P d 0).arc (P d 1).arc (P d 2).arc ξ (trays d) d)
   (hA:∀ d (i j:Fin 3),(P d i).θ=(P d j).θ ∧ ∀ k:ℕ,((P d i).bag k).era.coast.Q=((P d j).bag k).era.coast.Q)
   (H:∀i, ArcClock B O J U (fun d=>P d i) μ trays b) (C:Family G)(hL:Loft U C.path.levels) (P': Binding C)(hz:P'.prices=B) (hM:C.Makes) (hu:ParadeX C)
   (W : Worth)(a b c e r L)(hE:Scrim C W a b c e (fly C.path.levels) r L)(F): Paved C F:=by
    constructor
    · obtain ⟨i,hi⟩:=Filter.eventually_atTop.mp hL.tail
      filter_upwards [Filter.eventually_ge_atTop i] with m hm
      have hk:= hi (m+1) (hm.trans (Nat.le_add_right ..))
      let t:= C.path.levels.clock.J (m+1)
      have hh : ((C.S.block m).val:ℝ) ≤ 1+C.S.scale (m+1):= by
         rw [show C.S.block m = D'.L t from (C.path.levels.fits.sameFactor m).symm.trans (congr_fun hL.paid.lengths _)]
         linarith only [Real.add_one_le_exp (↑↑(D'.L t):ℝ), hk.2.2]
      apply Real.log_le_log (by exact_mod_cast (C.S.block m).property) hh
    intro N D R hT hS hR
    let d:= max N D; let p:=P d
    obtain ⟨β,hβ,hw⟩ : ∃ z:ℝ, (∀ i,(p i).arc ≤ z)∧ z ≥ 0:=by
         obtain ⟨v,hv⟩:= (Set.finite_range (fun i=>(p i).arc)).bddAbove
         exact ⟨max v 0,fun i=>(hv (mem_range_self _)).trans (le_max_left ..),le_max_right ..⟩
    let q:=Hop K β C.path.levels
    have hQ:Tendsto q atTop atTop:=hop_large β
    have hJ:Tendsto (C.path.levels.clock.J ∘ q) atTop atTop := C.path.levels.fits.deep.comp hQ
    let Z:=C.path.levels.clock
    obtain ⟨ξ,hξ⟩:=h' d
    have hl(i):0 ≤ (p i).arc:=by linarith only [(p i).huge, Nat.cast_nonneg (α:=ℝ) d]
    have hk: ∀ᶠ k in atTop, ∃ Y,Poised p P' hM O J (trays d) (μ d) (q k) Y:=by
       filter_upwards [carriage hL hG β hw,hJ.eventually (ht d), hQ.eventually hL.tail, hQ.eventually (wheel_room hL hG), hQ.eventually (staging (n:=trays d) (z:=μ d) p P' hM O J hG 0 hu (hA d 0)), hQ.eventually (eventually_all.mpr fun i=>(H i).rent C hL.paid P' hz)] with k hk ht' hf he hr hR'
       exact hr he fun i=> hR' i hf.1 hf.2.1 d ht' (small_journey hL (hβ i) hk (by unfold Ship.preHat; rw [←hL.paid.bar];rfl)).1 (small_journey hL (hβ i) hk (by unfold Ship.preHat; rw [←hL.paid.bar];rfl)).2
    obtain ⟨G₀,hG₀,k,hN,hP⟩ := frontage (x:=0) (y:=1) (w:=2) (F:=F) p P' hM hG hE O J (μ d) (he d) (Nat.le_add_left ..) R hR hT hS hξ q hQ hk (stops_near hL hG (hβ 0) (hl 0))
    exact reduce_near G₀ hS F hG₀ (le_max_right ..) ((le_max_left ..).trans (Nat.le_add_right ..)) k hN hP


lemma dense_funded (hG:G.Simple)(B:MapPrices)(O:HaarBudget G)(J:ChartRatio G)(hx:LocalRatio J) (u:ℕ→ℕ)(h:Hotline T B u) (hu:∀ i,u i ≤ (D'.L i).val) (T':Delays E) :
    ∃ V:Delays E, DelayLe T' V ∧ ∀ V':Delays E,DelayLe V V' → ∀ (D:Bar V') (W:Wait D), ∃ W':Wait D, W.minLength ≤ W'.minLength ∧ W.readyHere ≤ W'.readyHere ∧ W.window ≤ W'.window ∧ ∀ C:Family G,Paid W' C.path.levels→∀ Q:Binding C,Q.prices=B→ C.Makes→ParadeX C→∀ (W₀ : Worth)(a b c e r L),Scrim C W₀ a b c e (fly C.path.levels) r L→∀ F,Paved C F:=by
    obtain ⟨b,p,ht,hP,hK⟩:=h.buys
    let μ j:= ∑ i∈Finset.range (j+1),Accent.generator G i
    have he(i):0 ≤ Accent.generator G i:=by unfold Accent.generator; positivity
    have ho(j):= Finset.sum_nonneg (s:=Finset.range (j+1)) (fun i _ => he i)
    let ticket(x:ℝ):=∃ D:Bar T',D.value=x -- proof before later entries, handled as a function of numerical scale.
    choose seats prof h1 h2 h3 hC hA hB using fun D:Bar T'=>_root_.YM.OPE.Coverage.concert B O J hG hK ho (fun i=> Nat.le_add_left ..) hu hx (blank T' D)
    let gate(x:ℝ):= if hs:ticket x then (seats (hs.choose : Bar T')).readyHere else fun _=>0
    let V:=reset T' gate
    have hw:=reset_up T' gate
    refine ⟨V,hw,fun V' hv D W=>?_⟩
    let x:=D.value; have hh:ticket x:= earlier_parole (hw.trans hv) D
    let G':=hh.choose; have hG':G'.value=x:=hh.choose_spec
    let C':=seats G'; refine ⟨supplement C' W,le_max_right .., fun _=>le_max_right ..,fun i s=>(Nat.le_add_left ..).trans (Nat.le_add_right ..),fun C ht' H hY' hM hV a b c e t r l H' F=>?_⟩ -- shadow C
    have he':gate G'.value = C'.readyHere:=by rw [hG']; exact dif_pos hh
    have hs:=surface gate he' hG' hv ht'
    apply stationed_at hG B O J (prof G') μ hP ?_ ?_ (hA G') (hB G') C hs H hY' hM hV a b c e t r l H'
    · exact fun i hi d => Finset.single_le_sum (fun j _=> he j) (Finset.mem_range.mpr (Nat.lt_succ_of_le d))
    simpa only [hC G'] using ht
end YM.MergeProof.East
