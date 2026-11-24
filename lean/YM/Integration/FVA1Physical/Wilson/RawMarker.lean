import YM.Integration.FVA1Physical.Wilson.RawTicket
import YM.Integration.FVA1Physical.Wilson.StencilTicket
import YM.Integration.FVA1Physical.Wilson.InheritedReadout

/-! Reconstruct the entire inherited source ticket from the independently
computed normalized RG02 coefficients. Its first nonzero order cannot
precede the sum of the engineering orders of the actual stencil insertions. -/
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Finset Lattice RG YM.Wilson Tree Precision Marker Comparison.RG02
open FVA2.CityHistory FVA2.CityHistory.Delay FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open FormalOPE.RG10.MultiGauge.Splice FormalOPE.RG10.OpenSlots FormalOPE.RG10.MarkovChain.Warp
open FormalOPE.RG10.InversionTop RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.WilsonXLocal
open RGComparison.Core16.Lumen RGComparison.Core16.Parcel RGComparison.Core16.Parcel.Oven
open PertExtension PertExtension.Chart PertExtension.Series PertExtension.Series.Tested
open scoped Classical BigOperators ContDiff

variable {G : Gauge} {C : Family G} {V : Type} [Fintype V] [DecidableEq V]
    (R : Census V) {m p d : ℕ} (U : V → Stamp.Reservation C (C.side (m+1) p) d)
    (hC : C.Makes) (hs : ∀ i, Bid.pop (C.localSection i))
local notation "S" => C.path.levels.clock.op m p
local notation "F₀" => MSMatch.SourceTop.field U
local notation "w" => MSMatch.SourceTop.grade U

include hs in
omit [Fintype V] in
private theorem full_grade (s : R.Mode) (q : Bool) :
    Assembly.GradeAt (weight R w s) ((look q ∘ fullProduct F₀ s.val) ∘ expLinks G (Edge (Site (C.side (m+1) p)))) := by
  let z := axesP G (C.side (m+1) p)
  have one (i : V) : Assembly.GradeAt (w i) (F₀ i ∘ expLinks G (Edge (Site (C.side (m+1) p)))) := by
    have h := Bare.Signals.primary (C:=C) (U i).leg (hs _) (U i).anchor
    have e := h.coarse z.contDiff.contDiffAt z.map_zero
    convert e using 1
    funext x
    exact congrArg (F₀ i) (direct_link x).symm
  have prod (I : Finset V) : Assembly.GradeAt (∑ i ∈ I, w i)
      (fullProduct F₀ I ∘ expLinks G (Edge (Site (C.side (m+1) p)))) := by
    induction I using Finset.induction with
    | empty =>
      rw [Finset.sum_empty, show fullProduct F₀ ∅ ∘ expLinks G (Edge (Site (C.side (m+1) p))) = (fun _ => (1:ℂ)) by funext x; simp [fullProduct]]
      exact Assembly.GradeAt.unchecked contDiffAt_const
    | insert i I hi ih =>
      rw [Finset.sum_insert hi]
      rw [show fullProduct F₀ (insert i I) ∘ expLinks G (Edge (Site (C.side (m+1) p))) =
        (F₀ i ∘ expLinks G _) * (fullProduct F₀ I ∘ expLinks G _) from funext fun _ => Finset.prod_insert hi]
      exact (one i).mul ih
  exact (prod s.val).linear_contact (look q)

variable (F : Forest (C.path.levels.clock.op m p).ratio) (t : (C.path.levels.clock.op m p).Choices) (h : Bid.Larger (G:=G) (C.path.levels.clock.op m p))
    (Z : ChartRatio G) (hZ : LocalRatio Z) (v : (Descent.nil (top := C.side (m+1) p)).Tags)
local notation "d₁" => Descent.push S F Descent.nil
local notation "H₁" => (And.intro h True.intro)
local notation "η₁" => (t,v)

include hZ in
omit [Fintype V] in
private theorem ink_atop (s : R.Mode) (q : Bool) :
    skyread Z d₁ η₁ H₁ 1 (exPay (look q ∘ fullProduct F₀ s.val)) =
      solenoid S F Descent.nil v t Z 1 h True.intro
        (Stack.rise (stencilSignal S F (modeLamp R U hC hs s) (modeSite R U s) q)) := by
  let O := look q ∘ fullProduct F₀ s.val
  let J := modeLamp R U hC hs s
  let sites := modeSite R U s
  have c : fullProduct F₀ s.val = column J sites := by
    funext x
    exact (Finset.prod_coe_sort s.val (fun i => F₀ i x)).symm
  have mounted : boost (gate G S F) (exPay O) = Stack.rise (stencilSignal S F J sites q) := by
    rw [exPay,FormalOPE.RG10.MarkovChain.Vault.climbing _ ((full_grade R U hs s q).smooth.of_le le_top),
      group_stencil_ticket]
    apply congrArg Stack.rise
    funext x
    change look q (fullProduct F₀ s.val (expLinks G _ (pext G S F x.1))) = _
    rw [inserts,c]
  rw [atop S F Descent.nil v t Z 1 hZ h True.intro,invested,mounted]
  exact hZ

include hs hZ in
omit [Fintype V] in
private theorem ink_below (s : R.Mode) (q : Bool) {k : ℕ} (hk : k < weight R w s) :
    PowerSeries.coeff k (skyread Z d₁ η₁ H₁ 1 (exPay (look q ∘ fullProduct F₀ s.val))) = 0 := by
  let O := look q ∘ fullProduct F₀ s.val
  let A := exPay O
  have low : Through k A 0 := by
    intro j hj
    apply Subtype.ext
    funext x
    change (PowerSeries.coeff j (Stack.rise _)).val x = _
    rw [← Stack.reading_term,Stack.read_rise]
    change Assembly.jet ((look q ∘ fullProduct F₀ s.val) ∘ expLinks G _) j x = _
    rw [(full_grade R U hs s q).jet_z x (hj.trans_lt hk),map_zero]
    rfl
  have placed : Through k (boost (gate G S F) A) 0 := by
    intro j hj
    simp only [boost,PowerSeries.coeff_map]
    rw [low j hj]
    simp
  let Q := gateQ S F t (retained Descent.nil v (G:=G) True.intro)
  let z := useful S F Descent.nil v t h (G:=G) True.intro
  let W := fire S F t (μLedger Descent.nil Z v True.intro (parentZ 1)) Z 1
  let U₀ := Quadratic.uptake Q (Chart.tangent G F.Free) z
  have mul' : Through k (W * boost (gate G S F) A) 0 := by
    simpa only [mul_zero] using (Through.refl W).mul placed
  have int' : Through k (U₀ (W * boost (gate G S F) A)) 0 := by
    intro j hj
    change (PowerSeries.coeff j) (throughPrice _ (W * (boost (gate G S F) A))) = _
    simp only [throughPrice,AddMonoidHom.coe_mk,ZeroHom.coe_mk,PowerSeries.coeff_mk,
      mul' j hj,map_zero]
  have cond : Through k (solenoid S F Descent.nil v t Z 1 h True.intro (boost (gate G S F) A)) 0 := by
    change Through k (U₀ (W * boost (gate G S F) A) * FormalOPE.RG10.MarkovChain.Router.Return (U₀ W)) 0
    intro j hj
    exact ((int'.mul (Through.refl (FormalOPE.RG10.MarkovChain.Router.Return (U₀ W)))) j hj).trans (by rw [zero_mul])
  rw [atop S F Descent.nil v t Z 1 hZ h True.intro,invested]
  · exact (cond k le_rfl).trans (map_zero _)
  · exact hZ

variable (L : Bulk.Chain C.path)

/-- One coefficient at every order and field, including the zero coefficients
below the physical grade. -/
def rawMarker (s : R.Mode) (q : Bool) (u : Pins G (C.side m p)) (i : ℕ) : ℝ :=
  let a := weight R w s
  if a ≤ i then look q ((MSMatch.SourceTop.datum R m p U F t (axesP G _ u)).ordinaryCoefficient L
    (i-a) (i-a) s) else 0

include hC hs hZ in
theorem raw_marker_coefficient (s : R.Mode) (q : Bool) (u : Pins G (C.side m p)) (i : ℕ) :
    rawMarker R U F t L s q u i = PowerSeries.coeff i (Stack.read u
      (skyread Z d₁ η₁ H₁ 1 (exPay (look q ∘ fullProduct F₀ s.val)))) := by
  let a := weight R w s
  have power' : power (modeLamp R U hC hs s) = a := by
    change (∑ j : s.val, w j) = ∑ j ∈ s.val, w j
    exact Finset.sum_coe_sort ..
  change (if a ≤ i then look q ((MSMatch.SourceTop.datum R m p U F t (axesP G _ u)).ordinaryCoefficient L (i-a) (i-a) s) else 0) = _
  by_cases hi : a ≤ i
  · obtain ⟨P₀⟩ := Oven.builtafter (S).patch
    obtain ⟨X,H,_,cap⟩ := Spot.enough S F h P₀ u
    have eqn := normalized_solenoid R U hC hs u L F t s H h cap hZ v q
      (k:=i-a) (r:=i-a) le_rfl
    dsimp only at eqn
    rw [if_pos hi,ink_atop R U hC hs F t h Z hZ v s q]
    simpa only [power',Nat.add_sub_of_le hi] using eqn
  · rw [if_neg hi,Stack.reading_term,ink_below R U hs F t h Z hZ v s q (Nat.lt_of_not_ge hi)]
    rfl

end YM.Integration.FVA1Physical.Wilson
