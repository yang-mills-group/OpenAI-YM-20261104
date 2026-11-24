import YM.Integration.ActualRunSpring
import YM.LocalTaylorR2.Orbit.Sustained
import YM.LocalTaylorR2.Earned
import YM.R2I.Campaign.Accepted
import YM.Integration.ActualOriginalQPackets
import YM.IterationFour.Running

/-! Finite grading of the original marked Wilson step. The component grade
counts the real Taylor powers of every surviving Mayer logarithm. An
exceptional undistinguished component spends the top grade once, while its
entire integral still contains the joint original marked partner. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.Integration.ManuscriptQLocalMarkedGradeTail

open Function Set Finset Lattice Wilson RG RG.Shoot Pressure Pressure.Tube Tree
open Push Push.AbsoluteSums Push.PriceCompiler Push.SectorMeasure Precision
open ConnectedActivityE6 Progress.DirectedRecipe
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Mallow PhysicalNext.Repeat.Lotus
open LocalTaylorR2 LocalTaylorR2.Candle RG01.Survive MergeProof
open scoped Classical BigOperators

section component

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S}
    {P : Teller G} {Q : ConnectedActivityE6.Target G P} {W x μ C : ℝ}
    {o : ConnectedActivityE6.Target.Order G W} {R : Rep G f}
    (H : Cash W x μ L Q o C T R) (M : Team R) (χ : Chi) (p : H.ThinP)

/-- The top coefficient is the whole integrated component whenever a
surviving nonregular label occurs. This identity holds for each joint
partner and each external field. -/
theorem exceptional (k : ℕ) (h : ¬ Clear (Orbit.restP M H p))
    (e : Orders k) :
    Orbit.graded M H χ p e =
      if e = perch k then Orbit.deck M H χ p else 0 :=
  Orbit.graded_dead M H χ p (fun z => h z.2) e

end component

section trajectory

variable {G : Gauge} (R : Run G) {N n m : ℕ} {hm : m < N}
    (P : ActualRunSpring.Packet R N n m hm)
local notation "j" => R.alloy.B.a.clock.J (m+1)
local notation "β" => R.alloy.B.a.clock.hatBeta (m+1)
local notation "g" => Pert.Asymptotics.regulatorRun R.family N n (m+1)
local notation "S₀" => R.alloy.B.a.clock.op m n
local notation "Q₁" => P.input P.point.val
local notation "Q₀" => P.spring.result P.point.val

/-- The ordinary simultaneous campaign purchase supplies the grade
receipt and both support reserves before any cutoff, field or menu. -/
theorem campaign {T : Campaign R} {Δ : Daisy.Charity.RG12.Decal G}
    (paid : R2I.Funded ((Mallow.orbitD G).paired Δ) R T) :
    Mallow.RG12.Earned (Mallow.orbitD G) R.kit.shape R.alloy.delay ∧
      ∀ i, 100 ≤ (R.alloy.B.a.budget i).supportExponent :=
  ⟨fun levelIndex x hx i hi => (paid.localBudget.tailor levelIndex x hx i hi).1,
    fun i => (paid.fixed i).ge⟩

include hm in
/-- Convert the funded real grade into the fine coupling of the actual
Run, with its actual beta-band comparison and its original clock loss. -/
theorem price (k : ℕ) {δ : ℝ} (hδ : δ ≤ 1) (hsmall : CalendarStep.loss j ≤ δ) :
    β ^ Tail.requested (k+1) (CalendarStep.loss j) ≤
      (Real.sqrt 2 * g)^((k+1:ℝ)-δ) := by
  have ht := R.alloy.B.a.fits.delayed (m+1)
  refine (Real.rpow_le_rpow_of_exponent_le ht.le ?_).trans
    (CalendarStep.coupling_paid k δ hδ ht
      (((R.T.sticks N n).prices (m+1) (Nat.zero_le _) hm).2))
  unfold Tail.requested
  linarith

end trajectory
end YM.Integration.ManuscriptQLocalMarkedGradeTail

/-! The unfrozen original Q rows pay their kernel norm before insertion of
the coupling. This uses the actual signed Laurent powers of the literal
finite Q bank and retains its physical budget and every test domain. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalOriginalGradeTariff

open Function Finset Lattice Wilson RG Source Labels Marker
open LocalComparison PhysicalNext.Repeat.Legato Comparison.Density.RenderM
open scoped Classical BigOperators

section
variable {G : Gauge} {n : Side} {V : Type} [DecidableEq V] {Γ : Census V}
  {D : V → ComparisonDensity.Address.Orbit} (P : MarkedPackets D G n Γ)
  {C : BudgetPoint} {A : V → Support n}
  {region : Comparison.Density.Testing.Region (fun v => (D v).Mood) n}
  {w : V → ℝ} {g width budget : ℝ} {offset slope : ℕ}

/-- Every negative or zero Laurent prefactor dominates one at the actual
real weak coupling. All fields, paths, roots and source weights are those
of the supplied bank. -/
theorem unweighted (H : P.Paid C A region w g width budget offset slope)
    (hg : 0 < g) (hweak : g ≤ 1) (hp : ∀ i, P.power i ≤ 0) :
    P.Paid C A region w 1 width budget offset slope := by
  refine { H with roots := fun v => ?_ }
  apply Extra.Iteration.Cost.mono (H.roots v)
  · intro i
    split_ifs
    · cases hi : P.packet i with
      | none => exact le_rfl
      | some T =>
        have hc := (H.coefficient i T hi).1
        have ht := (Poly.worth H.positive (P.mode i)).le
        positivity
    · exact le_rfl
  · intro i
    split_ifs
    · cases hi : P.packet i with
      | none => exact le_rfl
      | some T =>
        have hc := (H.coefficient i T hi).1
        have ht := (Poly.worth H.positive (P.mode i)).le
        have hm : 1 ≤ ‖(g : ℂ) ^ P.power i‖ := by
          rw [norm_zpow, Complex.norm_real, Real.norm_of_nonneg hg.le]
          exact one_le_zpow_of_nonpos₀ hg hweak (hp i)
        simp only [Complex.ofReal_one, one_zpow, norm_one]
        gcongr
    · exact le_rfl
end

section
open ActualOriginalQReaders ActualOriginalQPackets
variable {G : Gauge} {R : Run G} {B : MS.Local.Physical.Deck G}
  {p L n : ℕ} {hn : n ≤ L} {V : Type} [DecidableEq V] [Fintype V]
  (Q : MS.Land.Prescription B)
  (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
  (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)

/-- The literal input before coupling freeze. The zero padding also has
power zero. -/
theorem powers_nonpositive (N i : ℕ) :
    (packets Q D u μ orders N).power i ≤ 0 := by
  unfold packets
  dsimp only [MarkedPackets.ofFin]
  split
  · exact neg_nonpos_of_nonneg (Int.natCast_nonneg _)
  · exact le_rfl

/-- The original physical budget pays the kernels on the unrescaled
analytic family without changing any power or using a new regulator. -/
theorem original (N : ℕ) (C : BudgetPoint) (w : V → ℝ) (width : ℝ)
    (hwidth : 0 < width) (hw : ∀ i, 0 < w i)
    (hg : 0 < Pert.Asymptotics.regulatorRun R.family N p L)
    (hweak : Pert.Asymptotics.regulatorRun R.family N p L ≤ 1) :
    (packets Q D u μ orders N).Paid C (positions D u).stub
      (ActualRunQlocalNativeTuple.readerRegion D) w 1 width
      (packetCost Q D u μ orders N w width) (packetCover Q D u μ orders N C) 0 :=
  unweighted _ (packets_paid Q D u μ orders N C w width hwidth hw)
    hg hweak (powers_nonpositive Q D u μ orders N)
end

/-- The actual weak-coupling cutoff is selected by the Run before the
period, bank, prescription, source fields and finite root tests. -/
theorem eventually_original {G : Gauge} (R : Run G) (hG : G.Simple) :
    ∀ᶠ L : ℕ in Filter.atTop, ∀ p N : ℕ, L ≤ N →
      ∀ {B : MS.Local.Physical.Deck G} {n : ℕ} {hn : n ≤ L}
        {V : Type} [DecidableEq V] [Fintype V] (Q : MS.Land.Prescription B)
        (D : ActualRunQlocalNativeTuple.Datum R p L n hn V)
        (u : V → MS.Rake.Label B) (μ : ℝ) (orders : V → ℕ)
        (C : BudgetPoint) (w : V → ℝ) (width : ℝ), 0 < width → (∀ i, 0 < w i) →
      (ActualOriginalQPackets.packets Q D u μ orders N).Paid C
        (ActualOriginalQPackets.positions D u).stub (ActualRunQlocalNativeTuple.readerRegion D)
        w 1 width (ActualOriginalQPackets.packetCost Q D u μ orders N w width)
        (ActualOriginalQPackets.packetCover Q D u μ orders N C) 0 := by
  filter_upwards [IterationFour.Currency.g_small hG R.makes 1 zero_lt_one] with L hL
  intro p N hN B n hn V _ _ Q D u μ orders C w width hwidth hw
  exact original Q D u μ orders N C w width hwidth hw
    (IterationFour.Currency.g_pos R.makes N p L hN) (hL N p hN).le
end YM.Integration.ManuscriptQLocalOriginalGradeTariff

/-! Joint auxiliary grading on the actual first connected-component and
second connected-cluster sums. Each selected short leaf keeps its assigned
degree, including all independent colors and each of their targets. The
real integrated partner and its original hard top-grade slot are retained.
-/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Orbit
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive Candle
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ s κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:Team R) (X:Coat T F) (H:Cash W s μ L Q o C T R)
    {Z : Support c} {k k':Finset ℕ}{u v : Air f G} (χ:Chi) (p:H.ThinP)
local notation "Θ"=>p.val
local notation "Ω"=> (M.signs S)
open _root_.YM.Marker Merge Switch Palette MergeProof Accent GridRenewal.Rain GridApprox.Nil
open Gas Ursell Trees
variable {ι Z:Type} [Fintype ι] [DecidableEq Z] (Y:ι→Leaf R)(u:ι→ℝ)(hU:Merge.Palette.Plot Y H u)
   (B:_root_.YM.Marker.Census Z)(z:ι→ _root_.YM.Marker.Poly B)
local notation "hd"=> Pressure.temp s
local notation "P!"=> Poly B
local notation "T!"=> turnWeight Y u
variable (l:ℕ)
variable (k:H.fragrances)
local notation "Θ'"=> reachability k
local notation "T'"=> Booking H Y l k -- check args
set_option quotPrecheck false
local notation "Z₀"=> Option (Fin k.1)
open Charge RG01.Survive.Products AnalyticBridge VerifiedReset Next.Foundations
variable {j k' m' n:ℕ} {θ ρ D K e v₀ d b r x Ct b' R' A c' δ :ℝ}
variable (hk:Marker.Tinted G s K d o.a L χ j)(U:StoresR2 H j v₀ d A D k' x n χ)
variable (N:Captain H j Ct d v₀ w A b r b' R' (n+j) χ) {ζ:ℝ}(hB:LocalBookingsR2 ζ c' N.conduit)
variable (h:1≤betaF G s L)(hζ:0≤ζ)(hH:1≤θ)(hp:1≤ρ)(hs:ρ*c'≤1)(hL: Charge.Allows l j θ)(hℓ: ρ^(l+1) ≤ betaF G s L^ζ)(hM:betaF G s L^ζ ≤ Real.exp (Q.mark L μ s))

/-- The disk acts on the real bounds of selected leaves after the partner
split. It leaves their fine fields and the normalized marked colors fixed. -/
def gradedCharges (u : ι → ℝ) (d : ι → ℕ) (ρ : ℝ) (i : ι) : ℝ := u i * ρ ^ d i

variable {t : ℝ} (ht : 1 ≤ t) (htρ : t ≤ ρ)
variable (ν : ι → ℕ) (hν : Merge.Palette.Plot Y H (gradedCharges u ν t))

omit [Fintype ι] in
lemma ticket_weight (i : Tickets (sign Y S)) :
    turnWeight Y (gradedCharges u ν ρ) i =
      turnWeight Y u i * ρ ^ (∑ s ∈ i.val, ν s) := by
  simp only [turnWeight, gradedCharges, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

/-- Sum of the powers on all selected leaves and the complete component's
native internal grade. Each selected row belongs to the genuine joint partner. -/
abbrev mixedDegree (w : Travel S Y l) : ℕ := w.2.val + ∑ i ∈ w.1.val, ν i

abbrev connectedDegree (q : Booking H Y l k) : ℕ :=
  Products.order (fun (_ : Z₀) (w : Travel S Y l) => mixedDegree Y l ν w) q

local notation "wU" => stationCost H χ Y u l N D x K θ
local notation "W₀"=> (fun i : H.ThinP => totalBill H χ i N Y (gradedCharges u ν t) K D θ ζ x ρ l)

section Cluster
include hk U hU hH hB h hζ hp hs hℓ hM ht htρ hν

/-- Weighted first tree criterion for the original real integrals. Both
source degrees and the local internal powers are charged before forming
the connected signed sum. -/
lemma mixed_bought {r : ℕ} (F : Finset (Booking H Y l k))
    (above : ∀ q ∈ F, r ≤ connectedDegree H Y l k ν q) :
    (∑ q ∈ F, cCost H χ Y u l k N D x K θ q) ≤
      (t^r)⁻¹ * ∏ i : Z₀, 2^j * W₀ (k.2 i) := by
  have component (p : H.ThinP) (w : Travel S Y l) :
      wU p w * t^(mixedDegree Y l ν w) ≤
        stationCost H χ Y (gradedCharges u ν t) l N D x K θ p w * ρ^w.2.val := by
    calc
      _ = stationCost H χ Y (gradedCharges u ν t) l N D x K θ p w * t^w.2.val := by
        unfold stationCost mixedDegree
        rw [ticket_weight, pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans ht) htρ _)
        (mul_nonneg (twN H Y (gradedCharges u ν t) hν _)
          (recNN (Palette.team Y w.1) H χ _ hk U N hH _))
  have priced (p : H.ThinP) :
      (∑ w : Travel S Y l, wU p w * t^(mixedDegree Y l ν w)) ≤ W₀ p := by
    apply (Finset.sum_le_sum (fun w _ => component p w)).trans
    rw [Fintype.sum_prod_type]
    exact turnout H χ p hk U N hB h hζ hH hp hs hℓ hM Y (gradedCharges u ν t) hν
  have weighted := Products.booked (fun i : Z₀ => wU (k.2 i)) (fun i : Z₀ => W₀ (k.2 i))
    t (fun (_ : Z₀) (w : Travel S Y l) => mixedDegree Y l ν w) j
    (zero_le_one.trans ht)
    (fun i w => mul_nonneg (twN H Y u hU _)
      (recNN (Palette.team Y w.1) H χ _ hk U N hH _)) (fun i => priced (k.2 i))
  rw [mul_comm, ← div_eq_mul_inv, le_div_iff₀ (by positivity), Finset.sum_mul]
  apply le_trans _ weighted
  apply le_trans (Finset.sum_le_sum (fun q hq =>
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (above q hq))
      (c_nn H χ Y u hU l k hk U N hH q)))
  have subset (A : Type) [inst : Fintype A] (q : Finset A) : q ⊆ univ := Finset.subset_univ q
  let inst := @Pi.instFintype (Option (Fin k.fst)) (fun _ => Travel S Y l)
    (fun _ _ => Classical.propDecidable _) inferInstance (fun _ => inferInstance)
  exact Finset.sum_le_sum_of_subset_of_nonneg (@subset _ inst F)
    (fun q _ _ => mul_nonneg (c_nn H χ Y u hU l k hk U N hH q)
      (pow_nonneg (zero_le_one.trans ht) _))
end Cluster
variable (q₁:Z→ℝ)(hQ:∀ i,0<q₁ i)(hq:∀ i,Marker.Poly.price q₁ (z i) ≤ 1) (Ra:Z→Site c) (hr:∀ i, GridApprox.Nil.Scoped {x| Ra x∈(Y i).crest.image S.ratio.parent} (z i)) -- Ra shadows!
variable (P':BudgetPoint) (he: P'.threshold=Pressure.temp s)(hJ:P'.order≤j)(hF:P'.B=radiusB s)(n':ℕ)(hn:P'.power≤n') (x':ℝ)(hy:0≤x')(hv:Sailor G P'.threshold x' j)(hZ:j*x' ≤ v₀)
local notation "a₀"=> wageScale H k P' j n'
local notation "fp"=> cCost H χ Y u l k N D x K θ
local notation "τ₀"=> (|coeff H k| *a₀)
local notation "m₀"=> frug H χ Y u B z l k N P' n' D x K θ -- check
include h hU hζ hH hp hs hL he hJ hF hn hv hy hZ hB U hk
local notation "WU" => measureS H χ Y u B z l k
local notation "p₀" => petition H Y B z l k
include hQ hq hℓ hM ht htρ hν
lemma mixed_refined (F:Finset (Booking H Y l k)) (r:ℕ)(hΩ : ∀ i∈F,r ≤ connectedDegree H Y l k ν i):
    ∃ p : Sheet B, 0 ≤ p ∧ wordsPrice q₁ p ≤ (t^r)⁻¹ * LeafReady.allowance P' k j n' W₀ ∧
    ∀ m,let Z':=fun U=>(WU F U).part m; P'.Regular Θ' Z' ∧ ∀ (o:Site c), o∈ Θ' → P'.supBounds o Θ' Z' (p m):=by -- notation W₀ conflict section rℝ! depends on `r` through inferred Lean parameter? W₀ uses N capturing r old ok.
  let L m:= ∑ i∈F,m₀ i m
  have hp m o₁ (hy':o₁∈Θ'): let Z':=fun U=>(WU F U).part m; P'.Regular Θ' Z'∧P'.supBounds o₁ Θ' Z' (L m):=by
    intro J; rw [show J=∑ i∈F,(fun U=>(slice H χ Y u B z l k i U).part m) from funext fun j=>by unfold J measureS;rw [Finset.sum_apply]; exact Poly.part_sum ..]; exact regular_bound_sum _ _ _ (fun i _=> straight H χ Y u hU B z l k hk U N hB h hζ hH hp hs hL P' he hJ hF n' hn x' hy hv hZ i m o₁ hy')
  let x₀:=(Song.locate H k).site; have ha : x₀∈Θ':= (Song.locate H k).anchor
  have hy₀:= hy
  refine ⟨L,fun m=> (hp m x₀ ha).2.1, ?_,fun m=> ⟨(hp m x₀ ha).1, fun i h => (hp m i h).2⟩⟩
  unfold wordsPrice L; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; unfold frug
  let U₀:=fun i:Booking H Y l k=> (τ₀)*fp i
  have hX : 0≤ shiftG s:=by unfold shiftG; positivity
  have hh : 0≤ τ₀:= mul_nonneg (abs_nonneg _) (by unfold wageScale; positivity)
  calc _ = ∑ i∈F,Poly.price q₁ (p₀ i)*U₀ i:=by apply Finset.sum_congr rfl; intro i _; unfold Poly.price; rw [Finset.sum_mul]; exact Finset.sum_congr rfl (fun j _=> (mul_assoc ..).symm)
       _ ≤ ∑ i∈F,U₀ i:= Finset.sum_le_sum fun i _=> le_of_le_of_eq (mul_le_mul_of_nonneg_right (pet_price H Y B z l k q₁ hQ hq i) (mul_nonneg hh (c_nn H χ Y u hU l k hk U N hH i))) (one_mul _)
       _ ≤ (τ₀)*((t^r)⁻¹*∏ j':Z₀,(2^j*W₀ (k.2 j'))):=by unfold U₀; rw [← Finset.mul_sum];exact mul_le_mul_of_nonneg_left (mixed_bought H χ Y u hU l k hk U N hB h hζ hH ‹1≤ρ› ‹ρ*c'≤1› hℓ hM ht htρ ν hν F hΩ) hh
       _ = _:= by
         unfold LeafReady.allowance clusters coeff wageScale; let D₀:=(t^r)⁻¹
         rw [abs_div,abs_of_nonneg (by positivity : (0:ℝ) ≤ ((k.1+1).factorial:ℝ))]; ring

omit hQ hq hℓ hM ht htρ hν h hU hζ hH hp hs hL he hJ hF hn hv hy hZ hB U hk
open Reserves Tender LeafReady
variable {a wN : ℝ} (h₁ : 0 < δ) (h₂ : Quotes.preExponent P' ≤ a)
local notation "pr0" => Quotes.preExponent P'
variable [Fintype Z] (F': ∀ k:H.fragrances, Finset (Booking H Y l k))
include ht htρ hν hU h hr hQ hq hk U hB hζ hH hp hs hL hℓ hM he hJ hF hn hv hy hZ h₁ h₂
lemma mixed_connected (hY: Ready H.smallAt P'.B (fun i=>2^j* W₀ i) (a+δ) wN δ (1/2)) (r:ℕ)(hc:∀ i q,q∈F' i → r ≤ connectedDegree H Y l i ν q): shop H B q₁ Ra P' (fun i=> measureS H χ Y u B z l i (F' i)) ((t^r)⁻¹*(collars G δ s j n'*(wN*(1-1/2:ℝ)⁻¹))) :=by
  have hr i:= retainsS H χ Y u B z l i _ hr (F' i)
  choose u hP ht hX using fun i=> mixed_refined H χ Y u hU B z l i hk U N hB h hζ hH hp hs hL hℓ hM ht htρ ν hν q₁ hQ hq P' he hJ hF n' hn x' hy hv hZ (F' i) r (hc i)
  let f i:= (t^r)⁻¹*allowance P' i j n' W₀ -- local notation capture
  have hv:= hitsA H P' n' W₀ hY r h₁ h₂ ‹1 ≤ t›
  have hf i:0≤f i:= (show 0≤ wordsPrice q₁ (u i) from sum_nonneg (fun j _=> mul_nonneg (Poly.worth hQ _).le (hP i j))).trans (ht i)
  refine ⟨f, ?_,hv,fun i=> ⟨_,hP i,ht i,hX i,hr i⟩⟩
  have hD : ∀ i:H.fragrances,(reachability i).Nonempty := fun i=> ⟨_,(Song.locate H i).anchor⟩
  have hf' := Product.everyone_ne _ _ hf (fun i _=> hD i) hv
  exact hf'.2.1.of_nonneg_of_le hf (fun i=> le_mul_of_one_le_right (hf i) (Real.one_le_exp (mul_nonneg (show 0 ≤pr0 from by unfold Quotes.preExponent; have h:= P'.exponent_pos; positivity) (Nat.cast_nonneg _))))
end YM.LocalTaylorR2.Orbit

namespace YM.LocalTaylorR2.Orbit
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Art Pond Poll Tablet Eider Stained Shield Flux Brush
open Scroll Frond Vine Polar Foramen Gate Quill Hues Rotation Progress.StationaryScenes Census Itinerary
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive Candle
open _root_.YM.Marker Merge Switch Palette MergeProof Accent GridRenewal.Rain GridApprox.Nil
open Gas Ursell Trees Charge RG01.Survive.Products AnalyticBridge VerifiedReset Next.Foundations Tail
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
  {R : Rep G f} {W s μ C : ℝ} {Q : YM.ConnectedActivityE6.Target G P}
  {o : ConnectedActivityE6.Target.Order G W}
  (H : Cash W s μ L Q o C T R) (χ : Chi)
  {ι Z : Type} [Fintype ι] [DecidableEq Z] [Fintype Z]
  (Y : ι → Leaf R) (u : ι → ℝ) (hbase : Merge.Palette.Plot Y H u)
  (B : _root_.YM.Marker.Census Z) (z : ι → _root_.YM.Marker.Poly B)
  (l : ℕ) (q₁ : Z → ℝ) (hQ : ∀ i, 0 < q₁ i)
  (hq : ∀ i, Marker.Poly.price q₁ (z i) ≤ 1) (Ra : Z → Site c)
  (hr : ∀ i, GridApprox.Nil.Scoped {x | Ra x ∈ (Y i).crest.image S.ratio.parent} (z i))
  (R₀ : Rep G c) (hTemp : R₀.p.threshold = Pressure.temp s)
  (Y₁ : Target.Expense Q) (he : Quotes.preExponent R₀.p ≤ Y₁.earn)
  (hF : R₀.p.B = radiusB s) (hStamp : Stamp T)

set_option maxHeartbeats 200000 in
include hbase hQ hq hr hTemp he hF hStamp in
/-- On the same booked pressure window the original vacuum radius is
retained in both tree criteria. The physical source columns require their
primitive quote only through their own radius cap. -/
lemma funded_mixed (cap : ℝ) (hcap : 1 ≤ cap) (ν : ι → ℕ)
    (raised : ∀ t : ℝ, 1 ≤ t → t ≤ cap → Merge.Palette.Plot Y H (gradedCharges u ν t))
    (ε : ℝ) (purchase : pledge Q Y₁ L W μ s o R₀.p.order R₀.p.power l χ ε)
    (F : ∀ k : H.fragrances, Finset (Booking H Y l k)) (r : ℕ) (hrange : r ≤ l+1)
    (above : ∀ i q, q ∈ F i → r ≤ connectedDegree H Y l i ν q) :
    shop H B q₁ Ra R₀.p (fun i => measureS H χ Y u B z l i (F i))
      (max (betaF G s L ^ requested r ε)
        ((cap^r)⁻¹ * betaF G s L ^ requested 0 ε)) := by
  let e₀ := Y₁.one / 2
  let a := Y₁.earn
  let σ := R₀.p.order
  let d := R₀.p.power
  obtain ⟨A,a',C,x,v₁,t',r',B',D,x',b,y,K,θ,ρ,w,l',n,hP,h⟩ := purchase
  obtain ⟨N,hA,hB,hF'⟩ := h _ _ _ _ hStamp _ _ H
  let z' : ℝ := l+1
  have hz : 0 ≤ z' := by unfold z'; positivity
  have hh₀ : 0 < e₀ := half_pos Y₁.first
  obtain ⟨hℓ,hG,hr',hu,hH,hT,hτ,hx,hδ,hθ,hB',hv,hL⟩ := hP
  let t := min ρ cap
  have h1 : 1 ≤ t := le_min hr' hcap
  have hρ : t ≤ ρ := min_le_left _ _
  have hRaised := raised t h1 (min_le_right _ _)
  let v := gradedCharges u ν t
  have hhN p := totalN (l:=l) H χ p hF' hB N hℓ hz hG hr' Y v hRaised
  let φ₀ i := totalBill H χ i N Y v K D θ z' x' ρ l
  have hX : Ready H.smallAt R₀.p.B (fun i => 2^σ * φ₀ i) (a+e₀) w e₀ (1/2) := by
    rw [hF]
    refine ⟨hu, hh₀, hB', by norm_num, fun i => mul_nonneg (by positivity) (hhN _), ?_⟩
    have exp : a + e₀ + e₀ ≤ Q.exp := by
      unfold a e₀
      linarith only [Y₁.worth, Y₁.second]
    exact fun i => budget_loosen (incarnate H χ hF' hB N hA hℓ hz hG hr' Y v hRaised hδ exp i) hθ
  have hR : Sailor G R₀.p.threshold y R₀.p.order := by
    rw [hTemp]
    exact ⟨fun c u h => N.weigh.stroke c _ (h.trans N.talent)⟩
  have hTail := mixed_connected H χ Y u hbase B z l hF' hB N hA hℓ hz hG hr'
    hT hH hτ hx h1 hρ ν hRaised q₁ hQ hq Ra hr R₀.p hTemp le_rfl hF d le_rfl
    y N.income hR N.near hh₀ he F hX r above
  apply opened H B q₁ Ra hTail
  by_cases hcut : ρ ≤ cap
  · rw [show t = ρ from min_eq_left hcut]
    have hfee := hv r hrange
    unfold Tail.report at hfee
    rw [one_mul] at hfee
    exact hfee.trans (le_max_left _ _)
  · rw [show t = cap from min_eq_right (le_of_not_ge hcut)]
    have hfee := hv 0 (Nat.zero_le _)
    unfold Tail.report at hfee
    simp only [pow_zero, inv_one, one_mul] at hfee
    exact (mul_le_mul_of_nonneg_left hfee
      (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hcap) _))).trans (le_max_right _ _)

/-- If source leaves can pay the radius beta^((1-η)/2), the loss in a
joint grade r is exactly the native clock loss plus ηr. -/
lemma capped_price (β : ℝ) (hβ : 1 ≤ β) (r : ℕ) (ε η : ℝ) (hη : 0 ≤ η) :
    max (β ^ requested r ε)
        (((β ^ ((1-η)/2))^r)⁻¹ * β ^ requested 0 ε) =
      β ^ requested r (ε+η*r) := by
  have hβ₀ : 0 < β := zero_lt_one.trans_le hβ
  have capped : (((β ^ ((1-η)/2))^r)⁻¹ * β ^ requested 0 ε) =
      β ^ requested r (ε+η*r) := by
    rw [← Real.rpow_mul_natCast hβ₀.le, ← Real.rpow_neg hβ₀.le, ← Real.rpow_add hβ₀]
    congr 1
    unfold requested
    push_cast
    ring
  rw [capped, max_eq_right]
  apply Real.rpow_le_rpow_of_exponent_le hβ
  unfold requested
  nlinarith [mul_nonneg hη (Nat.cast_nonneg (α:=ℝ) r)]
end YM.LocalTaylorR2.Orbit
