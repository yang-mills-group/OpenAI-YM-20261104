import YM.LocalTaylorR2.Orbit.Trio
import YM.LocalTaylorR2.Capstone.Corral
/-! Price APPARENT T complexity killed by geometry of log polygon. At every marker projection i and support.
  Real→complex derivative conventions bridged. `V`-selection support includes all traces.
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
local notation "t"=> Tickets (sign Y S)
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
local notation "Q₀"=> N.conduit
abbrev stationCost (D x K θ:ℝ)(s: H.ThinP)(e:Travel S Y l):ℝ:= turnWeight Y u e.1* receipt (Palette.team Y e.1) H χ s N D x K θ e.2
-- notation n order. actor after `Palette.E #rent`; sShadow when using γ only.
local notation "wU" => stationCost H χ Y u l N D x K θ
local notation "Δ" => fun i: H.ThinP=> totalBill H χ i N Y u K D θ ζ x ρ l
abbrev cCost (D x K θ:ℝ)(q:T') := atPrices (fun i:Z₀=> stationCost H χ Y u l N D x K θ (k.2 i)) j q
abbrev ranked (q:T'):= Products.order (fun (_:Z₀)(w:Travel S Y l)=> w.2.val) q
include hk U hU hH
lemma c_nn (q:T') : 0≤ cCost H χ Y u l k N D x K θ q:= by unfold cCost atPrices; exact Finset.prod_nonneg fun i _=> mul_nonneg (by positivity) (mul_nonneg (twN H Y u hU _) (recNN _ H χ _ hk U N hH _))
include hB h hζ hp hs hℓ hM
lemma c_bought {X':ℕ} (S':Finset (Booking H Y l k))(hx:∀ i∈S', X' ≤ ranked H Y l k i):
    (∑ i∈S', cCost H χ Y u l k N D x K θ i)≤ (ρ^X')⁻¹* ∏ j':Z₀,(2^j * Δ (k.2 j')):=by
  have hi p := turnout H χ p hk U N hB h hζ hH hp hs hℓ hM Y u hU
  have hf:=Products.booked (fun i:Z₀=>wU (k.2 i)) (fun i:Z₀=> Δ (k.2 i)) ρ (fun i (w:Travel S Y l)=> w.2.val) j (zero_le_one.trans hp) (fun i k=> mul_nonneg (twN H Y u hU _) (recNN (Palette.team Y k.1) H χ _ hk U N hH _)) (fun i=>by simp only []; rw [Fintype.sum_prod_type]; exact hi (k.2 i))
  rw [mul_comm,← div_eq_mul_inv,le_div_iff₀ (by positivity), Finset.sum_mul]; apply le_trans _ hf; let u₀:=cCost H χ Y u l k N D x K θ
  apply le_trans (Finset.sum_le_sum (fun i hi=>mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hp (hx _ hi)) (c_nn H χ Y u hU l k hk U N hH i)))
  have hr (A:Type)[P:Fintype A](x: Finset A):x⊆univ:=subset_univ x
  let vInst:= @Pi.instFintype (Option (Fin k.fst)) (fun _=> Travel S Y l) (fun _ _ => Classical.propDecidable _) inferInstance (fun _=> inferInstance)
  exact Finset.sum_le_sum_of_subset_of_nonneg (@hr _ vInst S') fun i _ _=> mul_nonneg (c_nn H χ Y u hU l k hk U N hH i) (pow_nonneg (zero_le_one.trans hp) _)

include hB hL
omit hℓ hM
lemma borderL (q:T') :
    let f:= channel H χ Y u l k q; GaugeInvariant f ∧ Measurable f ∧ LocalOn Θ' f ∧ ∀ V,Healthy hd Θ' V → Ore V f v₀ (cCost H χ Y u l k N D x K θ q) j:=by
  let g(i:H.ThinP)(t':Travel S Y l):= graded (Palette.team Y t'.1) H χ i t'.2
  have hh i (w:Travel S Y l) := holding (Palette.team Y w.1) H χ i w.2
  let f (i: H.ThinP)(w:Travel S Y l) :=state H χ i Y u l w; have hl (i: H.ThinP)(w:Travel S Y l): Items H i (f i w):=by
    exact ⟨fun x y=> congr_arg (turnWeight Y u w.1*·) ((hh i w).1 x y), measurable_const.mul (hh i w).2.1, fun x y h=> congr_arg (turnWeight Y u w.1*·) ((hh i w).2.2 x y h)⟩
  intro g₀; refine ⟨fun x y=> Finset.prod_congr rfl fun i _=> (hl _ (q i)).1 x y,Finset.measurable_fun_prod _ (fun i _=> (hl _ (q i)).2.1),?_,fun V hV Z _ _ _ v y hy hv=>?_⟩
  · intro U V hx; have hA i : H.smallAt (k.2 i)⊆Θ':= subset_biUnion_of_mem (H.smallAt ∘ k.snd) (mem_univ i)
    exact Finset.prod_congr rfl fun i _=> (hl _ (q i)).2.2 U V (agrees_mono hx (Finset.coe_subset.mpr (hA i)))
  have hz(i:Z₀)(w:Travel S Y l) : Brush j (wU (k.2 i) w) 1 ((f (k.2 i) w) ∘ v) y:=by
    have hl : c'≤1:= (le_mul_of_one_le_left (budget_nonneg (hB.leases.hit 0)) hp).trans hs
    have ht:= (recovers (Palette.team Y w.1) H χ (k.2 i) hk U N hB h hζ hH hl hL V (scopeFlag H k V hV i) w.2) Z v y hy hv
    have hT :0≤turnWeight Y u w.1:= twN H Y u hU w.1
    have hh' := ht.smul (turnWeight Y u w.1); rw [Real.norm_of_nonneg hT] at hh'; exact hh'
  exact Products.earns (fun i t'=> f (k.2 i) t' ∘ v) (fun i=> wU (k.2 i)) hz q

local notation "C₀"=> channel H χ Y u l k
variable (P':BudgetPoint) (he: P'.threshold=Pressure.temp s)(hJ:P'.order≤j)(hF:P'.B=radiusB s)(n':ℕ)(hn:P'.power≤n') (x':ℝ)(hy:0≤x')(hv:Sailor G P'.threshold x' j)(hZ:j*x' ≤ v₀)
abbrev wageScale (P':BudgetPoint)(j n:ℕ) :ℝ:= (shiftG s*(1+ ↑(coverNumber P'.B Θ')))^(j*n)
local notation "a₀"=> wageScale H k P' j n'
-- adapt Unroll.germs
include he hJ hF hn hv hy hZ
lemma via (q:T')(o₁:Site c)(hx:o₁∈Θ'):
    P'.Regular Θ' (C₀ q) ∧ P'.supBounds o₁ Θ' (C₀ q) ((a₀)*cCost H χ Y u l k N D x K θ q):=by -- x notation collision !!! rename
  let Z:= reachability k; let L:=C₀ q
  obtain ⟨hi,hm,hL,hA⟩:= borderL H χ Y u hU l k hk U N hB h hζ hH hp hs hL q
  let d:ℝ := shiftG s*(1+ ↑(coverNumber P'.B Z))
  have hK : 1 ≤ d:= by
    unfold d; unfold shiftG
    nlinarith [Nat.cast_nonneg (α:=ℝ) (coverNumber P'.B Z), Nat.cast_nonneg (α:=ℝ) (radiusB s)]
  have hg:= c_nn H χ Y u hU l k hk U N hH q
  have hh U (hhU: Healthy P'.threshold Z U) : ContDiffAt ℝ (↑P'.order : WithTop ℕ∞) (L ∘ increment U) 0:= (charted (hA U (he ▸ hhU)) N.position).of_le (by exact_mod_cast hJ)
  refine ⟨⟨hL,hm,hi,hh,fun U h a ℓ e=> Next.Foundations.left_has a e (hh U h)⟩,⟨mul_nonneg (pow_nonneg (zero_le_one.trans hK) _) hg,fun U hm ℓ he' hD=>?_⟩⟩
  have h0 : ∀ y∈Z, 1+(separation y o₁ :ℝ)≤d:= by
    intro y hy
    have hf := Corona.extent Z P'.B hy hx
    unfold d shiftG; rw [← hF]
    exact le_trans (show _ ≤ 1+(((coverNumber P'.B Z)*(4*P'.B+2) +2*P'.B:ℕ):ℝ) by exact add_le_add_right (by exact_mod_cast hf) _) (by push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) (coverNumber P'.B Z),Nat.cast_nonneg (α:=ℝ) P'.B])
  have hn := costsD (p:=P') (Y:=d) hL hv hy o₁ _ hZ (hA _ (he ▸ hm)) h0 hK ℓ (he'.trans hJ) hD
  apply le_trans hn _; change d^(P'.power*j)*_ ≤ d^(j*n')*_
  rw [Nat.mul_comm P'.power]; gcongr
end YM.LocalTaylorR2.Orbit
