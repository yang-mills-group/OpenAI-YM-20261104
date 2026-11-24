import YM.Integration.ManuscriptQLocalMarkedGradeTail
import YM.LocalTaylorR2.Orbit.Marks
import YM.MergeProof.Tinder
import YM.MergeProof.Buys
import YM.LocalTaylorR2.Orbit.Clocked

/-! This is the actual Run purchase for the auxiliary grade axis. One menu
offer is made at the source cap, with the original presplit signed partners
still occupying their actual physical slots. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Menu
open Function Finset Lattice Wilson RG Marker PhysicalNext.Repeat Lotus
open scoped BigOperators Classical
variable {ι V : Type} [Fintype ι] [DecidableEq V] {G : Gauge} {f : Side}
  {R : Rep G f} {B : Census V}

def gradedHat (M : Hat B R) (r : ℝ) (q : ℕ) : Hat B R :=
  { M with charge := M.charge * (r : ℂ)^q }

@[simp] lemma gradedHat_one (M : Hat B R) (q : ℕ) : gradedHat M 1 q = M := by
  cases M
  simp [gradedHat]

lemma gradedHat_sumFee (M : Hat B R) {r : ℝ} (hr : 0 ≤ r) (q : ℕ) (w : V → ℝ) :
    sumFee (gradedHat M r q) w = sumFee M w * r^q := by
  simp only [gradedHat, sumFee, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hr]
  ring

omit [Fintype ι] in
/-- The one offered unit on the full disk pays every smaller real source
radius with exactly the same rows, signs, crests, support and exponential. -/
lemma graded_offer (a : ι → Hat B R) (ν : ι → ℕ) (o : V → Site f) (w : V → ℝ)
    (hw : ∀ i, 0 < w i) {b : ℕ} {e d t cap : ℝ} (ht : 0 ≤ t) (hc : t ≤ cap)
    (H : Offer o (fun i => gradedHat (a i) cap (ν i)) w b e d) :
    Offer o (fun i => gradedHat (a i) t (ν i)) w b e d := by
  have fee i : fare (gradedHat (a i) t (ν i)) w ≤ fare (gradedHat (a i) cap (ν i)) w := by
    change sumFee (gradedHat (a i) t (ν i)) w * (a i).M.weight ≤
        sumFee (gradedHat (a i) cap (ν i)) w * (a i).M.weight
    rw [gradedHat_sumFee _ ht, gradedHat_sumFee _ (ht.trans hc)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ht hc _) (timed (a i) hw)) (a i).M.profit
  refine ⟨H.sites, fun x => ?_⟩
  apply Extra.Iteration.Cost.mono (H.budget x)
  · intro i
    split
    · exact mul_nonneg (Crew w hw) (Real.exp_pos _).le
    · exact le_rfl
  · intro i
    change (if x ∈ (a i).M.crest then fare (gradedHat (a i) t (ν i)) w *
      Real.exp (e*coverNumber b (a i).M.crest) else 0) ≤
      (if x ∈ (a i).M.crest then fare (gradedHat (a i) cap (ν i)) w *
      Real.exp (e*coverNumber b (a i).M.crest) else 0)
    split
    · exact mul_le_mul_of_nonneg_right (fee i) (Real.exp_pos _).le
    · exact le_rfl
end YM.MergeProof.Menu

noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow.Many
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} (g:G.Simple) {X:Metals G} {D: Rolls X.p} {A : Alloy X D}
    {R: Factor A} {l v:ℝ} {N m n:ℕ}(hm:m<N) {Q: In A.B.a m n} (H: Spring R N m n l v Q)
local notation "I" => Icc l v
local notation "L" => D.L (A.B.a.clock.J (m+1))
local notation "Θ" => A.B.a.S
local notation "J" => A.B.a.clock.J (m+1)
local notation "Jp" => A.B.a.clock.J m
local notation "K" => A.B.a.params m
local notation "wT" => radiusB (A.B.a.clock.hatBeta m)
local notation "k" => Rain.lint R.target A m
local notation "e" => Trio.base k wT
local notation "gV" => A.B.kin.alpha N m
local notation "B" => A.B.a.budget m
local notation "d" => H.ordinal
local notation "Y" => R.target J Jp
local notation "Ze" => R.expense J Jp
local notation "Cμ" => (R.shape.μ J Jp)
local notation "y" => A.B.a.clock.hatBeta m
local notation "O" => Chi.canonical
local notation "X₀" => H.H.base
variable (x: Icc l v)
local notation "hx" => x.property
local notation "W" => houseS H x
local notation "f'" => H.H.sister x
local notation "Tap0" => graft H.H H.knows H.W d x.val
open YM.Merge
open MergeProof Menu
variable (hE : (Q x).p.supportExponent≥100)(hN : 100≤(H.result x).p.supportExponent) (hS: Arrives R.shape A.delay) (hF:Pungent R.shape A.delay)
open YM.LocalTaylorR2 Orbit _root_.YM.Marker MergeProof.Accent
variable (hP : Mallow.RG12.Earned (Mallow.orbitD G) R.shape A.delay) (lP:ℕ)
variable {ι P:Type} [DecidableEq P] [Fintype P][Fintype ι]
  (C:_root_.YM.Marker.Census P)(b₀:ι→Menu.Hat C (Q x))(o:P→ Site (A.B.a.S.side (m+1) n))(r:P→ℝ)
set_option quotPrecheck false
local notation "o₀"=> (A.B.a.clock.op m n).ratio.parent ∘ o
local notation "F"=> H.result x
local notation "B'"=> (B).supportExponent
local notation "b₁"=> F -- unused
local notation "s₀"=> Mallow.straw Cμ L G y
local notation "P'"=> (A.B.a.budget m)
local notation "F'"=> A.B.a.clock.op m n
local notation "tx"=> (A.B.a.clock.hatBeta (m+1))
local notation "u₀"=> Mallow.station tx
local notation "u'"=> CalendarStep.loss J
local notation "Θ'"=> (houseS H x)
local notation "M'"=> fun i=> (b₀ i).M
local notation "M₀"=> fun i=> Menu.sumFee (b₀ i) r
local notation "M₁"=> fun i=> Menu.sing (b₀ i) r
local notation "g'"=>pupilK H x M' M₀

set_option maxHeartbeats 200000 in
include hE hN hS hP hm g in
/-- Direct two-tree purchase on the original Spring. Each finite selection
of true signed bookings with the prescribed total degree is bounded with
every independent input color, every site and all authenticated derivatives. -/
lemma gradedSail (hb : ∀ i, 0 < r i) (hs : Extra.Multi.Occupancy o₀ (J+1))
    (ν : ι → ℕ) (η : ℝ) (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (ht : Menu.Offer o (fun i => Menu.gradedHat (b₀ i) (tx^((1-η)/2)) (ν i)) r
      ((Q x).p.B) ((Q x).p.supportExponent-4) u₀) (hl : lP ≤ J)
    (Fsel : ∀ node : (Θ').fragrances, Finset (Orbit.Booking Θ' M' lP node))
    (degree : ℕ) (hd : degree ≤ lP+1)
    (listed : ∀ node q, q ∈ Fsel node → degree ≤ Orbit.connectedDegree Θ' M' lP node ν q) :
    Orbit.shop Θ' C r o₀ (F).p (fun i => Orbit.measureS Θ' Chi.canonical M' M₀ C M₁ lP i (Fsel i))
      (tx ^ Tail.requested degree (u'+η*degree)) := by
  let Rπ := houseS H x
  have hC := hS _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
  let Gx := minted_same R.shape hP
  have hK := Gx.word _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
  have hz : tx = betaF G y L := beta_eq A.B.valid m
  have hHop : Palette.shipPrice L Y y (J+1) u₀ := hz.symm ▸ hK.shipping
  have hΞ := Opera.protocol A.B hm R.pledging.conducts.full (n:=n)
  obtain ⟨a',ba,q,t',z,F'₀,t₃,t₄,t₅,t₆,node',hB,hA,N₀,hN'⟩ :=
    hC.1.2 _ _ _ _ hΞ (Q x) _ (houseS H x)
  have he : (B).supportExponent+3 ≤ (Ze).earn := by
    have he' := (R.pledging.agenda _ _ (step_paid A.B.a m)).1
    rw [Rain.jersey (A:=A) (m:=m)|>.2.2.1]
    linarith
  have plot (offered : ι → Menu.Hat C (Q x))
      (h₁ : Menu.Offer o offered r ((Q x).p.B) ((Q x).p.supportExponent-4) u₀) :
      Palette.Plot (fun i => (offered i).M) Θ' (fun i => Menu.sumFee (offered i) r) := by
    apply Photo.bidding Rπ C r hb offered o hC.1.1
    · rw [Rπ.laws.intake.sizes, Rπ.laws.data.funds.length_eq]
      exact hB.covers
    · change 4 ≤ (Y).exp+_+_
      change 100 ≤ B' at hN
      linarith only [he,hN,(Ze).worth,(Ze).first,(Ze).second,(Y).usable,(Y).pos]
    · exact hE
    · exact hz.symm ▸ hK.nonneg
    · exact h₁
    · exact hs
    · exact hHop
  have hβ : 1 ≤ tx := (A.B.a.fits.delayed (m+1)).le
  let cap : ℝ := tx^((1-η)/2)
  have hcap : 1 ≤ cap := Real.one_le_rpow hβ (by linarith)
  have offer (v : ℝ) (hv₀ : 0 ≤ v) (hv₁ : v ≤ cap) :=
    Menu.graded_offer b₀ ν o r hb hv₀ hv₁ ht
  have plain : Menu.Offer o b₀ r ((Q x).p.B) ((Q x).p.supportExponent-4) u₀ := by
    simpa only [Menu.gradedHat_one] using offer 1 zero_le_one hcap
  have raised (t : ℝ) (h1 : 1 ≤ t) (h2 : t ≤ cap) :
      Palette.Plot M' Θ' (Orbit.gradedCharges M₀ ν t) := by
    have h₀ := zero_le_one.trans h1
    have bought := plot _ (offer t h₀ h2)
    change Palette.Plot M' Θ' (fun i => Menu.sumFee (Menu.gradedHat (b₀ i) t (ν i)) r) at bought
    have eqfee : (fun i => Menu.sumFee (Menu.gradedHat (b₀ i) t (ν i)) r) = Orbit.gradedCharges M₀ ν t :=
      funext fun i => Menu.gradedHat_sumFee (b₀ i) h₀ (ν i) r
    exact eqfee ▸ bought
  have hV := plot b₀ plain
  have hUsable := Many.usable g hm H x M' M₀ N₀ hS hB hV
  have hr (i) : (b₀ i).s.val.image ((F').ratio.parent ∘ o) ⊆ (M' i).crest.image (F').ratio.parent := by
    intro v hv
    obtain ⟨i', hi, rfl⟩ := mem_image.mp hv
    exact mem_image_of_mem _ (plain.sites _ (mem_image_of_mem _ hi))
  have scoped₀ (i) : GridApprox.Nil.Scoped {v | o₀ v ∈ (M' i).crest.image (F').ratio.parent}
      (M₁ i) := GridApprox.Nil.scope_send _ _ _ ((Accent.room _ _ _).2 (hr i))
  have stamp := hP _ _ (A.B.valid.pays m) _ (step_paid A.B.a m)
  have funds := Rπ.laws.data.funds
  have scheduled := stamp.2.2 ⟨(F').patch,funds.funds.kernel,funds.length_eq,funds.funds.atStep⟩ lP hl
  have hf := params_eq A.B.valid m
  have hOrder : (P').order = (X.p.profile Jp).order := congr_arg RG.Stage.order hf
  have hPower : (P').power = (X.p.profile Jp).power := congr_arg RG.Stage.power hf
  rw [← hOrder, ← hPower] at scheduled
  have final := Orbit.funded_mixed Θ' Chi.canonical M' M₀ hV C M₁ lP r hb
    (fun i => Menu.paid (b₀ i) hb) o₀ scoped₀ (H.result x) hUsable.temp (Ze) he rfl hΞ
    cap hcap ν raised (u') scheduled Fsel degree hd listed
  rw [← hz] at final
  exact (Orbit.capped_price tx hβ degree (u') η hη) ▸ final
end YM.PhysicalNext.Repeat.Mallow.Many


namespace YM.Integration.ManuscriptQLocalMarkedGradeTail
open Function Filter Finset Set Lattice Wilson RG RG.Shoot
open Push Push.PriceCompiler Pressure Pressure.Tube Progress.DirectedRecipe
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open LocalTaylorR2 LocalTaylorR2.Orbit LocalTaylorR2.Candle RG01.Survive MergeProof
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {N period m : ℕ} {hm : m < N}
  (P : ActualRunSpring.Packet R N period m hm)
  {T : Campaign R} {Δ : Daisy.Charity.RG12.Decal G}
local notation "phaseOrder" => R.alloy.B.a.clock.J (m+1)
local notation "fineBeta" => R.alloy.B.a.clock.hatBeta (m+1)
local notation "fineCoupling" => Pert.Asymptotics.regulatorRun R.family N period (m+1)
local notation "fineRep" => P.input P.point.val
local notation "coarseRep" => P.spring.result P.point.val
local notation "stepData" => R.alloy.B.a.clock.op m period
local notation "physicalHouse" => Mallow.houseS P.spring P.point

set_option maxHeartbeats 200000 in
/-- The complete rooted high-grade part on a funded physical Run. Coupling
and cutoff, all finite marker slots, the tree cash and the analytic input
belong to the same Spring. The cap offer is one quote for its primitive
leaves, including their original crests and source normalization. -/
theorem physical_high (hG : G.Simple)
    (paid : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    {ι V : Type} [Fintype ι] [Fintype V] [DecidableEq V]
    (Γ : Marker.Census V) (a : ι → Menu.Hat Γ fineRep)
    (o : V → Site (R.alloy.B.a.S.side (m+1) period)) (w : V → ℝ)
    (hw : ∀ i, 0 < w i) (hOccupy : Extra.Multi.Occupancy ((stepData).ratio.parent ∘ o) (phaseOrder+1))
    (k : ℕ) (hk : k ≤ phaseOrder) (ν : ι → ℕ)
    {η δ : ℝ} (hη : 0 ≤ η) (hη1 : η ≤ 1) (hδ : δ ≤ 1)
    (reserve : CalendarStep.loss phaseOrder + η * (k+1) ≤ δ)
    (quote : Menu.Offer o (fun i => Menu.gradedHat (a i) (fineBeta^((1-η)/2)) (ν i)) w
      (fineRep).p.B ((fineRep).p.supportExponent-4) (Mallow.station fineBeta)) :
    let hats := fun i => (a i).M
    let fees := fun i => Menu.sumFee (a i) w
    let colors := fun i => Menu.sing (a i) w
    let high := fun s : (physicalHouse).fragrances => Finset.univ.filter
      (fun q : Booking physicalHouse hats k s => k+1 ≤ connectedDegree physicalHouse hats k s ν q)
    shop physicalHouse Γ w ((stepData).ratio.parent ∘ o) (coarseRep).p
      (fun i => measureS physicalHouse YM.Push.SectorMeasure.Chi.canonical hats fees Γ colors k i (high i))
      ((Real.sqrt 2 * fineCoupling)^((k+1:ℝ)-δ)) := by
  intro hats fees colors high
  obtain ⟨earned, bounds⟩ := campaign R paid
  have same : (fineRep).p = R.alloy.B.a.budget (m+1) :=
    (P.spring.knows P.point.val P.point.property).1.point
  have hin : 100 ≤ (fineRep).p.supportExponent := by
    rw [same]
    exact bounds (m+1)
  have budget := Mallow.Many.gradedSail hG hm P.spring P.point hin (bounds m)
    R.b.r earned k Γ a o w hw hOccupy ν η hη hη1 quote hk high (k+1)
    le_rfl (fun i q h => (Finset.mem_filter.mp h).2)
  apply Orbit.opened physicalHouse Γ w ((stepData).ratio.parent ∘ o) budget
  have hβ := R.alloy.B.a.fits.delayed (m+1)
  apply (Real.rpow_le_rpow_of_exponent_le hβ.le ?_).trans
    (CalendarStep.coupling_paid k δ hδ hβ
      (((R.T.sticks N period).prices (m+1) (Nat.zero_le _) hm).2))
  unfold Tail.requested
  push_cast
  linarith
end YM.Integration.ManuscriptQLocalMarkedGradeTail

/-! The auxiliary axis acts once on the complete integral of a required
hard component. The same statement holds with any finite set of distinct
source leaves, including several compulsory marks in that component. -/
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

variable (ν : ι → ℕ)

def uncleared (p : H.ThinP) (i : Tickets (sign Y S)) : Prop :=
  ¬ YM.LocalTaylorR2.Clear (p.val \ (Palette.team Y i).signs S)

def markedCompulsory (i : Tickets (sign Y S)) : Prop :=
  (Palette.team Y i).gasDue.Nonempty

def exceptionalTicket (p : H.ThinP) (i : Tickets (sign Y S)) : Prop :=
  uncleared H Y p i ∨ markedCompulsory Y i

/-- Every hard partner integral receives its order once. Soft partners
retain all their original marked and internal vertex degrees. -/
def protectedDegree (p : H.ThinP) (w : Travel S Y l) : ℕ :=
  if exceptionalTicket H Y p w.1 then l+1 else mixedDegree Y l ν w

def auxiliaryState (ζ : ℂ) (p : H.ThinP) (w : Travel S Y l) (U : Config G c) : ℂ :=
  ζ ^ protectedDegree H Y l ν p w * (state H χ p Y u l w U : ℂ)

omit [Fintype ι] in
lemma physical_state (p : H.ThinP) (w : Travel S Y l) (U : Config G c) :
    auxiliaryState H χ Y u l ν 1 p w U = (state H χ p Y u l w U : ℂ) := by
  simp [auxiliaryState]

omit [Fintype ι] in
/-- At every complex auxiliary value the complete distinguished hard
component is exactly one monomial times its real integrated deck. -/
lemma whole_exceptional (ζ : ℂ) (p : H.ThinP) (i : Tickets (sign Y S))
    (hard : exceptionalTicket H Y p i) (U : Config G c) :
    ∑ q : Orders l, auxiliaryState H χ Y u l ν ζ p (i,q) U =
      ζ^(l+1) * (turnWeight Y u i * deck (Palette.team Y i) H χ p U : ℝ) := by
  have real_sum : (∑ q : Orders l, state H χ p Y u l (i,q) U) =
      turnWeight Y u i * deck (Palette.team Y i) H χ p U := by
    change (∑ q : Orders l, turnWeight Y u i * graded (Palette.team Y i) H χ p q U) = _
    rw [← Finset.mul_sum, ← beams_split]
  simp only [auxiliaryState, protectedDegree, if_pos hard]
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, real_sum]

/-- Exact finite regrouping before any absolute value. A hard conditional
integral uses its own full physical deck at one perch and has no other
internal rows. Every untouched partner keeps the original decomposition. -/
def wholePartner (p : H.ThinP) (w : Travel S Y l) (U : Config G c) : ℝ :=
  if exceptionalTicket H Y p w.1 then
    if w.2 = perch l then turnWeight Y u w.1 * deck (Palette.team Y w.1) H χ p U else 0
  else state H χ p Y u l w U

def wholeDisk (ζ : ℂ) (p : H.ThinP) (w : Travel S Y l) (U : Config G c) : ℂ :=
  ζ^(protectedDegree H Y l ν p w) * (wholePartner H χ Y u l p w U : ℝ)

omit [Fintype ι] in
/-- Even at a complex auxiliary disk point, regrouping the original
real conditional integrals leaves their signed partner sum unchanged. -/
lemma whole_disk_sum (ζ : ℂ) (p : H.ThinP) (i : Tickets (sign Y S)) (U : Config G c) :
    ∑ q : Orders l, wholeDisk H χ Y u l ν ζ p (i,q) U =
        ∑ q : Orders l, auxiliaryState H χ Y u l ν ζ p (i,q) U := by
  classical
  by_cases hard : exceptionalTicket H Y p i
  · rw [whole_exceptional H χ Y u l ν ζ p i hard U]
    calc
      _ = ∑ q : Orders l, if q=perch l then
            ζ^(l+1)*(turnWeight Y u i*deck (Palette.team Y i) H χ p U : ℝ) else 0 := by
            refine Finset.sum_congr rfl fun q _ => ?_
            by_cases hq : q=perch l <;> simp [wholeDisk,protectedDegree,wholePartner,hard,hq]
      _ = _ := by simp
  · refine Finset.sum_congr rfl fun q _ => ?_
    simp [wholeDisk,auxiliaryState,wholePartner,hard]

omit [Fintype ι] in
/-- All independent internal orders on a genuinely connected roster may
be pooled before either tree takes an absolute value. -/
lemma whole_booking_sum (ζ : ℂ) (ticket : Z₀ → Tickets (sign Y S)) (U : Config G c) :
    ∑ q : Z₀ → Orders l, ∏ i : Z₀, wholeDisk H χ Y u l ν ζ (k.2 i) (ticket i,q i) U =
      ∑ q : Z₀ → Orders l, ∏ i : Z₀, auxiliaryState H χ Y u l ν ζ (k.2 i) (ticket i,q i) U := by
  let whole (i : Z₀) (q : Orders l) := wholeDisk H χ Y u l ν ζ (k.2 i) (ticket i,q) U
  let raw (i : Z₀) (q : Orders l) := auxiliaryState H χ Y u l ν ζ (k.2 i) (ticket i,q) U
  calc
    _ = ∏ i : Z₀, ∑ q : Orders l, whole i q := (Fintype.prod_sum (f:=whole)).symm
    _ = ∏ i : Z₀, ∑ q : Orders l, raw i q :=
      Finset.prod_congr rfl fun i _ => whole_disk_sum H χ Y u l ν ζ (k.2 i) (ticket i) U
    _ = _ := Fintype.prod_sum (f:=raw)

omit [Fintype ι] in
/-- The identical independently marked polynomial carries this exact
complex-disk regrouping, before taking a mode or normalizing the log. -/
lemma whole_marked_booking (ζ : ℂ) (ticket : Z₀ → Tickets (sign Y S)) (U : Config G c) :
    let field := stampX B (∏ i : Z₀, poles Y B z (ticket i))
    ∑ q : Z₀ → Orders l, ((coeff H k : ℂ) *
        ∏ i : Z₀, wholeDisk H χ Y u l ν ζ (k.2 i) (ticket i,q i) U) • field =
      ∑ q : Z₀ → Orders l, ((coeff H k : ℂ) *
        ∏ i : Z₀, auxiliaryState H χ Y u l ν ζ (k.2 i) (ticket i,q i) U) • field := by
  intro field
  rw [← Finset.sum_smul,← Finset.sum_smul,← Finset.mul_sum,← Finset.mul_sum,
    whole_booking_sum H χ Y u l k ν ζ ticket U]

omit [Fintype ι] in
/-- Empty native grades of an uncleared component carry zero native
price as well as zero field. -/
lemma unmarked_invalid (p : H.ThinP) (i : Tickets (sign Y S))
    (hard : uncleared H Y p i) (q : Orders l) (hq : q ≠ perch l) :
    stationCost H χ Y u l N D x K θ p (i,q) = 0 := by
  have hclear : ¬ (checked (Palette.team Y i) H p ∧ Clear (restP (Palette.team Y i) H p)) :=
    fun h => hard h.2
  simp only [stationCost, receipt, if_neg hclear, hq, false_and, if_false, mul_zero]

include hU hk U hH in
/-- All already booked seed, chain, long and unmarked forced components
pay this whole-component assignment within their original prices. The
sole outstanding hard case has a distinguished compulsory row and a
clear unmarked rest. -/
lemma protected_le (p : H.ThinP) (w : Travel S Y l) (t : ℝ) (ht : 1 ≤ t)
    (hcase : uncleared H Y p w.1 ∨ ¬ markedCompulsory Y w.1) :
    stationCost H χ Y u l N D x K θ p w * t ^ protectedDegree H Y l ν p w ≤
      stationCost H χ Y u l N D x K θ p w * t ^ mixedDegree Y l ν w := by
  have hw : 0 ≤ stationCost H χ Y u l N D x K θ p w :=
    mul_nonneg (twN H Y u hU _) (recNN (Palette.team Y w.1) H χ p hk U N hH _)
  by_cases he : exceptionalTicket H Y p w.1
  · rw [protectedDegree, if_pos he]
    have hu : uncleared H Y p w.1 := hcase.elim id (fun no => he.resolve_right no)
    by_cases hq : w.2 = perch l
    · apply mul_le_mul_of_nonneg_left _ hw
      apply pow_le_pow_right₀ ht
      unfold mixedDegree
      rw [hq]
      exact Nat.le_add_right _ _
    · obtain ⟨i,q⟩ := w
      rw [unmarked_invalid (D:=D) (x:=x) (K:=K) (θ:=θ) H χ Y u l N p i hu q hq, zero_mul, zero_mul]
  · rw [protectedDegree, if_neg he]

omit [Fintype ι] in
/-- For any connected term, the auxiliary exponent is the sum of the
degrees of its genuine distinct *components*. -/
lemma auxiliary_channel (ζ : ℂ) (q : Booking H Y l k) (U : Config G c) :
    (∏ i : Z₀, auxiliaryState H χ Y u l ν ζ (k.2 i) (q i) U) =
      ζ ^ (∑ i : Z₀, protectedDegree H Y l ν (k.2 i) (q i)) *
        (channel H χ Y u l k q U : ℝ) := by
  unfold auxiliaryState
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Complex.ofReal_prod]

omit [Fintype ι] in
/-- A real collection on exclusively ordinary input slots has no
distinguished compulsory partner, for every source ticket. -/
lemma regular_tickets (ordinary : ∀ i n, (Y i).turn ≠ .gasKey n)
    (s : Tickets (sign Y S)) : ¬ markedCompulsory Y s := by
  rintro ⟨n, hn⟩
  obtain ⟨a, ha, eq⟩ := (Lotus.Team.asked (Palette.team Y s) n).mp hn
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  exact ordinary i n eq

abbrev protectedConnected (q : Booking H Y l k) : ℕ :=
  ∑ i : Z₀, protectedDegree H Y l ν (k.2 i) (q i)

/-- Through l+1, the physical high field of covered exceptional integrals
is unchanged by putting their complete contents into exactly one top
grade, including any ordinary or other required partners. -/
lemma funded_protected_filter
    (covered : ∀ (p : H.ThinP) (t : Tickets (sign Y S)),
      markedCompulsory Y t → uncleared H Y p t ∨ ∃ a ∈ t.val, l+1 ≤ ν a)
    {r : ℕ} (hr : r ≤ l+1) (U : Config G c) :
    measureS H χ Y u B z l k
      (univ.filter (fun q : Booking H Y l k => r ≤ protectedConnected H Y l k ν q)) U =
    measureS H χ Y u B z l k
      (univ.filter (fun q : Booking H Y l k => r ≤ connectedDegree H Y l k ν q)) U := by
  unfold measureS
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases active : ∀ i : Z₀, state H χ (k.2 i) Y u l (q i) U ≠ 0
  · by_cases exceptional : ∃ i : Z₀, exceptionalTicket H Y (k.2 i) (q i).1
    · obtain ⟨i, hi⟩ := exceptional
      have hI : l+1 ≤ mixedDegree Y l ν (q i) := by
        have paid : uncleared H Y (k.2 i) (q i).1 ∨ ∃ a ∈ (q i).1.val, l+1 ≤ ν a :=
          hi.elim Or.inl (covered (k.2 i) (q i).1)
        rcases paid with rest | ⟨row,memRow,degree⟩
        · have top : (q i).2 = perch l := by
            by_contra hq
            have he := congrFun (graded_dead (Palette.team Y (q i).1) H χ (k.2 i)
              (fun h => rest h.2) (q i).2) U
            exact active i (by simp only [state, he, if_neg hq, Pi.zero_apply, mul_zero])
          unfold mixedDegree
          rw [top]
          exact Nat.le_add_right _ _
        · have price : ν row ≤ ∑ a ∈ (q i).1.val, ν a :=
            Finset.single_le_sum (fun a _ => Nat.zero_le (ν a)) memRow
          exact (degree.trans price).trans (Nat.le_add_left _ _)
      have hP : l+1 ≤ protectedDegree H Y l ν (k.2 i) (q i) := by
        rw [protectedDegree, if_pos hi]
      have hA : r ≤ connectedDegree H Y l k ν q :=
        (hr.trans hI).trans (Finset.single_le_sum
          (f:=fun j : Z₀ => mixedDegree Y l ν (q j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      have hB : r ≤ protectedConnected H Y l k ν q := by
        unfold protectedConnected
        exact (hr.trans hP).trans (Finset.single_le_sum
          (f:=fun j : Z₀ => protectedDegree H Y l ν (k.2 j) (q j))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
      rw [if_pos hA, if_pos hB]
    · have equal : protectedConnected H Y l k ν q = connectedDegree H Y l k ν q := by
        apply Finset.sum_congr rfl
        intro i _
        exact if_neg (fun hi => exceptional ⟨i, hi⟩)
      rw [equal]
  · push Not at active
    obtain ⟨i, hi⟩ := active
    have zero : channel H χ Y u l k q U = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    have vanish : slice H χ Y u B z l k q U = 0 := by simp only [slice, zero, mul_zero, Complex.ofReal_zero, zero_smul]
    simp only [vanish, ite_self]

lemma covered_filter
    (covered : ∀ (p : H.ThinP) (t : Tickets (sign Y S)),
      markedCompulsory Y t → uncleared H Y p t)
    {r : ℕ} (hr : r ≤ l+1) (U : Config G c) :
    measureS H χ Y u B z l k
      (univ.filter (fun q : Booking H Y l k => r ≤ protectedConnected H Y l k ν q)) U =
    measureS H χ Y u B z l k
      (univ.filter (fun q : Booking H Y l k => r ≤ connectedDegree H Y l k ν q)) U :=
  funded_protected_filter H χ Y u B z l k ν (fun p t h => Or.inl (covered p t h)) hr U

/-- Every original compulsory marker is charged at the source using
its own rooted divided FullBudget. Ordinary interior grades are retained,
and each whole exceptional integral is given only one top grade. -/
lemma rooted_forced_filter
    (forced : ∀ i n, (Y i).turn = .gasKey n → l+1 ≤ ν i)
    {r : ℕ} (hr : r ≤ l+1) (U : Config G c) :
    measureS H χ Y u B z l k
      (univ.filter (fun q : Booking H Y l k => r ≤ protectedConnected H Y l k ν q)) U =
    measureS H χ Y u B z l k
      (univ.filter (fun q : Booking H Y l k => r ≤ connectedDegree H Y l k ν q)) U := by
  apply funded_protected_filter H χ Y u B z l k ν _ hr U
  intro p t hard
  right
  obtain ⟨n,hn⟩ := hard
  obtain ⟨row,source,eq⟩ := (Lotus.Team.asked (Palette.team Y t) n).mp hn
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp source
  exact ⟨i,hi,forced i n eq⟩

lemma ordinary_filter (ordinary : ∀ i n, (Y i).turn ≠ .gasKey n)
    {r : ℕ} (hr : r ≤ l+1) (U : Config G c) :
    measureS H χ Y u B z l k
      (univ.filter (fun q : Booking H Y l k => r ≤ protectedConnected H Y l k ν q)) U =
    measureS H χ Y u B z l k
      (univ.filter (fun q : Booking H Y l k => r ≤ connectedDegree H Y l k ν q)) U :=
  covered_filter H χ Y u B z l k ν (fun _ t h => (regular_tickets Y ordinary t h).elim) hr U
end YM.LocalTaylorR2.Orbit

/-! The temporary marker radii are a choice of normalization of each
finite booking. All restored sums carry their original fields,
nilpotent modes, supports and differentiated purchases. -/
set_option autoImplicit false
noncomputable section
namespace YM.LocalTaylorR2.Orbit
open Function Filter Finset MeasureTheory Matrix Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell Channel SliceRows Coat Control Window Pulse Footprint Raw Matter Mask
open PhysicalNext.Repeat Lotus Packets Greenbelt Daisy Port RG01.Survive Candle
open MeasureTheory Gas Ursell
open _root_.YM.Marker Merge Switch Palette MergeProof Accent GridRenewal.Rain GridApprox.Nil
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {P : Teller G} {T : Tube G S}
  {R : Rep G f} {W s μ C : ℝ} {Q : YM.ConnectedActivityE6.Target G P}
  {o : ConnectedActivityE6.Target.Order G W}
  (H : Cash W s μ L Q o C T R) (χ : Chi)
  {ι V : Type} [Fintype ι] [DecidableEq V]
  (Γ : _root_.YM.Marker.Census V) (M : ι → Menu.Hat Γ R)
local notation "leaves" => fun i => Menu.Hat.M (M i)
local notation "fees" => fun (w : V → ℝ) i => Menu.sumFee (M i) w
local notation "ink" => fun (w : V → ℝ) i => Menu.sing (M i) w

omit [Fintype ι] in
/-- Source charge times normalized color is the radius-independent,
physical stamped leaflet on each full partner. -/
lemma stamped_ticket (w : V → ℝ) (hw : ∀ i, 0 < w i)
    (q : Tickets (Palette.sign leaves S)) :
    ((turnWeight leaves (fees w) q : ℝ) : ℂ) • poles leaves Γ (ink w) q =
        ∏ i ∈ q.val, Menu.stamp (M i) := by
  simp_rw [← Menu.purchase _ hw]
  unfold turnWeight poles
  rw [Finset.prod_smul, ← Complex.ofReal_prod]

omit [Fintype ι] in
lemma stamped_slice (w : V → ℝ) (hw : ∀ i, 0 < w i)
    (l : ℕ) (k : H.fragrances) (q : Booking H leaves l k) (U : Config G c) :
    slice H χ leaves (fees w) Γ (ink w) l k q U =
      ((coeff H k * ∏ a, graded (Palette.team leaves (q a).1) H χ (k.2 a) (q a).2 U : ℝ) : ℂ) •
        stampX Γ (∏ a, ∏ i ∈ (q a).1.val, Menu.stamp (M i)) := by
  have terms : ((∏ a, turnWeight leaves (fees w) (q a).1 : ℝ) : ℂ) •
      (∏ a, poles leaves Γ (ink w) (q a).1) = ∏ a, ∏ i ∈ (q a).1.val, Menu.stamp (M i) := by
    simp_rw [← stamped_ticket Γ M w hw]
    rw [Finset.prod_smul, ← Complex.ofReal_prod]
  unfold slice channel state petition currentPoly
  rw [Finset.prod_mul_distrib, ← terms, map_smul, smul_smul]
  congr 1
  simp only [Complex.ofReal_mul]
  ring

omit [Fintype ι] in
/-- Every finite selection, including any high-grade filter, reads
the identical physical polynomial at both positive source radii. -/
lemma same_selection (w v : V → ℝ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (l : ℕ) (k : H.fragrances) (F : Finset (Booking H leaves l k)) :
    measureS H χ leaves (fees v) Γ (ink v) l k F =
        measureS H χ leaves (fees w) Γ (ink w) l k F := by
  funext U
  unfold measureS
  exact Finset.sum_congr rfl (fun q _ =>
    (stamped_slice H χ Γ M v hv l k q U).trans (stamped_slice H χ Γ M w hw l k q U).symm)

variable {Γ} {p : BudgetPoint} {Z : H.fragrances → Config G c → Poly Γ}
  {r₀ : V → Site c} {v w : V → ℝ} {e : ℝ}

omit [Fintype ι] in
lemma restore_words {u : ℝ} (h : ∀ i : Γ.Mode, Poly.toll w i ≤ u * Poly.toll v i)
    (A : GridApprox.Nil.Sheet Γ) (hA : 0 ≤ A) :
    GridApprox.Nil.wordsPrice w A ≤ u * GridApprox.Nil.wordsPrice v A := by
  unfold GridApprox.Nil.wordsPrice
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => (mul_le_mul_of_nonneg_right (h i) (hA i)).trans_eq (mul_assoc ..))

omit [Fintype ι] in
lemma restore_shop {u : ℝ} (hu : 0 ≤ u)
    (h : ∀ i : Γ.Mode, Poly.toll w i ≤ u * Poly.toll v i) (ht : shop H Γ v r₀ p Z e) :
    shop H Γ w r₀ p Z (u*e) := by
  obtain ⟨f,hf,hit,all⟩ := ht
  refine ⟨fun x => u*f x, hf.mul_left u, _root_.YM.AnalyticBridge.VerifiedReset.Quotes.hit_scale hu hit, fun i => ?_⟩
  obtain ⟨sheet,hs,hfee,on_support,properties⟩ := all i
  exact ⟨sheet,hs,(restore_words h sheet hs).trans (mul_le_mul_of_nonneg_left hfee hu),on_support,properties⟩

variable [Fintype V]
omit [Fintype ι] in
lemma restore_toll (β a : ℝ) (hβ : 1 ≤ β) (ha : 0 ≤ a) (hw : ∀ i, 0 < w i)
    (i : Γ.Mode) : Poly.toll w i ≤ β^(a * Fintype.card V) *
      Poly.toll (fun j => β^(-a)*w j) i := by
  have hcard : (i.val.card : ℝ) ≤ Fintype.card V := by exact_mod_cast Finset.card_le_univ i.val
  have hpos := zero_lt_one.trans_le hβ
  have price : 1 ≤ β^(a*Fintype.card V) * (β^(-a))^i.val.card := by
    rw [← Real.rpow_mul_natCast hpos.le, ← Real.rpow_add hpos]
    exact Real.one_le_rpow hβ (by nlinarith only [mul_le_mul_of_nonneg_left hcard ha])
  unfold Poly.toll
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  simpa only [Poly.toll,one_mul,mul_assoc] using
    (mul_le_mul_of_nonneg_right price ((Poly.worth hw i).le))

omit [Fintype V] [Fintype ι] in
lemma restored_power (β : ℝ) (hβ : 0 < β) (r n : ℕ) (κ ε η : ℝ) :
    β^(3*κ*n) * β^(Tail.requested r (ε+η*r)) =
      β^(Tail.requested r (ε+η*r+6*κ*n)) := by
  rw [← Real.rpow_add hβ]
  congr 1
  unfold Tail.requested
  ring
end YM.LocalTaylorR2.Orbit

namespace YM.Integration.ManuscriptQLocalMarkedGradeTail
open Finset LocalTaylorR2
open scoped BigOperators

/-- Explicit common ordering of the grade cap and the finite-source
budget. A single stage suffices for the complete prescribed horizon. -/
theorem reserve_for_request (r n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hsmall : δ ≤ 1) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∃ j₀ : ℕ, ∀ j ≥ j₀,
      CalendarStep.loss j + η*r + 6*CalendarStep.loss j*n ≤ δ := by
  let η := δ / (2*(r+1:ℝ))
  have hr : 0 ≤ (r:ℝ) := Nat.cast_nonneg _
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have denom : 0 < 2*(r+1:ℝ) := by positivity
  have cap : η ≤ 1 := (div_le_iff₀ denom).mpr (by linarith)
  have sep : η*(r+1:ℝ) = δ/2 := by
    unfold η
    field_simp
  have charge : η*r ≤ δ/2 := by
    calc η*(r:ℝ) ≤ η*(r+1:ℝ) := mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hδ.le denom.le)
         _ = _ := sep
  obtain ⟨j₀,hJ⟩ := exists_nat_ge ((2+12*(n:ℝ))/δ)
  refine ⟨η,div_pos hδ denom,cap,j₀,fun j hj => ?_⟩
  have hj₀ : ((2+12*(n:ℝ))/δ) ≤ (j:ℝ) := hJ.trans (by exact_mod_cast hj)
  have top := (div_le_iff₀ hδ).mp hj₀
  have budget : (1+6*(n:ℝ)) / (j+1:ℝ) ≤ δ/2 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  calc CalendarStep.loss j + η*r + 6*CalendarStep.loss j*n =
          (1+6*(n:ℝ))/(j+1:ℝ) + η*r := by unfold CalendarStep.loss; ring
       _ ≤ _ := by linarith
end YM.Integration.ManuscriptQLocalMarkedGradeTail

namespace YM.Integration.ManuscriptQLocalMarkedGradeTail
open LocalTaylorR2

/-- The price of the literal primitive coefficients need only be subpower
for each fixed positive exponent. That exponent and the source cap are
chosen once and persist through all subsequent cutoffs and fields. -/
theorem fixed_source_reserve (r n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hsmall : δ ≤ 1) :
    ∃ η κ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < κ ∧ ∃ j₀ : ℕ, ∀ j ≥ j₀,
      CalendarStep.loss j ≤ κ ∧ CalendarStep.loss j + η*r + 6*κ*n ≤ δ := by
  obtain ⟨η,hη,h₁,j₀,paid⟩ := reserve_for_request r n δ hδ hsmall
  have hκ : 0 < CalendarStep.loss j₀ := by unfold CalendarStep.loss; positivity
  refine ⟨η,CalendarStep.loss j₀,hη,h₁,hκ,j₀,fun j hj => ?_⟩
  have down : CalendarStep.loss j ≤ CalendarStep.loss j₀ := by
    unfold CalendarStep.loss
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact_mod_cast Nat.succ_le_succ hj
  exact ⟨down,by linarith only [down,paid j₀ le_rfl]⟩
end YM.Integration.ManuscriptQLocalMarkedGradeTail

/-! On the original funded Wilson calendar, six surplus total degrees
per external mark restore the temporary marker radii. Only a fixed
finite band remains between the requested degree and the far tail. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalMarkedGradeTail
open Function Filter Finset Set Lattice Wilson RG RG.Shoot
open Push Push.PriceCompiler Pressure Pressure.Tube Progress.DirectedRecipe
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open LocalTaylorR2 LocalTaylorR2.Orbit LocalTaylorR2.Candle RG01.Survive MergeProof
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) {N period m : ℕ} {hm : m < N}
    (P : ActualRunSpring.Packet R N period m hm) {T : Campaign R} {Δ : Daisy.Charity.RG12.Decal G}
local notation "J₀" => R.alloy.B.a.clock.J (m+1)
local notation "β" => R.alloy.B.a.clock.hatBeta (m+1)
local notation "g₀" => Pert.Asymptotics.regulatorRun R.family N period (m+1)
local notation "P₁" => P.input P.point.val
local notation "P₀" => P.spring.result P.point.val
local notation "S₀" => R.alloy.B.a.clock.op m period
local notation "H₀" => Mallow.houseS P.spring P.point

def farOrder (k external : ℕ) := k+6*external

theorem restored_loss (k depth : ℕ) {a η δ : ℝ} (h : a+η*((depth:ℝ)+1)≤δ) :
    Tail.requested k (a+η*((depth+1:ℕ):ℝ))≤Tail.requested k δ := by
  have bound : a+η*((depth+1:ℕ):ℝ)≤δ :=
    (show ((depth+1:ℕ):ℝ)=(depth:ℝ)+1 from Nat.cast_add_one depth).symm ▸ h
  unfold Tail.requested
  linarith only [bound]

theorem far_power {b : ℝ} (hb : 0<b) (k external : ℕ) (t : ℝ) :
    b^(3*(external:ℝ))*b^Tail.requested (farOrder k external+1) t =
      b^Tail.requested (k+1) t := by
  rw [←Real.rpow_add hb]
  congr 1
  unfold Tail.requested farOrder
  push_cast
  ring

/-- Both the disk exponent and the level are selected before the cutoff,
the period, the source packet family and every inserted field. -/
theorem far_stage (k external : ℕ) {δ : ℝ} (hδ : 0<δ) (h1 : δ≤1) :
    ∃ η : ℝ, 0<η ∧ η≤1 ∧ ∃ m₀ : ℕ, ∀ m≥m₀,
      farOrder k external≤R.alloy.B.a.clock.J (m+1) ∧
        CalendarStep.loss (R.alloy.B.a.clock.J (m+1)) + η*(farOrder k external+1)≤δ := by
  obtain ⟨η,κ,hη,hη1,_,j₀,pay⟩ := fixed_source_reserve (farOrder k external+1) 0 δ hδ h1
  let top := max j₀ (farOrder k external)
  have grows : Tendsto R.alloy.B.a.clock.J atTop atTop := R.family.path.levels.fits.deep
  obtain ⟨m₀,stage⟩ := eventually_atTop.mp (grows.eventually (eventually_ge_atTop top))
  refine ⟨η,hη,hη1,m₀,fun m hm => ?_⟩
  have hx := stage (m+1) (by omega)
  refine ⟨(le_max_right _ _).trans hx,?_⟩
  simpa only [Nat.cast_zero,mul_zero,add_zero,Nat.cast_add,Nat.cast_one] using
    (pay _ ((le_max_left _ _).trans hx)).2

variable {ι V : Type} [Fintype ι] [Fintype V] [DecidableEq V]
    (Γ : Marker.Census V) (a : ι → Menu.Hat Γ (P.input P.point.val))
    (o : V → Site (R.alloy.B.a.S.side (m+1) period)) (w : V → ℝ)
    (k : ℕ) (ν : ι → ℕ)
local notation "l" => farOrder k (Fintype.card V)
local notation "hats" => fun i => Menu.Hat.M (a i)
local notation "fees" => fun i => Menu.sumFee (a i) w
local notation "colors" => fun i => Menu.sing (a i) w
local notation "places" => Lattice.Ratio.parent (RG.StepData.ratio S₀) ∘ o

set_option maxHeartbeats 200000

theorem standard_far (_hG : G.Simple) (_paid : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (_hw : ∀ i, 0<w i) (_occupied : Extra.Multi.Occupancy places (J₀+1)) (_hl : l≤J₀)
    {η δ : ℝ} (_hη : 0≤η) (_hη1 : η≤1) (_hδ : δ≤1)
    (_reserve : CalendarStep.loss J₀+η*(l+1)≤δ)
    (_quote : Menu.Offer o (fun i => Menu.gradedHat (a i) (β^((1-η)/2)) (ν i))
      (fun i => β^(-(3:ℝ))*w i) (P₁).p.B ((P₁).p.supportExponent-4) (Mallow.station β))
    (F : ∀ s : (H₀).fragrances, Finset (Booking H₀ hats l s))
    (_listed : ∀ s q, q∈F s → l+1≤connectedDegree H₀ hats l s ν q) :
    shop H₀ Γ w places (P₀).p
      (fun s => measureS H₀ YM.Push.SectorMeasure.Chi.canonical hats fees Γ colors l s (F s))
      ((Real.sqrt 2*g₀)^((k+1:ℝ)-δ)) :=
  let booked := campaign R _paid
  let earned := booked.1
  let bounds := booked.2
  have same : (P₁).p=R.alloy.B.a.budget (m+1) := (P.spring.knows P.point.val P.point.property).1.point
  have hin : 100≤(P₁).p.supportExponent := same.symm ▸ bounds (m+1)
  let r i := β^(-(3:ℝ))*w i
  have hβ := R.alloy.B.a.fits.delayed (m+1)
  have hp : 0<β := zero_lt_one.trans hβ
  have hr i : 0<r i := mul_pos (Real.rpow_pos_of_pos hp _) (_hw i)
  have low := Mallow.Many.gradedSail _hG hm P.spring P.point hin (bounds m) R.b.r earned l Γ a o r hr _occupied
    ν η _hη _hη1 _quote _hl F (l+1) le_rfl _listed
  have toll (mode : Γ.Mode) : Marker.Poly.toll w mode ≤
      β^(3*(Fintype.card V:ℝ))*Marker.Poly.toll r mode :=
    restore_toll (Γ:=Γ) β 3 hβ.le zero_le_three _hw mode
  have restored := restore_shop H₀ (Real.rpow_nonneg hp.le _) toll low
  have sameField (s : (H₀).fragrances) :=
    same_selection H₀ YM.Push.SectorMeasure.Chi.canonical Γ a w r _hw hr l s (F s)
  have eqn : (fun s => measureS H₀ YM.Push.SectorMeasure.Chi.canonical hats
      (fun i => Menu.sumFee (a i) r) Γ (fun i => Menu.sing (a i) r) l s (F s)) =
      fun s => measureS H₀ YM.Push.SectorMeasure.Chi.canonical hats fees Γ colors l s (F s) := funext sameField
  Orbit.opened H₀ Γ w places (eqn ▸ (far_power hp k (Fintype.card V) _ ▸ restored))
    ((Real.rpow_le_rpow_of_exponent_le hβ.le (restored_loss (k+1) l _reserve)).trans
      (CalendarStep.coupling_paid k δ _hδ hβ (((R.T.sticks N period).prices (m+1) (Nat.zero_le _) hm).2)))

theorem standard_protected (_hG : G.Simple) (_paid : R2I.Funded ((Mallow.orbitD G).paired Δ) R T)
    (_hw : ∀ i, 0<w i) (_occupied : Extra.Multi.Occupancy places (J₀+1)) (_hl : l≤J₀)
    (_hard : ∀ i j, (a i).M.turn = .gasKey j → l+1≤ν i)
    {η δ : ℝ} (_hη : 0≤η) (_hη1 : η≤1) (_hδ : δ≤1)
    (_reserve : CalendarStep.loss J₀+η*(l+1)≤δ)
    (_quote : Menu.Offer o (fun i => Menu.gradedHat (a i) (β^((1-η)/2)) (ν i))
      (fun i => β^(-(3:ℝ))*w i) (P₁).p.B ((P₁).p.supportExponent-4) (Mallow.station β)) :
    let F := fun s : (H₀).fragrances => Finset.univ.filter
      (fun q : Booking H₀ hats l s => l+1≤protectedConnected H₀ hats l s ν q)
    shop H₀ Γ w places (P₀).p
      (fun s => measureS H₀ YM.Push.SectorMeasure.Chi.canonical hats fees Γ colors l s (F s))
      ((Real.sqrt 2*g₀)^((k+1:ℝ)-δ)) :=
  let F := fun s : (H₀).fragrances => Finset.univ.filter
    (fun q : Booking H₀ hats l s => l+1≤protectedConnected H₀ hats l s ν q)
  let native := fun s : (H₀).fragrances => Finset.univ.filter
    (fun q : Booking H₀ hats l s => l+1≤connectedDegree H₀ hats l s ν q)
  have bought := standard_far R P Γ a o w k ν _hG _paid _hw _occupied _hl _hη _hη1 _hδ _reserve _quote native
    (fun _ _ h => (Finset.mem_filter.mp h).2)
  have same (s : (H₀).fragrances) :
      measureS H₀ YM.Push.SectorMeasure.Chi.canonical hats fees Γ colors l s (F s) =
        measureS H₀ YM.Push.SectorMeasure.Chi.canonical hats fees Γ colors l s (native s) :=
    funext fun U=>rooted_forced_filter H₀ YM.Push.SectorMeasure.Chi.canonical hats fees Γ colors l s ν _hard le_rfl U
  (congrArg (fun reading => shop H₀ Γ w places (P₀).p reading
    ((Real.sqrt 2*g₀)^((k+1:ℝ)-δ))) (funext same)).mpr bought

theorem finite_band {E X : Type*} [DecidableEq E] [AddCommMonoid X] (A : Finset E)
    (degree : E → ℕ) (r b : ℕ) (hrb : r≤b) (f : E → X) :
    (∑ i ∈ A.filter (fun i => r≤degree i), f i) =
      (∑ i ∈ A.filter (fun i => r≤degree i ∧ degree i<b), f i) +
      ∑ i ∈ A.filter (fun i => b≤degree i), f i := by
  classical
  let low := A.filter (fun i => r≤degree i ∧ degree i<b)
  let high := A.filter (fun i => b≤degree i)
  have dis : Disjoint low high := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_filter.mp hi).2.2.not_ge (Finset.mem_filter.mp hj).2
  have all : A.filter (fun i => r≤degree i)=low∪high := by
    ext i
    simp only [low,high,Finset.mem_filter,Finset.mem_union]
    constructor
    · rintro ⟨ha,hr⟩
      by_cases h : degree i<b
      · exact Or.inl ⟨ha,hr,h⟩
      · exact Or.inr ⟨ha,le_of_not_gt h⟩
    · rintro (⟨ha,hr,_⟩ | ⟨ha,hb⟩)
      · exact ⟨ha,hr⟩
      · exact ⟨ha,hrb.trans hb⟩
  rw [all,Finset.sum_union dis]

end YM.Integration.ManuscriptQLocalMarkedGradeTail
end
