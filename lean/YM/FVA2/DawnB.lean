import YM.FVA2.PlateP
/-!
# The regulated (meromorphic PS) Gram argument; need *physical* sector comparison.

Use point Gram and clearance estimates rather than fixed-radius smoothing.
Target positive definite. Does not require finite positive matrix symmetric, but approximations do converge.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace YM.FVA2.Counterpart
open Function Filter Set MeasureTheory
open Pert Pert.Position Maxwell Maxwell.Free PositionX
open PositionX.Jet
open Wilson Lattice Gauge PertExtension PertExtension.Chart PertExtension.LatticePT
open MS MS.Menus MS.Land MS.Theater MS.Tone MS.Book MS.Book.Program MS.Book.Convolve MS.Orbit MS.Tide MS.Rake
open Clock Score Based PairCoords Modes Paper Trans ColorCode Attend BoxOffice Blaze Frost ArchTurn
open PowerSeries WorldJet Metric Pond Fountain
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {Q: Booked (wings G)}(V:Warehouse G)(P: Prescription (wings G))(M:MS_Data G Q)
variable (H:ExactSpin V P)(HI:Trusted P) (he: MixedStory.AllProfiles M V P)
variable {m d:ℕ}(q:ℕ+)(hq:1 < q.val) (j:ℕ) (μ:ℝ)
local notation "Y"=> V.F
local notation "I"=> Fin m
local notation "Ω"=> sameAxis V.F d
local notation "N"=> LatticePT.side q
local notation "Z"=> epsilon q
local notation "ε"=> ( epsilon q j )
local notation "φ"=> Pond.clock q j
variable (v: Test m)(X:Fin m→ E V.F d) (u: Grid.offsets q m j) (t: LatticePT.Native q j)
-- leading price recurrence.
def rawL (d:ℕ):= (BoxOffice.view V (side_even q j) (fund q G j) (gates q G j) (Z j) (fun i=>u i + t) d)
-- `me` needed world.
local notation "D"=> bareD V P ε (μ-φ) 0 d
private lemma Drag_zero (A: Jet.Word (Buffer V.F d))(G0:Court (E V.F d) m Cn)(v:Fin m→ E V.F d) : PowerSeries.coeff 0 (drag V.F A (sameAxis V.F d) G0 v) = coeff 0 ( G0 (frameWord V.F A 0 ∘ v) ) := by
    rw [ atDrag, map_sum ]; let X:=( coeff (R:=ℂ) 0|>.compMultilinearMap G0 ); rw [show coeff 0 (G0 (frameWord V.F A 0 ∘ v))= _ from WorldJet.countr Y Ω X (frameWord V.F A 0 ∘ v) ]; refine Finset.sum_congr rfl fun i _=>?_ ; simp_rw [ coeff_zero_eq_constantCoeff_apply,map_mul,map_prod, ← coeff_zero_eq_constantCoeff_apply, ← Clock.out_coeff, node4 ]; rfl
lemma born_eff : PowerSeries.coeff 0 ( tuition V P H HI q j μ t u d X ) = coeff 0 ( rawL V q j u t d (D ∘ X) ) := by unfold tuition altered; rw [ Drag_zero,frame_projects, LinearMap.compMultilinearMap_apply,← Clock.out_coeff,gradeS,Program.pay0 ]; rfl
-- Leadership order zero regulator for non-family fields at positions, via Raw.t layer
variable (T:(k:ℕ)→ LatticePT.Native q k) (A:(k:ℕ)→ Grid.offsets q m k)
variable (hT:∀ k,T k∈ origins q k){x:Points m}(hK:x∈conf m)(hA:Tendsto (fun i=>Grid.sample q i (A i)) atTop (𝓝 x))
private def preL (d:ℕ) := (coeff (R:=ℂ) 0).compMultilinearMap ( BoxOffice.key V (side_even q j) (fund q G j) (gates q G j) ε (fun i=> A j i + T j ) d )
private lemma atLabel (p: Fin m→ V.Atom d) (j:ℕ): preL V q j T A d ( (V.scene d).basis ∘ p )= (finiteQ (members V p) q T j (A j):ℂ):= by
   obtain hp:= BoxOffice.point V (side_even q j) (fund q G j) (gates q G j) (epsilon q j) (fun i=> A j i + T j) p 0
   apply mul_left_cancel₀ (a:= ((epsilon q j:ℂ)^4)^m); swap
   · apply Eq.trans hp; let S:= members V p; let u :Grid.offsets q m j := A j; let X(i:I)(Q:Cover):= Q+(Lattice.lift ∘ u) i; have hv: (Price.ticket (members V p) q j ( Lattice.lift (T j)) (Lattice.lift ∘ A j)) = finiteQ (members V p) q T j (A j):= by
        unfold finiteQ Price.ticket Price.KK; rw [show (wrap (side q j) ∘ fun i=>X i (Price.orig q j (T j)))=(wrap (side q j) ∘ fun i=> X i (Lattice.lift (T j))) from ?_ ]; funext i; unfold X; simp [Function.comp_apply,map_add, Price.casts]
     rw [ ← Complex.ofReal_sum,← hv, ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul ]; have hu := Price.sum_identity S q j (A j) (T j); rw [Fintype.card_fin, pow_mul] at hu; refine congr_arg Complex.ofReal ( Eq.trans ?_ hu ); exact Finset.sum_congr (@univ_unique _ _ _) (fun i _=> rfl)
   exact pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast (epsilon_pos q j).ne'))
include hT hK hA hq
lemma Z_real : Tendsto (fun i=> PowerSeries.coeff 0 (rawL V q i (A i) (T i) d X )) atTop (𝓝 ( visible V.F d x X )) := by
   let U:= RawLabels.physicalLabel V.F d; let p:= U ∘ X; let Y₀:= (visible V.F d x).compLinearMap (fun _=> RawLabels.enroll V.F d); have hu : visible V.F d x X = Y₀ p:= by unfold Y₀; rw [MultilinearMap.compLinearMap_apply ]; apply congr_arg; funext i; exact Eq.symm ( RawLabels.physical_round .. );
   have h (p: Fin m→ V.Atom d): Tendsto ( fun i=> preL V q i T A d ( (V.scene d).basis ∘ p )) atTop (𝓝 (Y₀ ((V.scene d).basis ∘ p))):= by
       let S:=members V p; let z:=electricity S x;
       have h' : Y₀ ((V.scene d).basis ∘ p)=z:= by unfold Y₀; rw [MultilinearMap.compLinearMap_apply,visible_eq ]; apply congr_arg; exact funext fun i=> ( PositionX.Bare.Shop.electrify ( warehouse V ) (p i) ).symm
       rw [ h', ← show (↑z.re:ℂ)=z from Complex.conj_eq_iff_re.mp ( PositionX.Bare.Shop.electricity_real x hK S ) ]; simp_rw [ atLabel ]; exact Complex.ofRealCLM.continuous.continuousAt.tendsto.comp ( ticket_limit _ q hq T hT A hK hA ) -- address_eq.F
   change Tendsto (fun i=> preL V q i T A d p) atTop _; rw [ hu ]; let b:= (V.scene d).basis; have hv (L:MultilinearMap ℂ (fun _ : Fin m=> Labels.Label G d) ℂ): L p=∑ i:Fin m→ V.Atom d, (∏ j, b.coord (i j) (p j))*L (b ∘ i):= by
       conv_lhs => rw [← funext fun j=> b.sum_equivFun (p j) ]
       rw [MultilinearMap.map_sum_finset,Fintype.piFinset_univ ]; exact Finset.sum_congr rfl fun i _=>L.map_smul_univ ..
   rw [ hv Y₀, funext fun i=> hv (preL V q i T A d) ]; exact tendsto_finsetSum _ fun i _=> (h i).const_mul _
end YM.FVA2.Counterpart
