import YM.Integration.FVA1Physical.TwoReset.MassAffine
import YM.Integration.FVA1Physical.TwoReset.VacuumCover

/-!
# Mass readout determines formal beta^(p)

Not asserting an arbitrary convention for the denominator or guessed
Caliber's compatibility; all markings will be on this same layout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.TwoReset
open Function Filter Finset Lattice RG RG.Supply Pressure Input Org Precision Tree YM.Wilson
open Push Push.AbsoluteSums PriceCompiler PhysicalNext Repeat Further.PhysicalPeriodLimitF933
open ConnectedActivityE6 Push.Uniform Next.Scheduling Extra.Iteration ThroughLaunch Roost Legato
open AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Faith QuadraticLocal.Rebirth Comparison.RG02 Comparison.RG02.Bulk
open AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire AllOrder.Ink AllOrder.Ink.Money
open Laurent Stationary Kinetic.Port Pane Marker Primitives.TwoWave Primitives.TwoWave.RealSlice
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} (R : Run G)
variable {N n i k : ℕ}
set_option quotPrecheck false
local notation "sz"=> R.family.side
local notation "S" => R.alloy.B.a.S
local notation "op"=> R.family.path.levels.clock.op
local notation "B"=> R.alloy.B.kin.path N i
local notation "cl"=> ( R.alloy.B.a.params i ).clip
local notation "T"=> Step.tape ( k+2 )
local notation "W"=> R.alloy.B.a.clock.J (i+1)
local notation "E"=> R.alloy.B.a.clock.J i
local notation "F"=> R.alloy.B.a.clock.adm (i+1)
variable (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
variable (hx:k+2≤ R.alloy.B.a.clock.J i)
local notation "I"=> Card R.rolls D W E F k
variable (Z: Card R.rolls D (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i)
  (R.alloy.B.a.clock.adm (i+1)) k) (hZ:Journey D R.alloy (m:=i) (N:=N) Z)
variable (hi : i<N) (π π' π₀:Layout G) (q q':Pace.Coin)
local notation "G₀" q:max π':max=> Pace.grouping q π' T cl B

-- Quiet affine channel; includes exponential path coefficients. The *output*
-- budget and kernel contain this condition, not requiring as new reserve for history.
structure AffineMass (k:ℕ) : Prop where
  zeroed : q 0=0
  quote : ∀ j ∈ tape (k+2),∃ u v:ℝ,0<u ∧ Floe.StateE.Quoted (π' j) u v
  binding : MassCall R hi π π' q k

-- On this counterterm convention, uniqueness of the formal power
-- prescription. The stencil (cost-bearing) implementation of those powers
-- will remain a choice.
variable (H:AffineMass R hi π π' q k) (H':AffineMass R hi π π₀ q' k)
lemma AffineMass.legal {R k N i hi} {π π':Layout G} {q:Pace.Coin} (H:AffineMass (N:=N) (i:=i) R hi π π' q k): Legal (tape (k+2)) π':= by
  choose a b ha hQ using H.quote;
  exact ⟨fun i hi=> ⟨a i hi,b i hi,ha i hi,(hQ i hi).pay⟩,fun i hi=> (hQ i hi).symm⟩

lemma rainbow (j h j' h' r) (he: ∀ i≤r,j i=j' i):
    (Rebirth.caliber j h).back r=(Rebirth.caliber j' h').back r:=by
  suffices H:(Rebirth.caliber j h).direct r=(Rebirth.caliber j' h').direct r by
    unfold Adjacent.Caliber.back; rw [H]
  let J:=Rebirth.caliber j h; let J':=Rebirth.caliber j' h'
  have hx : J.tariff r= J'.tariff r:= by
    funext x; unfold Adjacent.Caliber.tariff; exact Finset.sum_congr rfl (fun i hi=> by
      have hh: J.measure i=J'.measure i:=by change j i+_=j' i+_; rw [he _ (mem_range_succ_iff.mp hi)]
      rw [hh]) -- align
  have hu (A B': Adjacent.UnitCost) (h:A.rating=B'.rating): A=B':=by cases A; cases B'; congr
  exact hu _ _ (by change (fun t=>(Real.sqrt (J.tariff r t))⁻¹)= fun t=>(Real.sqrt (J'.tariff r t))⁻¹; rw [hx])

include H H'
lemma booked {j:ℕ} (hj:j ≤ k+2) : (G₀ q π') j= (G₀ q' π₀) j:=by
  classical
  funext X x
  let V : Census PUnit := ⟨univ,mem_univ _,fun j=>mem_univ _,fun _ _ _=>mem_univ _⟩
  let U (z:Covers S i X) : Bulk.Colors V G (sz (i+1) z.val) := ⟨0,0,0⟩
  let Y (z:Covers S i X) := (Tree.select (op i z.val).ratio (op i z.val).patch.odd_side).some
  let t (z:Covers S i X) : (op i z.val).Choices := Classical.arbitrary _
  haveI : NeBot (coverFilter S i X) := coverFilter_neBot R.kit.floor _ _
  have ht := Complex.ofReal_injective (neg_injective (tendsto_nhds_unique (H.binding PUnit V X U Y t j hj x) (H'.binding PUnit V X U Y t j hj x)))
  rw [ReadAffine.honor_zero q q' π' π₀] at ht; exact sub_left_inj.mp ht

include Z hZ
variable (g:G.Simple)
include g
lemma backed {j:ℕ} (hp:j≤ k+2): q j=q' j:=by
  have ht := TwoReset.booked R hi π π' π₀ q q' H H' hp
  rw [← hZ.books.south, PriceCompiler.params_eq R.alloy.B.valid i] at ht
  exact ReadAffine.chosen_money g H.quote H'.quote Z.att2 Z.floor2 Z.sworn2 Z.self.downCost ht

omit H'
lemma toChart (X:Side)(j:ℕ) (hp:j≤ k+2) : QuadraticLocal.Faith.Spirit.suction (G₀ 0 π') j =
    Adjacent.born (Faith.Spirit.suction (n:=X) (G₀ q π')) ((Rebirth.caliber q H.zeroed).back (k+2)) 0 (k+2) j:=by
  have h:= Faith.Spirit.returned (n:=X) q H.zeroed (k+2) Z.self.south _ π' T g H.legal Z.self.downCost hp
  rw [← hZ.books.south, PriceCompiler.params_eq R.alloy.B.valid i]; exact h.symm

include H'
lemma stamp_unique :
    (Rebirth.caliber q H.zeroed).back (k+2)=(Rebirth.caliber q' H'.zeroed).back (k+2):= by
  apply rainbow; exact fun i hi'=> backed R D Z hZ hi π π' π₀ q q' H H' g hi'
lemma jet_unique {j:ℕ}(hp:j ≤ k+2) (X: Side) :
    QuadraticLocal.Faith.Spirit.suction (n:=X) (G₀ 0 π') j = QuadraticLocal.Faith.Spirit.suction (n:=X) (G₀ 0 π₀) j := by
  rw [toChart R D Z hZ hi π π' q H g X j hp,toChart R D Z hZ hi π π₀ q' H' g X j hp, stamp_unique R D Z hZ hi π π' π₀ q q' H H' g];
  funext x
  let η:Adjacent.UnitCost:= (Rebirth.caliber q' H'.zeroed).back (k+2)
  let F₁:= Spirit.suction (n:=X) (G₀ q π'); let F₂:= Spirit.suction (n:=X) (G₀ q' π₀)
  have hz : ∀ i≤ k+2, F₁ i= F₂ i:=by
    intro i hj; funext y; exact congr_arg (fun f:Ink.Money.Bills (Coarse G)=> -Complex.ofReal (f X y)) (TwoReset.booked R hi π π' π₀ q q' H H' hj)
  have he : (fun t:ℝ => Adjacent.ages F₁ 0 (k+2) t (η.rating t) x)=(fun t:ℝ=> Adjacent.ages F₂ 0 (k+2) t (η.rating t) x) := by
    funext t; unfold Adjacent.ages Adjacent.cover
    refine congr_arg (_ * ·) (Finset.sum_congr rfl (fun i hi=>?_)); rw [hz i (mem_range_succ_iff.mp hi)]
  exact congr_fun (congr_arg Comparison.RG02.Moving.Path.motion he) j
omit H H' g

include hx
local notation "𝚹"=> litP D R.alloy Q hx Z
lemma calculator (hA : Bid.Larger (G:=G) ( R.family.path.levels.clock.op i n ))
    (hV : π=Z.extra) (hv : π' = (litP D R.alloy Q hx Z).laid Z) (hN : q = (litP D R.alloy Q hx Z).issue Z): AffineMass R hi π π' q k:= by
  refine ⟨ hN ▸ ((𝚹).sustenance.due Z).1, ?_, TwoReset.money R D Q hx hi π π' q Z hZ hA hV hv hN ⟩
  intro j hj; let Y:= (𝚹).sustenance
  obtain ⟨f,hF,H⟩:= Y.rents j hj; rw [hv]; exact ⟨_,_, D.shape k|>.pos ( R.alloy.B.a.clock.J i ) j,H Z⟩
end YM.Integration.FVA1Physical.TwoReset
