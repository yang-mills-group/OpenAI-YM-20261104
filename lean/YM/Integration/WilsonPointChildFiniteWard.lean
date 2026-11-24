import YM.Integration.WilsonVacuumPreResetFiniteWard
import YM.Integration.WilsonPointChildTables
import YM.FormalBulk08.Reef.Safe
import YM.FormalBulk08.Wine.Cab

/-! The original unaliased finite history preserves nonlinear gauge invariance
    of a charged base word under the single-child forward and exact reset. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPointChildFiniteWard
open Function Finset Filter Lattice Wilson RG Precision Tree Bloch Exterior PowerSeries
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets
open FormalBulk08.Shore FormalBulk08.Lava FormalBulk08.Wine FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open Next.Free Stationary Next.Foundations PhysicalNext.Repeat.Legato
open WilsonVacuumPreResetIndependentForecast
open scoped BigOperators Classical Topology
variable {G:Gauge}{I:Type}[DecidableEq I]{D:I→ℕ}
variable (R:Run G)(u:G.ColorIndex)
local notation "V" => R.family.path.levels
variable (tags:∀j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

theorem recorded {U:Type} [Fintype U] (T:Pap U):flash (rancho T)=T:=by
  apply PowerSeries.ext
  intro e
  let p:=PowerSeries.coeff e T
  change PowerSeries.coeff e (PowerSeries.mk (fun j=>Blue.totalR (rancho T j)))=p
  rw [PowerSeries.coeff_mk]
  have stop:Blue.still (rancho T e) (p.totalDegree+1):=by
    intro r hr
    exact (Lava.marble_eq_zero_iff r p).mpr (MvPolynomial.homogeneousComponent_eq_zero r p (by omega))
  rw [Blue.visible stop]
  simp only [WilsonConditionalTaylorWheelTensors.painted,rancho,Lava.marble_grade]
  exact MvPolynomial.sum_homogeneousComponent p

private theorem scaled {U:Type}[Fintype U](m:ℕ)(p:Pap U):rancho (m • p)=m • rancho p:=by
  have sum (Q:Fin m→Pap U):
      rancho (∑i,Q i)=∑i,rancho (Q i):=by
    funext e r; simp [rancho,_root_.map_sum,←canyon_eq,Finset.sum_apply]
  simpa using sum (fun _=>p)

theorem step (simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    {N j:ℕ}(live:j<N)(n:Side)(T:PChart G (n*(destination V N j).patch.L))
    (old:Rite (flash T) (flash T) 1 0)(m:ℕ):
    let Z:=m • WilsonMarkedFiniteIndependentStep.fixed R u tags N j n T
    Rite (flash Z) (flash Z) 1 0:=by
  let P:=destination V N j
  let C:=prescription R u N j
  let W:=WilsonVacuumPreResetFiniteHistory.action R u tags N (N-(j+1)) (j+1) (n*P.L)
  let F:=Flat.routes ((V).clock.op j 0).patch
  let H:=((V).blocks j 0).branches
  let Z:=Reef.tossed P R.metals.O H F n (tags j n) W (flash T)
  have prior:=WilsonVacuumPreResetFiniteWard.original R u tags simple v funded live (n*P.L)
  have root:(primary P.patch (V).clock.kernel n).ratio.embed 0=0:=by rw [←Ratio.root_embed];exact map_zero _
  have hZ:Rite Z Z 1 0:=Reef.tossed_ward P R.metals.O H F n (tags j n) W prior.1
    (RunFormalChain.fromRun R).receipt ((V).clock.adm j) prior.2 1 0 (flash T) (flash T) (root.symm ▸ old)
  have hC:=Wine.morph (bookH C) (bookU C) 1 0 hZ (book_equal C)
  let U:=Wine.stamp (bookH C) (bookU C) (rancho Z)
  let J:=Wine.canter (bookH C) (bookU C) (wire G n) Z
  have issued:flash (m • U)=m • J:=by
    change flash (m • Wine.stamp (bookH C) (bookU C) (rancho Z))=_
    rw [←Wine.stamp_book,←scaled,recorded]
  change Rite (flash (m • U)) (flash (m • U)) 1 0
  rw [issued]
  intro V' inst a b k ac bc ha hb hk hz hold
  simpa only [map_nsmul] using congrArg (fun y=>m • y) (hC V' a b k ac bc ha hb hk hz hold)

theorem original (simple:G.Simple)(v:ℕ→Gear G→ℝ)(paid:FundedMarkedCoverRows.prices v R.kit)
    (N:ℕ)(d:I→ℕ)(X:Outerm G D)(s:I)
    (bare:∀p: I → Cover,∀f:Pen D {s}→L[ℝ]ℝ,∀n,Rite (flash ((tuftV f (X p {s})).1 n))
      (flash ((tuftV f (X p {s})).1 n)) 1 0)(h j:ℕ)(live:j+h≤N)
    (p:I → Cover)(f:Pen D {s}→L[ℝ]ℝ)(n:Side):
    let Z:=WilsonPointChildTables.finite R u tags N d X s h j p f n
    Rite (flash Z) (flash Z) 1 0:=by
  induction h generalizing j p f n with
  | zero=>exact bare p f n
  | succ h ih=>
    let P:=loose V j
    let T:=WilsonPointChildTables.finite R u tags N d X s h (j+1) (splitQ P p {s} 0)
      (WilsonMarkedFiniteIndependentHistory.probe P {s} f 0) (n*P.L)
    have old:Rite (flash T) (flash T) 1 0:=ih (j+1) (by omega) _ _ _
    let U:=WilsonMarkedFiniteIndependentStep.fixed R u tags N j n T
    have cast:((P.L.val:ℝ)^(d s)) • U=(P.L.val^(d s)) • U:=by rw [←Nat.cast_pow,Nat.cast_smul_eq_nsmul ℝ]
    change Rite (flash (((P.L.val:ℝ)^(d s)) • U)) (flash (((P.L.val:ℝ)^(d s)) • U)) 1 0
    rw [cast]
    exact step R u tags simple v paid (N:=N) (j:=j) (by omega) n T old (P.L.val^(d s))

end YM.Integration.WilsonPointChildFiniteWard

