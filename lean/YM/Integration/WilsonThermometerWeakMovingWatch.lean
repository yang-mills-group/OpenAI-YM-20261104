import YM.Integration.WilsonCenteredCalibratedSampling
import YM.Integration.WilsonThermometerWeakWatchedDates
import YM.Integration.WilsonThermometerWeakPublishedResponse

/-! The cutoff-dependent raw reporter and every spectator are evaluated against
the same Wilson measure. Keep each child at its own microscopic rounded site. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerWeakMovingWatch
open Function Set Filter Metric MeasureTheory Analysis Table Spec Lattice Extraction Next.UVStress
open Wilson RG Source PhysicalNext.Repeat.Legato StressFlux.Matching Finset Cells
open WilsonCenteredPhysicalPanel WilsonCenteredCompactBooking WilsonCenteredWatchedShape WilsonCenteredWatchedCylinder
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {n:ℕ} {f:Extraction.Order} {S:Table R.family.book}

open private joined move_cast restrict_test mesh from YM.Integration.WilsonCenteredCalibratedSampling

theorem calibrated (F:Spec.Final R.family f S) (simple:G.Simple)
    {l:Filter (ℕ×ℕ)}[l.NeBot](law:l≤f.fuse)(d:Fin n→ℕ)
    (a:ℕ×ℕ→∀j,R.family.label (d j))(b:∀j,R.family.label (d j))
    (converges:∀j,Tendsto (fun z=>a z j) l (𝓝 (b j)))
    (r:ℝ)(φ:Test n)(W:Watch R.family)
    (clear:∀x∈tsupport (φ:Points n→ℂ),joint W r x∈conf _)
    (tie:∀ᵐx ∂volume.restrict (tsupport (φ:Points n→ℂ)),joint W r x∈generic _):
    Tendsto (fun k:ℕ×ℕ=>moment (R.family.beta k.1 k.2) (fun U=>
      cylinder R d k (a k) (mass R φ r k) U*W.plot k.1 k.2 U)) l
      (𝓝 (WilsonCenteredWatchedLimit.reading (S:=S) R d b φ W r)):=by
  let join := fun (t:∀i,R.family.label (d i))=>RG17.joinRef R.family d
    (e:=fun i=>(W.q i).1) t (fun j=>(W.q j).2)
  have coords (i:Fin (n+W.n)):Tendsto (fun k=>join (a k) i) l (𝓝 (join b i)):=by
    cases i using Fin.addCases with
    | left i=>simp only [join,RG17.joinRef,Fin.addCases_left];exact move_cast R (Fin.append_left ..) (converges i)
    | right i=>simp only [join,RG17.joinRef,Fin.addCases_right];exact tendsto_const_nhds
  let K := tsupport (φ:Points n→ℂ)
  have passage:= WilsonCenteredMeasuredJunction.original F law
    (μ:=volume.restrict K) (joint W r) (φ:Points n→ℂ) (join b) (fun k=>join (a k))
    (R.again simple).1.control (continuous_joint W r) φ.hasCompactSupport clear
    (ae_restrict_mem φ.hasCompactSupport.measurableSet) tie
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).restrict coords
  have read (T:Table R.family.book)(t:∀j,R.family.label (d j)) :
      (∫x in K,φ x*T.value _ (joint W r x) (join t)) =
      φ.applyTo (fun x=>T.read (joint W r x) (tags R d t W)) :=by
    rw [←joined R d t W]
    exact restrict_test φ _
  rw [read S b] at passage
  refine passage.congr' ?_
  filter_upwards [(mesh (f:=f) W.t).filter_mono law] with k late
  exact (read (rounded R.family k.1 k.2) (a k)).trans
    (WilsonCenteredWatchedCylinder.original R d (a k) W φ r late).symm

open private read from YM.Integration.WilsonCenteredWatchedCylinder

open WilsonThermometerWeakPublishedWatch WilsonThermometerWeakPublishedResponse
open WilsonPositionThermometerCapStation WilsonPositionPhysicalCellTest
open Trace.Pilot OPE OPE.Orbits

theorem screened_full {cap:ℕ}(d:Fin n→Fin (cap+1))(u:∀i,R.family.label (d i))(φ:Test n)
    (W:Watch R.family)(ρ:ℝ){N p:ℕ}(hw:W.t≤N):
    screened d φ W ρ N p (fun _=>u) Finset.univ =
    moment (R.family.beta N p) (fun U=>cylinder R (fun i=>(d i).val) (N,p) u
       (WilsonCenteredCompactBooking.mass R φ ρ (N,p)) U*W.plot N p U):=by
  rw [WilsonCenteredWatchedCylinder.original R (fun i=>(d i).val) u W φ ρ hw]
  apply integral_congr_ae
  filter_upwards with x
  congr 1
  rw [read R (fun i=>(d i).val) u W hw ρ x,R.family.num]
  apply integral_congr_ae
  filter_upwards with U
  change _=(∏i,R.family.seen (tags R (fun i=>(d i).val) u W i)
    (Fin.append (WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x) (W.among N p) i) U)
  rw [Fin.prod_univ_add]
  simp only [WilsonCenteredWatchedCylinder.tags,Fin.append_left,Fin.append_right]
  change (∏i:(Finset.univ:Finset (Fin n)),_) * _ = (∏i:Fin n,_) * _
  congr 1
  exact (Finset.prod_subtype (p:=fun i:Fin n=>i∈(Finset.univ:Finset (Fin n))) (Finset.univ:Finset (Fin n)) (fun _=>Iff.rfl)
    (fun i=>R.family.O N p (u i) ((WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) x) i) U)).symm

end YM.Integration.WilsonThermometerWeakMovingWatch
