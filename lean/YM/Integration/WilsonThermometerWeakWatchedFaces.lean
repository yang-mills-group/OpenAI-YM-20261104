import YM.Integration.WilsonThermometerWeakMovingWatch

/-! Every physical subword uses the literal Wilson units in its inactive
places, with the original calibrated moving columns and the same spectator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakWatchedFaces
open Function Set Filter Metric MeasureTheory Analysis Table Spec Lattice Extraction Next.UVStress
open Wilson RG Source PhysicalNext.Repeat.Legato StressFlux.Matching Finset Cells
open Trace.Pilot OPE OPE.Orbits Climb PhysMS
open WilsonPositionThermometerCapStation WilsonThermometerWeakPublishedWatch
open WilsonThermometerWeakPublishedResponse WilsonCenteredWatchedShape
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n cap:ℕ} (d:Fin n→Fin (cap+1))
    {f:Extraction.Order}{S:Table R.family.book}

def mask (s:Finset (Fin n))(u:∀i,R.family.label (d i))(i:Fin n):R.family.label (d i):=
  if i∈s then u i else R.family.refUnit (d i)

def heard (Z:Group R.family cap)(w:∀i,(Bel R.family.book).Field (d i))(W:Watch R.family)(ρ:ℝ)
    (s:Finset (Fin n))(x:Points n):ℂ:= S.read (joint W ρ x)
    (WilsonCenteredWatchedCylinder.tags R (fun i=>(d i).val) (mask R d s
      (fun i=>Z.lift (index Z (d i)) (Z.change (d i) (w i)))) W)

private theorem erased (u:∀i,R.family.label (d i))(s:Finset (Fin n))(φ:Test n)(W:Watch R.family)
    (ρ:ℝ)(N p:ℕ)(started:∀i,R.family.ref (d i)≤N):
    screened d φ W ρ N p (fun _=>mask R d s u) univ=screened d φ W ρ N p (fun _=>u) s:=by
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  apply integral_congr_ae
  filter_upwards with U
  let c:=WilsonPositionPhysicalCellTest.site (R:=R) ρ (N,p) z
  let op (v:∀i,R.family.label (d i))(i:Fin n):=R.family.O N p (v i) (c i) U
  change (∏i:(univ:Finset (Fin n)),op (mask R d s u) i)*W.plot N p U=(∏i:s,op u i)*W.plot N p U
  congr 1
  rw [←prod_subtype (univ:Finset (Fin n)) (fun _=>Iff.rfl),←prod_subtype s (fun _=>Iff.rfl)]
  calc _=∏i∈s,op (mask R d s u) i:=(prod_subset (subset_univ s) (fun i _ h=>by
           dsimp [op,mask];rw [if_neg h,R.family.constant R.makes _ (started i) _];rfl)).symm
       _=_:=prod_congr rfl fun i h=>by simp only [op,mask,if_pos h]

theorem onRoom (F:Spec.Final R.family f S)(simple:G.Simple){l:Filter (ℕ×ℕ)}[l.NeBot]
    (law:l≤f.fuse)(Z:Group R.family cap)(w:∀i,(Bel R.family.book).Field (d i))
    (landing:Tendsto Z.station.wheel.atCut l (𝓝 Z.lift))(W:Watch R.family)
    (ρ:ℝ)(s:Finset (Fin n))(φ:Test n)
    (clear:∀x∈tsupport (φ:Points n→ℂ),joint W ρ x∈conf _)
    (tie:∀ᵐx ∂volume.restrict (tsupport (φ:Points n→ℂ)),joint W ρ x∈generic _):
    Tendsto (nominated d w Z φ W ρ s) l (𝓝 (φ.applyTo (heard (S:=S) R d Z w W ρ s))):=by
  let a (k:ℕ×ℕ)(i:Fin n):=Z.station.wheel.atCut k (index Z (d i)) (Z.change (d i) (w i))
  let b (i:Fin n):=Z.lift (index Z (d i)) (Z.change (d i) (w i))
  have moves (i:Fin n):Tendsto (fun k=>mask R d s (a k) i) l (𝓝 (mask R d s b i)):=by
    by_cases hi:i∈s
    · simp only [mask,if_pos hi]
      have exc:Continuous (fun X:Lifts R.family Z.horizon=>X (index Z (d i)) (Z.change (d i) (w i))):=
        (continuous_apply _).clm_apply continuous_const
      exact exc.continuousAt.tendsto.comp landing
    · simp only [mask,if_neg hi];exact tendsto_const_nhds
  have exact_read:=WilsonThermometerWeakMovingWatch.calibrated R F simple law (fun i=>(d i).val)
    (fun k=>mask R d s (a k)) (mask R d s b) moves ρ φ W
    clear tie
  have mesh (m:ℕ):∀ᶠk:ℕ×ℕ in l,m≤k.1:=by
    have pre:∀ᶠk:ℕ×ℕ in f.fuse,m≤k.1:=by
      rw [Extraction.Order.fused,Extraction.Order.late]
      exact Eventually.of_forall fun _=>f.mesh.cofinal.eventually_ge_atTop m
    exact pre.filter_mono law
  refine exact_read.congr' ?_
  filter_upwards [mesh W.t,eventually_all.mpr (fun i=>mesh (R.family.ref (d i)))] with k hw hN
  exact (WilsonThermometerWeakMovingWatch.screened_full R d (mask R d s (a k)) φ W ρ hw).symm.trans
    (erased R d (a k) s φ W ρ k.1 k.2 hN)

end YM.Integration.WilsonThermometerWeakWatchedFaces
end
