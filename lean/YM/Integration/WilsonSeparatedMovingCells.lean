import YM.Integration.WilsonSeparatedSingleMeasure

/-! A genuinely moving exterior for the original complete Wilson
product. The exterior sites may approach the origin with preserved
mutual and central clearance r^b. Every growing cell price, including
its dependence on the degree and arity, is spent explicitly. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedMovingCells
open Function Filter Lattice Wilson Cells Extraction OPE OPE.Cards OPE.Orbits OPE.Log OPE.Log.Trunk.Shuttle
open Frontier6.Road StressFlux.Matching Trace.Pilot
open WilsonWholeLimit SharedIntrinsicWilsonGrid ActualFoundryDetectorSource ContinuumIntrinsicWilsonProduct
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
variable {I E : Type} [Fintype I] [Fintype E] {d : I → ℕ} {D : ℕ}

/-- Every fixed finite exterior admits a positive such exponent on
every chosen original common grid. -/
theorem exponent (P : Plan C D (Fintype.card I) (∑ i,d i)) (de : E → ℕ) :
    ∃ b : ℝ, 0 < b ∧ 3*b < P.h ∧ (∑ i,((de i:ℝ)+1)*(4*b)) < 1/32 := by
  have first : Tendsto (fun b:ℝ=>3*b) (𝓝[>] 0) (𝓝 0) := by
    have idlimit : Tendsto (fun b:ℝ=>b) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero] using (tendsto_const_nhds (x:=(3:ℝ))).mul idlimit
  have total : Tendsto (fun b:ℝ=>∑ i,((de i:ℝ)+1)*(4*b)) (𝓝[>] 0) (𝓝 0) := by
    have c : Continuous (fun b:ℝ=>∑ i,((de i:ℝ)+1)*(4*b)) := by fun_prop
    have at0 : ContinuousAt (fun b:ℝ=>∑ i,((de i:ℝ)+1)*(4*b)) 0 := c.continuousAt
    simpa only [mul_zero,Finset.sum_const_zero] using at0.tendsto.mono_left nhdsWithin_le_nhds
  have positive : ∀ᶠ a:ℝ in 𝓝[>] 0,0<a := self_mem_nhdsWithin
  exact (positive.and ((first.eventually (gt_mem_nhds P.pos)).and
    (total.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/32))))).exists

/-- For every allowed shrinking clearance, one full true cluster is
available before either the far positions or their independently
bounded physical fields. The unselected statement holds without a
coordinate screen; a screened inner supplies all characters as well. -/
theorem original (F : Spec.Final C f S) (fac : Facilities C f S) (anchor : I)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (P : Plan C D (Fintype.card I) (∑ i,d i)) (J : ℝ → PhysMS.tower S) (H : PhysMS.Leading F J)
    (v : (i:I) → (Climb.Bel C.book).Field (d i)) {g : ℝ → ℝ} (hg : Coupling G g) (hG : G.Simple)
    (de : E → ℕ) (R : E → ℝ) (Rpos : ∀ i,0 < R i) {b : ℝ} (bp : 0 < b) (inside : 3*b < P.h)
    (extra : ℝ) (reserve : extra+(∑ i,((de i:ℝ)+1)*(4*b)) < 1/32) (k : ℕ) (ε : ℝ) (εpos : 0 < ε) :
    ∀ᶠ r in trail, ∀ x : I → Cover, Plot C (P.b r) (P.middle r) (P.j r) x →
      (∃ z : C.label D, Cluster F Q J v r (P.b r) (P.j r) x z) ∧
      ∀ z : C.label D, Cluster F Q J v r (P.b r) (P.j r) x z →
        ∀ y : E → E4, ClearOf 0 y (r^b) → Injective (beside (C.S.gridPoint (P.j r) ∘ x) y) →
        ∀ w : Labels S de, (∀ i,‖S.representative _ (w i)‖ ≤ R i) →
          (‖whole S (C.S.gridPoint (P.j r) ∘ x) (PhysMS.Frame.born J r v) y w -
            upon S D 0 y w (S.project D z)‖ ≤ ε*g r^k*r^D*r^extra) ∧
          (Screen (C.S.gridPoint (P.j r) ∘ x) → ∀ s : Viewers F,
            ‖whole (spectator F s) (C.S.gridPoint (P.j r) ∘ x) (PhysMS.Frame.born J r v) y w -
              upon (spectator F s) D 0 y w (S.project D z)‖ ≤ ε*g r^k*r^D*r^extra) := by
  classical
  let ht := PhysMS.to_log_zoom
  obtain ⟨o,scaleO⟩ := found (S:=C.S) ht C.path.levels.fits.mesh (show 0≤2*b by positivity)
  obtain ⟨u,scaleU⟩ := found (S:=C.S) ht C.path.levels.fits.mesh (show 0≤3*b by positivity)
  obtain ⟨n,scaleN⟩ := found (S:=C.S) ht C.path.levels.fits.mesh (show 0≤4*b by positivity)
  have clearance := (PhysMS.length_rate.rpow b).overtakes
    ((RateLE.const (2:ℝ) ht).mul (scaleO.mesh.pays ht)) ht (by linarith only [bp])
  have core := scaleO.mesh.overtakes ((RateLE.const (10:ℝ) ht).mul (scaleU.mesh.pays ht)) ht (by linarith only [bp])
  have separated := scaleU.mesh.overtakes ((RateLE.const ((Fintype.card E:ℝ)*6) ht).mul (scaleN.mesh.pays ht)) ht
    (by linarith only [bp])
  obtain ⟨fee,rate,_,paid⟩ := WilsonSeparatedPhysicalCopies.purchased F fac anchor Q P J H v
  obtain ⟨n₀,A,_,ext⟩ := exterior_bounds F de R Rpos 1 one_pos
  let B (i:E) (r:ℝ) := A i*C.S.a (n r)^(-(de i:ℝ)-1)+1
  have charges (i:E) : RateLE trail LogV (B i) (((de i:ℝ)+1)*(4*b)) := by
    have bill := (RateLE.const (A i) ht).mul ((scaleN.mesh.rpow (-(de i:ℝ)-1)).pays ht)
    rw [show 0+(-(de i:ℝ)-1)*-(4*b)=((de i:ℝ)+1)*(4*b) by ring] at bill
    exact bill.add ((RateLE.const (1:ℝ) ht).mono (by positivity)) ht
  have lo := rate.mul (RateLE.prod (S:=Finset.univ) ht (fun i _=>charges i))
  have hi := (((RateIs.const ht εpos).mul ((PhysMS.coupling_rate hg hG).power k)).mul
    (PhysMS.length_rate.power D)).mul (PhysMS.length_rate.rpow extra)
  have budget := hi.outweigh lo (by simp only [mul_zero,zero_add,mul_neg,mul_one]; linarith only [reserve]) ht
  filter_upwards [paid,budget,scaleO.earlier (by linarith only [bp]) ht scaleU,
    scaleU.earlier (by linarith only [bp]) ht scaleN,scaleU.earlier inside ht P.coarse,
    scaleN.grows.eventually_ge_atTop n₀,clearance,core,separated,PhysMS.length_rate.pos,
    exists_cluster F fac anchor Q P J v] with r funds afford ou un ub old co cu cn positive select
  intro x plot
  refine ⟨select x plot,?_⟩
  intro z hz y free sep w bounded
  have out : Injective (beside (sole (0:E4)) y) := by
    refine beside_distinct.mpr ⟨injective_of_subsingleton _,(beside_distinct.mp sep).2.1,?_⟩
    intro _ i e
    have away := (Real.rpow_pos_of_pos positive b).trans_le (free.openSpace i)
    change (0:E4)=y i at e
    rw [e,sub_self,norm_zero] at away
    exact lt_irrefl _ away
  have fits := WilsonSeparatedSingleMeasure.atLevels (C:=C) f ou.le un.le co cu cn y free 1
  obtain ⟨t,places⟩ := fits.exists
  have payment : fee r*(∏ i,B i r) ≤ ε*g r^k*r^D*r^extra := (Real.le_norm_self _).trans afford
  have outer := ext (n r) old 1 one_pos
  constructor
  · obtain ⟨l,live,sub,found⟩ := hz
    letI := live
    have limit := WilsonSeparatedFusedReadout.original F fac.toServices Q J v r _ _ x y w sep out sub found
    apply (le_of_tendsto limit.norm ?_).trans payment
    filter_upwards [((funds x plot).and (places.and outer)).filter_mono sub] with j all
    obtain ⟨cell⟩ := all.2.1
    exact WilsonSeparatedSingleMeasure.one F y cell ub.le de w all.1 (fun i=>B i r)
      (all.2.2 (fun i=>S.representative _ (w i)) bounded)
  · intro screen s
    have hall : Hall C.S (o r) (u r) (P.b r) (u r) (n r) 1 (Fintype.card E) := by
      refine ⟨ou.le,le_rfl,ub.le,un.le,?_,?_⟩
      · simpa only [Nat.cast_one,one_mul] using (show 2*(5*C.S.a (u r)) < C.S.a (o r) by linarith only [cu])
      · convert cn using 1
        ring
    have prep : Prepared (C:=C) (names w) f (n r) (fun i=>B i r) :=
      ⟨fun i => outer.mono fun j hj=> hj (fun i=>S.representative _ (w i)) bounded i⟩
    have viewer : Probe.Viewer C f (names w) (P.b r) (r^b) (∏ i,B i r) :=
      ⟨o r,u r,u r,n r,_,hall,co,prep,rfl⟩
    exact (WilsonSeparatedPhysicalView.measured F fac Q J v r _ _
      (plot.first.trans ((Nat.le_succ _).trans plot.last)) x screen y w viewer free sep out
      (funds x plot) z hz s).trans payment

end YM.Integration.WilsonSeparatedMovingCells
