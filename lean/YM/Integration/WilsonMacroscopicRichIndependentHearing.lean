import YM.Integration.WilsonMacroscopicRichCapturedProbes
import YM.Integration.WilsonMacroscopicRichProjectedCoordinates

/-! A fixed finite family of observations of the full earlier density compares a prescribed output
with the continuum coefficient on the original run. Both norms retain the actual discrepancy. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichIndependentHearing
open Set Function Filter Spec OPE OPE.Orbits PhysMS Pert.Asymptotics Lattice Cells Wilson
open Trace.Pilot RG16 RG16.Literal RG MergeProof Trace.Physical.GermGraph FilteredWilsonProduct
open Source Labels Analysis Next.Foundations Push.Local Bid Next.UVStress
open PhysicalNext.Repeat.Legato RGComparison.Core16 FilteredIntrinsicGramReadout
open ProjectorNext.Equivariance Trace.Physical
open WilsonMacroscopicRichMeasuredFiling WilsonMacroscopicRichCapturePropagation
open WilsonMacroscopicRichCapturedProbes
open scoped Topology BigOperators Classical ContDiff
variable {G:Gauge}(R:Run G){S:Table R.family.book}{f:Extraction.Order}
variable {I:Type}[Fintype I][Nonempty I]{d:I→ℕ}

def debit {h N p u b:ℕ}(P:Finset (Probe G h))(door:Opened R.family h u p)
    (ub:u≤b)(uN:u≤N)(z:R.family.label h)(Z:Config G (R.family.side b p)→ℂ):ℝ:=
  ∑ t∈P,‖runProbe (R.family.labels.level h) t (forecast R door uN z)-
    Germ.jet R.family.params t (R.family.path.rep N p u).p.threshold 0 (returned R (N:=N) ub h Z)‖

theorem measured (F:Final R.family f S)(reader:Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (J:ℝ→tower S)(leading:Leading F J)(foundation:Foundation F reader)(fac:Facilities R.family f S)
    (pace:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda R.family.path.levels m))
    (h:ℕ)(η M B:ℝ)(hη:0<η)(hM:0<M)(hB:20<B):
    ∃a:ℕ,∃W:Fin a→Watch R.family,∃D:(Fin a→ℂ)→L[ℂ] S.Field h,∃top u:ℕ,∃T:Stop R.family h top u,
    ∃P:Finset (Probe G h),∃K:ℝ,0≤K ∧ (∀y,D (fun i=>(W i).tester S h y)=y) ∧
    ∀(v:(j:I)→(Climb.Bel R.family.book).Field (d j)),(∀i,‖v i‖≤1)→
    ∀(g:ℝ→ℝ),Coupling G g→G.Simple→∀(q:ℕ)(δ ε:ℝ),0<δ→δ<1/16→0<ε→
    ∀ᶠ m : ℕ in Filter.atTop, ∃ (_um : u ≤ m), ∀(ρ:ℝ)(x : I → Lattice.Cover),Tuple R.family M η B m ρ x→
    ∀ᶠ w : ℕ × ℕ in f.fuse, ∃ (_hn : m < w.1), 
    ∀(b:ℕ)(ub:u≤b)(bN:b≤w.1)(_:Slices R.family.path.levels w.2)
      (Z:Config G (R.family.side b w.2)→ℂ),
      let r:=R.family.S.a m*ρ
      let Y:=field F reader J v r m x w
      let A:=reader.packet h (fun i=>R.family.S.gridPoint m (x i)) (Frame.born J r v) 0
      credit R.family w.1 w.2 h Y b bN=Z →
      ∀y:(Climb.Bel R.family.book).Field h,
        let z:=S.representative h (J r h y)
        let c:=debit R P (T.doors w.2) ub (ub.trans bN) z Z
        ‖J r h y-A‖≤K*c+ε*g r^q*r^((h:ℝ)+δ) ∧
        ‖y-(J r h).symm A‖≤‖(J r h).symm.toLinearMap.toContinuousLinearMap‖*(K*c)+ε*g r^q*r^δ:=by
  obtain ⟨a,W,D,top,u,T,fits,issued⟩:=WilsonMacroscopicRichProjectedCoordinates.original
    (d:=d) F reader J leading foundation fac pace h η M B hη hM hB
  obtain ⟨P,probes⟩:=WilsonMacroscopicRichCapturedProbes.measured R S h
  obtain ⟨K,kn,measure⟩:=probes u T.doors
  refine ⟨a,W,D,top,u,T,P,K,kn,fits,?_⟩
  intro v cap g coupling simple q δ ε hd hr he
  filter_upwards [issued v cap g coupling simple q δ ε hd hr he] with m ready
  obtain ⟨um,cells⟩:=ready
  refine ⟨um,?_⟩
  intro ρ x geom
  filter_upwards [cells ρ x geom] with w results
  obtain ⟨hn,book,phys,coords⟩:=results
  refine ⟨hn,?_⟩
  intro b ub bN course Z
  let r:=R.family.S.a m*ρ
  let Y:=field F reader J v r m x w
  dsimp only []
  intro account y
  let z:=S.representative h (J r h y)
  let V:=S.project h (label (w:=w) F.room.cutoff (T.doors w.2) (um.trans hn.le) Y)
  let A:=reader.packet h (fun i=>R.family.S.gridPoint m (x i)) (Frame.born J r v) 0
  let E:=(J r h).symm.toLinearMap.toContinuousLinearMap
  let c:=debit R P (T.doors w.2) ub (ub.trans bN) z Z
  let ν (t:Probe G h):=‖runProbe (R.family.labels.level h) t (forecast R (T.doors w.2) (ub.trans bN) z)-
    Germ.jet R.family.params t (R.family.path.rep w.1 w.2 u).p.threshold 0 (returned R (N:=w.1) ub h Z)‖
  have sum_eq:c=∑ t∈P,ν t:=rfl
  have nn (t:Probe G h):0≤ν t:=norm_nonneg _
  let obs (i:I)(k:Fin (d i+1)):=R.family.O w.1 w.2
    (S.representative _ (reader.cutTest k.val (d i) (J r (d i) (v i))))
    (location R.family.S m w.1 w.2 (x i))
  have values (U:Config G (R.family.side w.1 w.2)):Y U=∏i,∑k, obs i k U:=by
    simp only [Y,FilteredWilsonProduct.field,obs,Finset.prod_apply,Finset.sum_apply]
  have ct:Continuous Y:=by
    rw [show Y=(fun U=>∏i,∑k,obs i k U) from funext values]
    exact continuous_finsetProd _ fun _ _=>continuous_finsetSum _ fun _ _=>R.family.continuousO ..
  have gi:GaugeInvariant Y:=by
    intro gauge U
    rw [values,values]
    exact Finset.prod_congr rfl fun i _=>Finset.sum_congr rfl fun k _=>R.family.invariant F.room.cutoff _ _ _ _ _ gauge U
  have cc:0≤c:=sum_eq.symm ▸ Finset.sum_nonneg (fun t _=>nn t)
  have small (t:Probe G h)(ht:t∈P):ν t≤c:=by rw [sum_eq];exact Finset.single_le_sum (fun k _=>nn k) ht
  have bound:‖S.project h z-V‖≤K*c:=measure w.1 w.2 b course ub bN (um.trans_lt hn) Y Z ct gi book account z c cc small
  have present:S.project h z=J r h y:=S.rep ..
  rw [present] at bound
  have fixed:‖J r h y-A‖≤K*c+ε*g r^q*r^((h:ℝ)+δ):=
    (norm_sub_le_norm_sub_add_norm_sub _ V _).trans (add_le_add bound phys)
  have back:‖y-(J r h).symm V‖≤‖E‖*(K*c):=by
    calc
      _=‖E (J r h y-V)‖:=by rw [map_sub];change ‖y-(J r h).symm V‖=‖(J r h).symm (J r h y)-(J r h).symm V‖;rw [LinearEquiv.symm_apply_apply]
      _≤‖E‖*‖J r h y-V‖:=E.le_opNorm _
      _≤_:=mul_le_mul_of_nonneg_left bound (ContinuousLinearMap.opNorm_nonneg E)
  exact ⟨fixed,(norm_sub_le_norm_sub_add_norm_sub _ ((J r h).symm V) _).trans (add_le_add back coords)⟩

end YM.Integration.WilsonMacroscopicRichIndependentHearing
