import YM.Integration.WilsonOriginalNullReleasedOrientation

noncomputable section
namespace YM.Integration.WilsonOriginalNullReleasedOrientationPay
open Function Filter RG Lattice Wilson Source Labels Next.Rank Next.Rank.Price Next.Rank.Atlas
open Next.Rank.Station Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open Spec OPE OPE.Orbits RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize WilsonPositionCapTransport
open WilsonMaxwellThermometerMaximalHead WilsonMaxwellThermometerStationHeads
open scoped BigOperators Classical Topology
open Filter Finset Lattice Wilson RG Labels Source Trace.Physical Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato RGComparison.Core16.Astage RG05Preconstruction
open Next.Rank.Price RG12 RG17 MergeProof.East ConnectedActivityE6
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open WilsonMaxwellThermometerNominatedOrientation WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic
open private salary_cap from YM.Integration.WilsonOriginalThermometerTopGrading
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
local notation "C₀"=>R.family
local notation "road"=>R.family.path.levels

/-- An occupied literal input returns to its signed public axis at the true station.
Both matrix and winding prices are restored in its public field units before either limit. -/
theorem original (simple:G.Simple)(shop:WilsonReportingAbsoluteInletSimultaneous.StationInvoice R)(ε:ℝ)(ep:0<ε):
    ∀ᶠ k:ℕ in atTop,∀A:Group C₀ 6,A.station.k=k→A.station.checked f H A.horizon→close R A→
    ∀N p:ℕ,∀live:k<N,∀W:Rep G ((C₀).side k p),W.p=(road).budget k→W.beta=((C₀).path.rep N p k).beta→
    ∀S:Finset (Fin 3),∀arm∈S,∀home:Opened C₀ (levels arm) k p,
      let d:=levels arm
      let F:=(C₀).labels.level d
      let raw:=((C₀).factory d N p).terminal.symm (A.station.wheel.atCut (N,p) (index A (grade arm)) (vector A S arm))
      let M:=fitting (C:=C₀) d N p k R.makes home live.le
      let declared:=F.scaled (Coat.gStep W.beta/W.p.threshold) (M raw)
      let h:=WilsonOriginalAdjacentMicroscopicPrice.height R d
      ∀c:F.Coeff,∀L:ℝ,0≤L→F.coeffSize (c-declared)≤L*F.coeffSize declared→
      ∀r:ℝ,0<r→Station.gap (road) A.station.b k=r→∀j:F.Index,F.grades j=(d,d/2)→
      ‖(((r^d)⁻¹:ℝ):ℂ)*c j-(ladder C₀ (index A (grade arm)) (source C₀ S arm)) j‖≤
        ((C₀).S.a k/r)^d*(L*(2:ℝ)^(h+1)+(2:ℝ)^h*invoice (C:=C₀) d k p*stock C₀ k)*
          (road).clock.hatBeta k^ε*mass R+deviation R A N p S arm:=by
  filter_upwards [WilsonOriginalNullReleasedNominated.original R (f:=f) (H:=H) simple shop ε ep,
    WilsonOriginalThermometerPalette.station R (f:=f) (H:=H) simple ε ep] with k fit array
  intro A date checked near N p live W tier beta S arm hit home d F raw M declared h c L L₀ paid r r₀ radial j degree
  subst k
  let k:=A.station.k
  let v:=A.station.wheel.atCut (N,p) (index A (grade arm)) (vector A S arm)
  let ω:=awake C₀ d k N p v
  let cash:=(road).clock.hatBeta k^ε*mass R
  have same:vector A S arm=vector A univ arm:=by simp [vector,source,hit]
  have earned:=fit A rfl checked near k N p live le_rfl live.le W tier beta arm home
  have fitcost:F.coeffSize declared≤(2:ℝ)^(h+1)*((C₀).S.a k)^d*cash:=by
    have ne:=((C₀).S.a_pos k).ne'
    dsimp only [declared,M,raw]
    rw [same]
    dsimp only [k] at earned ne
    simpa only [div_self ne,Real.one_rpow,mul_one,mul_assoc] using earned
  have wage:F.coeffSize ω≤cash:=by
    have work:=(array A rfl checked N p live arm).trans (mul_le_mul_of_nonneg_left (salary_cap R A near)
      (Real.rpow_nonneg (zero_le_one.trans ((road).fits.delayed k).le) _))
    unfold coordinates at work
    rw [← same] at work
    exact work
  have inv₀:0 ≤ invoice (C:=C₀) d k p:=mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (Germ.germ_close F (C₀).params).choose_spec.1.le) (Real.exp_pos _).le
  have st₀:0 ≤ stock C₀ k:=zero_le_one.trans ((road).params k).columns_ge
  have ax:=WilsonOriginalNullReleasedOrientation.landed R A S arm live.le home W tier beta c r
    (L*F.coeffSize declared) radial paid j degree
  change ‖(((r^d)⁻¹:ℝ):ℂ)*c j-_‖≤(r^d)⁻¹*(L*F.coeffSize declared+
    (2:ℝ)^h*invoice (C:=C₀) d k p*stock C₀ k*((C₀).S.a k)^d*F.coeffSize ω)+_ at ax
  apply ax.trans
  refine add_le_add ?_ le_rfl
  calc
    _ ≤ (r^d)⁻¹*(L*((2:ℝ)^(h+1)*((C₀).S.a k)^d*cash)+
          (2:ℝ)^h*invoice (C:=C₀) d k p*stock C₀ k*((C₀).S.a k)^d*cash):=by
      exact mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left fitcost L₀)
        (mul_le_mul_of_nonneg_left wage (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) inv₀)
          st₀) (pow_nonneg ((C₀).S.a_pos k).le d)))) (inv_nonneg.mpr (pow_nonneg r₀.le _))
    _ = _:=by dsimp only [cash];rw [div_pow];ring

end YM.Integration.WilsonOriginalNullReleasedOrientationPay
end
