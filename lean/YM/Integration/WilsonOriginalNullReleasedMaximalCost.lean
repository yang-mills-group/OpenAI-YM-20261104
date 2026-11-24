import YM.Integration.WilsonOriginalNullReleasedOrientationPay
import YM.Integration.WilsonOriginalNullReleasedPeriod

noncomputable section
namespace YM.Integration.WilsonOriginalNullReleasedMaximalCost
open Function Filter Finset RG Lattice Wilson Source Labels Next.Rank Next.Rank.Price Next.Rank.Atlas
open Next.Rank.Station Further.CorrectedLift Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource
open Spec OPE OPE.Orbits RG17 PhysMS PhysMS.Frame Maxwell XSpace XSpace.Normalize WilsonPositionCapTransport
open WilsonMaxwellThermometerMaximalHead WilsonMaxwellThermometerStationHeads
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph ConnectedActivityE6
open WilsonPositionThermometerGradedReading WilsonMaxwellThermometerNominatedOrientation
open WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic
open private nonneg from YM.Integration.WilsonOriginalThermometerPalette
open private compare from YM.Integration.WilsonTrueProjectedNaturalFee
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
local notation "C₀"=>R.family
local notation "road"=>R.family.path.levels

def matrix (d q:ℕ):ℝ:=
  2*∑row:(R.family.labels.level d).Index,(1+2*(((R.family.labels.level d).grades row).2.succ:ℝ)*(q+4))

def graph (d q k:ℕ):ℝ:=
  ((2:ℝ)^(WilsonOriginalAdjacentMicroscopicPrice.height R d+1)*matrix R d q*2*mass R)*
    ((road).clock.hatBeta k)^(-(1/4):ℝ)

def torus (d k p:ℕ):ℝ:=
  ((2:ℝ)^WilsonOriginalAdjacentMicroscopicPrice.height R d*((road).clock.hatBeta k)^(1/4:ℝ)*mass R)*
    invoice (C:=C₀) d k p*stock C₀ k

theorem hot (q:ℕ) {β B:ℝ}(boost:4  ≤  B)(band:B/2  ≤  β):
    Coat.gStep β^(q+1)*B^(1/4:ℝ)  ≤  2*B^(-(1/4):ℝ):=by
  have posB:0<B:=by linarith
  have posβ:1 ≤ β:=by linarith
  have g0:0 ≤ Coat.gStep β:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have g1:Coat.gStep β ≤ 1:=by
    change (Real.sqrt β)⁻¹ ≤ 1
    simpa only [inv_one] using inv_anti₀ zero_lt_one (Real.one_le_sqrt.mpr posβ)
  have weak:=compare posB band
  calc
    _  ≤  Coat.gStep β*B^(1/4:ℝ):=by
      exact mul_le_mul_of_nonneg_right (by
        rw [pow_succ]
        simpa only [one_mul] using (mul_le_mul_of_nonneg_right (pow_le_one₀ (n:=q) g0 g1) g0)) (Real.rpow_nonneg posB.le _)
    _  ≤  2*(Real.sqrt B)⁻¹*B^(1/4:ℝ):=mul_le_mul_of_nonneg_right weak (Real.rpow_nonneg posB.le _)
    _ = _:=by rw [mul_assoc,Real.sqrt_eq_rpow,←Real.rpow_neg posB.le,←Real.rpow_add posB];congr 2;norm_num

theorem major {z a b x y W U v:ℝ} (z₁:z ≤ 1)(a₀:0 ≤ a)(b₀:0 ≤ b)(x₀:0 ≤ x)(y₀:0 ≤ y)
    (W₀:0 ≤ W)(U₀:0 ≤ U)(tiny:x*W ≤ v):
    z*(a*x+b*y)*W*U  ≤  a*v*U + (b*W*U)*y:=by
  calc
    _  ≤  1*(a*x+b*y)*W*U:=by gcongr
    _ = a*(x*W)*U + (b*W*U)*y:=by ring
    _  ≤  _ := by gcongr

theorem restore {z α f c x y n W U τ:ℝ} (z₁:z ≤ 1)(A:0 ≤ α)(B:0 ≤ f)(C:0 ≤ c)
    (X:0 ≤ x)(Y:0 ≤ y*n)(cash:0 ≤ W)(stocked:0 ≤ U)(tiny:x*W ≤ 2*τ):
    z*(f*x*α+c*y*n)*W*U ≤ α*f*2*U*τ+(c*W*U)*y*n:=by
  calc
    _ = z*((α*f)*x+c*(y*n))*W*U:=by ring
    _ ≤ (α*f)*(2*τ)*U+(c*W*U)*(y*n):=major z₁ (mul_nonneg A B) C X Y cash stocked tiny
    _ = _:=by ring

/-- All fixed-order costs of one released axis are explicit in the actual two physical clocks. -/
theorem original (simple:G.Simple)(shop:WilsonReportingAbsoluteInletSimultaneous.StationInvoice R)(q:ℕ):
    ∀ᶠ k:ℕ in atTop,∀A:Group C₀ 6,A.station.k=k→A.station.checked f H A.horizon→close R A→
    ∀N p:ℕ,∀live:k<N,∀W:Rep G ((C₀).side k p),W.p=(road).budget k→W.beta=((C₀).path.rep N p k).beta→
    ∀S:Finset (Fin 3),∀arm∈S,∀home:Opened C₀ (levels arm) k p,
      let d:=levels arm
      let F:=(C₀).labels.level d
      let raw:=((C₀).factory d N p).terminal.symm (A.station.wheel.atCut (N,p) (index A (grade arm)) (vector A S arm))
      let M:=fitting (C:=C₀) d N p k R.makes home live.le
      let declared:=F.scaled (Coat.gStep W.beta/W.p.threshold) (M raw)
      ∀c:F.Coeff,F.coeffSize (c-declared) ≤ matrix R d q*Coat.gStep W.beta^(q+1)*F.coeffSize declared→
      ∀r:ℝ,0<r→Station.gap (road) A.station.b k=r→∀j:F.Index,F.grades j=(d,d/2)→
      ‖(((r^d)⁻¹:ℝ):ℂ)*c j-(ladder C₀ (index A (grade arm)) (source C₀ S arm)) j‖ ≤ 
      graph R d q k+torus R d k p+deviation R A N p S arm:=by
  have mpos:0 ≤ mass R:=by
    unfold mass
    exact Finset.sum_nonneg (fun j _=>mul_nonneg (nonneg R j) (add_nonneg zero_le_one (norm_nonneg _)))
  filter_upwards [WilsonOriginalNullReleasedOrientationPay.original R (f:=f) (H:=H) simple shop (1/4) (by norm_num),
    clock R simple,(Station.hat_rate (road) simple).eventually_ge_atTop 4] with k paid monitor hotdate
  intro A date checked near N p live W tier beta S arm mem home d F raw M declared c bought r rp radial j degree
  have zoom:1  ≤  Station.mag road A.station.b k:=
    Real.one_le_rpow ((by norm_num:(1:ℝ) ≤ 2).trans monitor.2.1)
      (le_of_lt ((by norm_num:(0:ℝ)<5).trans checked.high.1))
  have ratio:(C₀).S.a k/r ≤ 1:=by
    apply (div_le_one rp).mpr
    rw [←radial]
    exact le_mul_of_one_le_right ((C₀).S.a_pos k).le zoom
  have a₀:0  ≤  matrix R d q:=by unfold matrix;positivity
  have g₀:0  ≤  Coat.gStep W.beta:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hβ:0<(road).clock.hatBeta k:=by linarith
  have density:0  ≤  invoice (C:=C₀) d k p*stock C₀ k:=
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (germ_close F (C₀).params).choose_spec.1.le)
      (Real.exp_pos _).le) (zero_le_one.trans ((road).params k).columns_ge)
  have band:(road).clock.hatBeta k/2 ≤ W.beta:=by
    rw [beta]
    exact (R.makes.wilson.represents N p k live.le).band.1
  have thermal:=hot q hotdate band
  have cash:=paid A date checked near N p live W tier beta S arm mem home c _ (mul_nonneg a₀ (pow_nonneg g₀ _))
    bought r rp radial j degree
  apply cash.trans
  refine add_le_add ?_ le_rfl
  exact restore (pow_le_one₀ (n:=d) (div_nonneg ((C₀).S.a_pos k).le rp.le) ratio)
    (pow_nonneg (by norm_num) _) a₀ (pow_nonneg (by norm_num) _) (pow_nonneg g₀ _) density
    (Real.rpow_nonneg hβ.le _) mpos thermal

end YM.Integration.WilsonOriginalNullReleasedMaximalCost
end
