import YangMills.WilsonProof.NativeSupport.JointPlantedAbsolute

/-! A numerical caller on the full physical finite torus, using only the
authenticated zero-coarse-field packet. The dated row and its displacement
band are explicit, so this caller can be checked on the original producer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsolutePlantedPort
open Function Filter Finset Lattice RG Wilson RGComparison.Core16 RGComparison.Core16.Spool
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics Next.Foundations Labels
open WilsonConditionalTaylorLabels WilsonOffsetJointRoster WilsonUniformUnmarkedInletEnergySites
open WilsonUniformUnmarkedInletBondRemainder WilsonUniformUnmarkedInletConnectedShift
open InletSusceptibility.Packet
open scoped Classical BigOperators Topology
variable {G:Gauge} {R:Run G} {C:Campaign R} {Θ:Luna.Tableau C.width 300} {v:ℕ→ℕ→ℝ}
local notation "A₀" => R.alloy.B.a

theorem original (sky:Campaign.Sky R C Θ v) (simple:G.Simple)
    (slow:∀ n,(((A₀).S.block n).val:ℝ)≤Real.log (2+Real.log ((A₀).clock.hatBeta n)))
    (support:∀ j,(((A₀).budget j).supportExponent+1)*(((A₀).S.block (j-1)).val:ℝ)^4≤Real.sqrt ((A₀).clock.hatBeta j))
    (a:Roster G) (s:Finset (Fin a.length)) (hs:s.Nonempty) (radius W:ℕ)
    (stencils:∀i:↥s,minSide G (grades a s i)≤radius):
    let S:ℕ:=(2*radius+1)^4
    let J:=radiusDegree W S (tariffDegree Θ.price)
    let H:=susceptibilityLoss s.card W S (tariffDegree Θ.price)
    let K:ℝ:=2*5^s.card*bill (grades a s) G*4^(2*J*(s.card+1))
    ∀ᶠ k:ℕ in atTop,∀u t,k≤t → ∀tn:t<u+1,
      ((u+1-t:ℕ):ℝ)*Real.log 3≤R.family.S.scale (u+1)-R.family.S.scale t →
      R.family.S.scale (u+1)-R.family.S.scale t≤(W:ℝ)*Real.log ((A₀).clock.hatBeta (u+1)) →
      ∀ per (T:Slices (A₀) per) (o:Fin a.length→Site (R.family.side (u+1) per)) i,i∈s →
      ∀ (z e:Site (R.family.side (u+1) per)) (part:Bool) (p:ℕ) (β δ:ℕ→ℝ) (η:ℝ),
        η≤1 → 2*(2*J+1)≤p →
        let d:=traversal T tn.le
        let B:=RGComparison.Core16.line R.family.path per t (u+1)
        let g:=regulatorRun R.family (u+1) per (u+1)
        let φ:=WilsonReportFrozenTraversal.planted R a s o i z e part
        β+δ=B → δ d.depth=0 → (∀l,l≤d.depth → |δ l|≤η*g^p) →
        (∀r∈Set.Icc (0:ℝ) 1,(∑j∈interior d,|picture d β δ 1 φ r j|)≤K/g^H) ∧
        ∃r∈Set.Ioo (0:ℝ) 1,d.conditioned B φ 1-d.conditioned β φ 1=
            ∑j∈interior d,δ (lag d j)*picture d β δ 1 φ r j ∧
          |d.conditioned B φ 1-d.conditioned β φ 1|≤η*g^p*(K/g^H):=by
  intro S J H K
  filter_upwards [planted_absolute sky simple slow support a s hs radius W stencils] with k paid
  intro u t kt tn floor roof per T o i hi z e part p β δ η small order d B g φ endB endδ band
  have gp:0≤g:=inv_nonneg.mpr (Real.sqrt_nonneg _)
  have cash:0≤η*g^p:=(abs_nonneg _).trans (band _ le_rfl)
  have line(l:ℕ):β l+δ l=B l:=congrFun endB l
  have all(r:ℝ)(hr:r∈Set.Icc (0:ℝ) 1):(∑j∈interior d,|picture d β δ 1 φ r j|)≤K/g^H:=by
    let Y:=temperatures β δ r
    have changeAt(l:ℕ):Y l-B l=(r-1)*δ l:=by rw [←line];change β l+r*δ l-(β l+δ l)=_;ring
    have terminal:Y d.depth=B d.depth:=sub_eq_zero.mp (by rw [changeAt,endδ,mul_zero])
    have charged(l:ℕ)(_lo:0<l)(lt:l<d.depth):|Y l-B l|≤g^p:=by
      rw [changeAt,abs_mul]
      have ur:|r-1|≤1:=abs_le.mpr ⟨by linarith only [hr.1],by linarith only [hr.2]⟩
      calc
        _≤1*|δ l|:=mul_le_mul_of_nonneg_right ur (abs_nonneg _)
        _≤1*(η*g^p):=mul_le_mul_of_nonneg_left (band l lt.le) zero_le_one
        _≤g^p:=by simpa only [one_mul] using mul_le_mul_of_nonneg_right small (pow_nonneg gp p)
    have bought:=paid u t kt tn floor roof per T o i hi z e part p β δ r order terminal charged
    simpa only [K,J,S,H,div_eq_mul_inv,mul_assoc] using bought
  let w (loc:↥s→Site (R.family.side (u+1) per)):=wordAt (grades a s) (labels a s) loc part
  have wc(loc):Continuous (w loc):=(component part).continuous.comp
    (continuous_finsetProd _ fun j _=>(localSection G (grades a s j)).continuous_places _ _)
  have wg(loc):GaugeInvariant (w loc):=by
    intro U X
    apply congrArg (component part)
    exact prod_congr rfl fun j _=>(localSection G (grades a s j)).placed_invariant (sound G _) _ _ U X
  have placed:φ=fun U=>w (fun j:↥s=>Function.update o i z j.val) U-w (fun j:↥s=>Function.update o i e j.val) U:=
    actual_planted R a s o i hi z e part
  have continuous:Continuous φ:=by rw [placed];exact (wc _).sub (wc _)
  have gauge:GaugeInvariant φ:=by rw [placed];intro U X;exact congrArg₂ (·-·) (wg _ U X) (wg _ U X)
  obtain ⟨r,hr,eq⟩:=shift d (traversal_ok T tn.le) β δ 1 continuous gauge
  rw [endB] at eq
  have total:=eq.trans (WilsonUniformUnmarkedInletBondCovariances.centered d (traversal_ok T tn.le) β δ endδ 1 continuous r)
  refine ⟨all,r,hr,total,?_⟩
  rw [total]
  refine (Finset.abs_sum_le_sum_abs ..).trans ?_
  calc
    _≤∑j∈interior d,η*g^p*|picture d β δ 1 φ r j|:=Finset.sum_le_sum fun j _=>by
      rw [abs_mul];exact mul_le_mul_of_nonneg_right (band (lag d j) (dates d j).1) (abs_nonneg _)
    _=η*g^p*(∑j∈interior d,|picture d β δ 1 φ r j|):=(Finset.mul_sum ..).symm
    _≤η*g^p*(K/g^H):=mul_le_mul_of_nonneg_left (all r ⟨hr.1.le,hr.2.le⟩) cash
end YM.Integration.WilsonReportingAbsolutePlantedPort
