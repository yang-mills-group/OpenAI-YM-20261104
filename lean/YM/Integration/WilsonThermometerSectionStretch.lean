import YM.Integration.WilsonOriginalThermometerReportedGrading
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSectionStretch
open Filter Finset Lattice Wilson RG Source Labels Marker QuadraticLocal Earn Sunrise QuadraticLocal.Affinity
open FVA1 WilsonLimitConstruction PhysicalNext.Repeat Cells MeasureTheory Extraction Table Climb Trace Trace.Pilot
open Next.UVStress Next.Rank Next.Rank.East MergeProof.East Next.Rank.Price PhysicalNext.Repeat.Legato
open WilsonOriginalStarSceneWords WilsonOriginalStarSceneRows WilsonOriginalStarSceneRent
open WilsonPositionThermometerCapStation WilsonPositionThermometerGradedSource WilsonPositionThermometerGradedReading
open WilsonOriginalThermometerPalette WilsonOriginalThermometerMicroscopic WilsonOriginalThermometerTopDensity
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {f:Extraction.Order} {H:(Bel R.family.book).Hierarchy}
local notation "C" => R.family
local notation "S" => R.family.S
local notation "B" n:max => R.family.path.levels.clock.hatBeta n
local notation "J" => Stock.census (Fin 3)

/-- The actual inverse calibrated sections cost only the physical mesh ratio over any
finite interval. The incoming coordinate is the one fixed at the genuine bare cutoff. -/
theorem sectionAt (d k N p:ℕ) (ref:(C).ref d≤k) (v:(C).label d) {j:ℕ} (date:k≤j) :
    j≤N → ((C).labels.level d).coeffSize (awake C d j N p v) ≤
      ((S).a k/(S).a j)^(d+1)*((C).labels.level d).coeffSize (awake C d k N p v):=by
  induction j, date using Nat.le_induction with
  | base =>
    intro hn
    simp [(S).a_pos k|>.ne']
  | succ j kj ih=>
    intro cut
    let x:=((S).block j).val
    let F:=(C).labels.level d
    have non:0≤F.coeffSize (awake C d j N p v):=sum_nonneg fun _ _=>norm_nonneg _
    have xp:(0:ℝ)<x:=by exact_mod_cast Nat.zero_lt_of_lt ((S).block j).property
    have columns:((C).path.levels.params (j+1)).columns≤(x:ℝ):=RG12.Commission.column_priced (C).path.levels j
    have priced:=WilsonOriginalAdjacentMicroscopicPrice.backward R d j N p (by omega) (ref.trans kj) v
    have r:((S).a k/(S).a (j+1))=x*((S).a k/(S).a j):=by
      rw [(S).a_step]
      field_simp [((S).a_pos j).ne',xp.ne']; rfl
    rw [r,mul_pow]
    calc
      _ ≤ ((x:ℝ)^d*((C).path.levels.params (j+1)).columns)*F.coeffSize (awake C d j N p v):=priced
      _ ≤ ((x:ℝ)^d*x)*F.coeffSize (awake C d j N p v):=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left columns (pow_nonneg xp.le _)) non
      _ = (x:ℝ)^(d+1)*F.coeffSize (awake C d j N p v):=by rw [pow_succ]
      _ ≤ (x:ℝ)^(d+1)*(((S).a k/(S).a j)^(d+1)*F.coeffSize (awake C d k N p v)):=
        mul_le_mul_of_nonneg_left (ih (by omega)) (pow_nonneg xp.le _)
      _ = _:=by ring

def cap (k:ℕ)(ε aperture:ℝ):=aperture^7*((B k)^ε*mass R)

theorem coordinates (simple:G.Simple) (ε:ℝ)(positive:0<ε):
    ∀ᶠ k:ℕ in atTop,∀ A:Group C 6,A.station.k=k → A.station.checked f H A.horizon → close R A →
    ∀ aperture:ℝ,1≤aperture → ∀N p:ℕ,k<N → (S).a k/(S).a N≤aperture → ∀j:Fin 3,
      ((C).labels.level (levels j)).coeffSize (WilsonOriginalThermometerPalette.coordinates R A N N p j) ≤
        cap R k ε aperture:=by
  filter_upwards [station R (f:=f) (H:=H) simple ε positive,
    eventually_all.mpr (fun j:Fin 3=>eventually_ge_atTop ((C).ref (levels j)))] with k booked refs A atK funded near aperture one N p kN width j
  let d:=levels j
  let F:=(C).labels.level d
  let v:=A.station.wheel.atCut (N,p) (index A (grade j)) (vector A univ j)
  let h:=F.coeffSize (awake C d k N p v)
  have pay:h≤(B k)^ε*mass R:=(booked A atK funded N p kN j).trans
    (mul_le_mul_of_nonneg_left (WilsonOriginalThermometerReportedGrading.station_mass R A near)
      (Real.rpow_nonneg (zero_le_one.trans ((C).path.levels.fits.delayed k).le) _))
  have gate:((S).a k/(S).a N)^(d+1)≤aperture^7:=
    (pow_le_pow_left₀ (div_nonneg ((S).a_pos _).le ((S).a_pos _).le) width _).trans
      (pow_le_pow_right₀ one (Nat.succ_le_succ (WilsonOriginalThermometerGradedPalette.ceiling j)))
  exact (sectionAt R d k N p (refs j) v kN.le le_rfl).trans
    (mul_le_mul gate pay (sum_nonneg (fun _ _=>norm_nonneg _)) (pow_nonneg (zero_le_one.trans one) _))

end YM.Integration.WilsonThermometerSectionStretch
