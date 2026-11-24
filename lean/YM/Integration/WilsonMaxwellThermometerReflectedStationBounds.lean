import YM.Integration.WilsonMaxwellThermometerReflectedUnit
import YM.Integration.WilsonPositionProgramNormalizedAmplitude
/-! A common finite salary on the two true inverse-calibrated reflected
currents and each original proper face. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerReflectedStationBounds
open Filter Function Set Finset MeasureTheory Lattice Wilson RG RG.Supply Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp
open WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Layout WilsonCoeffUV.Embroider WilsonCoeffUV.Shard WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS
open Source Source.Drops Labels XSpace XSpace.Normalize Maxwell Table Climb Trace Trace.Pilot
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonMaxwellThermometerReflectedPhysicalColumns (levels active)
open WilsonMaxwellThermometerReflectedStation (Name source phase)
open WilsonPositionThermometerCapStation (Group)
open WilsonPositionProgramOriginalStationRadius (zoomFactor covers)
open WilsonPositionProgramNormalizedMaster (fee)
open scoped Topology BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}{D k u e:ℕ}
variable (d:Fin 2→ℕ)(fit:∀i,levels i<d i)
local notation "Q" => deck (G:=G) levels d fit

def covered (big:0<D)(φ:Wilt Q)(A:Group R.family 6)(checked:A.station.checked f H A.horizon)
    (a:Axis)(b:Sec G 6)(m N p k:ℕ)(s:Name)(t:ℕ)(i:Alma ((primes G).F 0)):ℝ:=
  PowerSeries.coeff t (lodgeIn R.family.path.levels R.metals.O ((primes G).T 0) big
    (sceneGrow (covers R A checked) φ) (normalized R.family.path.levels R.metals.O Q
      (source R d fit A a b m s N p) m) m m m k i)

def originalTorus (φ:Wilt Q)(A:Group R.family 6)(checked:A.station.checked f H A.horizon)
    (a:Axis)(b:Sec G 6)(m N p D:ℕ)(s:Name)(t:ℕ)(i:Alma ((primes G).F 0)):ℝ:=
  WilsonPositionProgramNominatedPublicScalar.finite R levels d fit m N p t D
    (sceneGrow (covers R A checked) φ) (source R d fit A a b m s N p) i

theorem original (simple:G.Simple)(paid:WilsonPositionProgramNominatedMenuInvoice.issued G R.kit)
    (big:0<D)(rails:Rails 0 k u e)(cap:capP Q ≤ k)(φ:Wilt Q)
    (sep:∀i j,i≠j → Disjoint (tsupport (φ i).ψ.val) (tsupport (φ j).ψ.val)):
    ∀ᶠ m:ℕ in atTop,1≤zz R.family.path.levels m → ∀A:Group R.family 6,A.station.k=m → ∀checked:A.station.checked f H A.horizon,
      ∀(a:Axis)(b:Sec G 6),∃C:ℝ,0 ≤ C ∧ ∀N p:ℕ,m<N → ∀s:Name,∀t ≤ e,∀i,
        ‖covered R d fit big φ A checked a b m N p k s t i‖ ≤ C:=by
  let L:=R.family.path.levels
  obtain ⟨Z,w,_,profile⟩:=WilsonPositionProgramOriginalStationRadius.original (f:=f) (H:=H) (c:=6) R simple φ sep 1
  obtain ⟨E,B,posE,posB,K,M,mass⟩:=WilsonPositionProgramNormalizedAmplitude.original R simple
    (WilsonPositionProgramNominatedMenuInvoice.wallet G) paid.2 big rails levels d fit cap
  filter_upwards [profile,mass,
    WilsonMaxwellThermometerReflectedPhysicalColumns.original (f:=f) (H:=H) R simple 1 zero_lt_one e d fit] with m shape ready costs
  intro strip A date checked a b
  let ρ:=zoomFactor R A
  let z:=max (Compar L.S (zz L) m m) (Z*ρ)
  let expenses (s:Name)(i:Fin 2):ℝ:=
    let F:=R.family.labels.level (levels i)
    (Fintype.card (Alma F)*(e+1:ℕ):ℕ)*(‖phase s i‖ *
      ((2:ℝ)^(univ.sup fun v:F.Index=>(F.grades v).2)*L.clock.hatBeta m^((1:ℝ))*
        (WilsonPositionThermometerStationNorm.cost R.family (levels i)*‖active R A a b s.1 s.2.2 i‖)))
  obtain ⟨eligible,_,budget,_⟩:=shape A date checked
  let purse(s:Name):=E*z^K*∏i:Fin 2,ρ⁻¹^4*w i*(B*(zz L m)^M*expenses s i)
  refine ⟨∑s:Name,‖purse s‖,sum_nonneg fun _ _=>norm_nonneg _,?_⟩
  intro N p top s t grade i
  let X:=source R d fit A a b m s N p
  have angle:Bough Q (sceneGrow (covers R A checked) φ) (paceT L.S m m) z
      (fun i=>ρ⁻¹^4*w i):=by simpa only [pace_self] using budget
  have wage:∀i:Fin 2,fee X e i ≤ expenses s i:=fun i=>
    costs A date checked N p top a b s.1 s.2.2 (phase s) i
  have zpos:0 ≤ z:=zero_le_one.trans angle.pos
  have zzpos:0≤zz L m:=zero_le_one.trans strip
  have price:= (ready X m m le_rfl le_rfl _ _ z (le_max_left ..) angle t grade i m le_rfl).2
  apply price.trans
  have bump (i:Fin 2):0 ≤ fee X e i:=by unfold fee;positivity
  have bounds:E*z^K*(∏i:Fin 2,ρ⁻¹^4*w i*(B*(zz L m)^M*fee X e i)) ≤ purse s:=by
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg posE.le (pow_nonneg zpos _))
    apply Finset.prod_le_prod
    · intro i _
      exact mul_nonneg (angle.lanes i).1 (mul_nonneg (mul_nonneg posB.le (pow_nonneg zzpos _)) (bump i))
    · intro i _
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (wage i)
        (mul_nonneg posB.le (pow_nonneg zzpos _))) (angle.lanes i).1
  exact bounds.trans ((le_abs_self (purse s)).trans (single_le_sum
    (f:=fun s:Name=>‖purse s‖) (fun j _=>norm_nonneg _) (mem_univ s)))
end YM.Integration.WilsonMaxwellThermometerReflectedStationBounds
