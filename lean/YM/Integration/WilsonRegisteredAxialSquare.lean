import YM.Integration.WilsonRegisteredAxialRoom
import YM.Integration.WilsonRegisteredAxialMass

/-! Full genuine positive-Gibbs second moment of the marked high-mode
regular residual, including the rejected physical collar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAxialSquare
open MeasureTheory Filter Set Finset Lattice RG Wilson OPE.Therm RG16 PhysicalNext.Repeat.Legato MSbar.Heath
open WilsonRegisteredAffineHalo WilsonRegisteredAxialRates WilsonReportingForestAngularFare
open WilsonInheritedRegisteredField WilsonRegisteredFrozenReading WilsonReportingForestAngularReflection
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

private theorem split {Ω:Type*} [MeasurableSpace Ω] (μ:Measure Ω) [IsProbabilityMeasure μ]
    (f:Ω→ℝ) (z:∀U,0 ≤ f U) (E:Set Ω) (me:MeasurableSet E) {M B η:ℝ}
    (small:∀U∈E,f U ≤ η*M) (gross:∀U,(f U)^2 ≤ B*M^2) (mass:B*μ.real Eᶜ ≤ η^2):
    (∫ U,(f U)^2 ∂μ) ≤ 2*η^2*M^2:=by
  let a:=(η*M)^2
  let b:=B*M^2
  have i:Integrable (fun U=>a+Eᶜ.indicator (fun _=>b) U) μ:=
    (integrable_const a).add ((integrable_const b).indicator me.compl)
  have h (U):f U^2 ≤ a+Eᶜ.indicator (fun _=>b) U:=by
    by_cases paid:U∈E
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr paid),add_zero]
      exact pow_le_pow_left₀ (z U) (small U paid) 2
    rw [Set.indicator_of_mem (show U∈Eᶜ from paid)]
    exact (gross U).trans (le_add_of_nonneg_left (sq_nonneg _))
  calc
    _ ≤ (∫ U,a+Eᶜ.indicator (fun _=>b) U ∂μ):=
      integral_mono_of_nonneg (ae_of_all _ fun U=>sq_nonneg (f U)) i (ae_of_all _ h)
    _=a+μ.real Eᶜ*b:=by rw [integral_add (integrable_const _) ((integrable_const _).indicator me.compl),integral_const,
          integral_indicator_const _ me.compl];simp [smul_eq_mul]
    _ ≤ a+η^2*M^2:=by dsimp only [b];rw [←mul_assoc,mul_comm (μ.real Eᶜ)];gcongr
    _=2*η^2*M^2:=by dsimp only [a];ring

theorem physical (simple:G.Simple) (gate:posted R)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (a:Lattice.Order) (p base t:ℕ) {ε:ℝ} (he:0<ε):
    ∀ᶠ m:ℕ in atTop,∀ N per (live:m+1 ≤ N) d (_ref:R.family.ref d ≤ m+1)
      (v:R.family.label d) (o:Site (R.family.side (m+1) per)),
      let k:=m+1
      let μ:=scene R.family.path N per k
      let b:=WilsonDegreeFourInheritedRange.height R p k
      let Z:=packet R.makes live v o
      let L:=R.family.labels.level d
      (∫U,(‖previous R live v o b U‖*(Real.log (β k))^t)^2 ∂μ)
        ≤ (ε*L.coeffSize (L.core Z.x))^2:=by
  let η:=ε/2
  have ep:0<η:=half_pos he
  filter_upwards [WilsonRegisteredAxialRoom.purchased R simple slow J clear a p base t ep,
    WilsonRegisteredAffineHalo.purchased R simple gate p (base+1) 1 0 (sq_pos_of_pos ep),
    WilsonRegisteredAxialMass.capacity R simple slow t] with m good miss cap
  intro N per live d ref v o k μ b Z L
  let H:=radius R p (base+1) k
  let E:=House.chilly (G:=G) (WilsonPhysicalHistoryKioskPlaquettes.faces H o) (angularCut (β k))
  let s:=Real.log (β k)
  let M:=L.coeffSize (L.core Z.x)
  let f U:=‖previous R live v o b U‖*s^t
  letI:IsProbabilityMeasure (scene R.family.path N per k):=probability R.makes.wilson live
  have bp:0 ≤ β k:=zero_le_one.trans ((A).fits.delayed k).le
  have sp:0 ≤ s:=Real.log_nonneg ((A).fits.delayed k).le
  have mp:0 ≤ M:=Finset.sum_nonneg fun _ _=>norm_nonneg _
  have z (U):0 ≤ f U:=mul_nonneg (norm_nonneg _) (pow_nonneg sp t)
  have bill:β k*μ.real Eᶜ ≤ η^2:=by
    simpa only [pow_one,pow_zero,mul_one,Set.iUnion_const] using miss N per live (fun _:Fin 2=>o)
  have size (U):(f U)^2 ≤ (β k)*M^2:=by
    have observed:‖previous R live v o b U‖ ≤ ((A).params k).columns*M:=(WilsonRegisteredAxialMass.gross R live ref v o b).2 U
    calc
      _ ≤ ((((A).params k).columns*s^t)*M)^2:=by
        apply pow_le_pow_left₀ (z U)
        exact (mul_le_mul_of_nonneg_right observed (pow_nonneg sp t)).trans_eq (by ring)
      _ ≤ _:=by rw [mul_pow];exact mul_le_mul_of_nonneg_right cap (sq_nonneg M)
  refine (split μ f z E (House.bath _) (good N per live d ref v o) size bill).trans ?_
  dsimp only [η];nlinarith only [sq_nonneg (ε*M)]

end YM.Integration.WilsonRegisteredAxialSquare
end
