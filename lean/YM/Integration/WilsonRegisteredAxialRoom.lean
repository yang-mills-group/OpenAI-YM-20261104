import YM.Integration.WilsonRegisteredAxialChart
import YM.Integration.OriginalPeriodWindingPrice

/-! The true torus contains the projected box at every period after
one level, and the existing local thermal event pays its plaquettes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAxialRoom
open Filter Set Finset Lattice RG Wilson OPE.Therm RG16 PhysicalNext.Repeat.Legato MSbar.Heath
open WilsonRegisteredAffineHalo WilsonRegisteredAxialRates WilsonReportingForestAngularFare
open WilsonInheritedRegisteredField Push.AbsoluteSums.Animals
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

theorem torus (simple:G.Simple) (p base:ℕ):
    ∀ᶠ k:ℕ in atTop,∀ per,10*radius R p base k<(R.family.side k per).val:=by
  let D:=factor p base
  have dp:0<D:=by dsimp [D,factor];positivity
  let C:=11*D
  have cp:0<C:=by dsimp only [C];positivity
  have grow:=Next.Rank.Station.hat_rate (A) simple
  have sub:=(Real.isLittleO_pow_log_id_atTop (n:=3)).bound (inv_pos.mpr cp)
  filter_upwards [grow.eventually sub,(Real.tendsto_log_atTop.comp grow).eventually_ge_atTop 1,
    OriginalPeriodWindingPrice.period_power (A) 1] with k small late period
  intro per
  let s:=Real.log (β k)
  have sp:1 ≤ s:=late
  have s0:0<s:=zero_lt_one.trans_le sp
  have bp:0<β k:=zero_lt_one.trans ((A).fits.delayed k)
  have hi:(radius R p base k:ℝ) ≤ D*s^3:=geometry R p base k sp
  have coupon:s^3 ≤ C⁻¹*(β k):=by
    change ‖s^3‖ ≤ C⁻¹*‖β k‖ at small
    simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg s0.le 3),abs_of_pos bp] using small
  have limit:C*s^3 ≤ β k:=(mul_le_mul_of_nonneg_left coupon cp.le).trans_eq (by field_simp)
  have pay:10*(radius R p base k:ℝ)<((R.family.side k per).val:ℝ):=calc
    _ ≤ 10*(D*s^3):=by gcongr
    _ < C*s^3:=by dsimp only [C];nlinarith only [mul_pos dp (pow_pos s0 3)]
    _ ≤ β k:=limit
    _ ≤ _:=by simpa only [pow_one] using period per
  exact_mod_cast pay

theorem cells {n:Side} (H:ℕ) (o:Site n):
    WilsonAxialWindow.cells o H ⊆ WilsonPhysicalHistoryKioskPlaquettes.faces H o:=by
  intro z hz
  have old:z.1∈(box H).image (fun w=>wrap n w+o):=(Finset.mem_product.mp hz).1
  obtain ⟨w,hw,eq⟩:=Finset.mem_image.mp old
  apply Finset.mem_product.mpr
  refine ⟨(neighbors_mem _ _ _).2 ?_,Finset.mem_univ _⟩
  rw [←eq]
  exact (Work.E08.separation_box_add o hw).trans (by omega)

theorem purchased (simple:G.Simple)
    (slow:∀m,((R.family.S.block m).val:ℝ) ≤ Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (a:Lattice.Order) (p base t:ℕ) {ε:ℝ} (he:0<ε):
    ∀ᶠ m:ℕ in atTop,∀ N per (live:m+1 ≤ N) d (_ref:R.family.ref d ≤ m+1)
      (v:R.family.label d) (o:Site (R.family.side (m+1) per)),
      let k:=m+1
      let b:=WilsonDegreeFourInheritedRange.height R p k
      let H:=radius R p (base+1) k
      let Z:=packet R.makes live v o
      let L:=R.family.labels.level d
      ∀U∈House.chilly (WilsonPhysicalHistoryKioskPlaquettes.faces H o) (angularCut (β k)),
      ‖WilsonRegisteredFrozenReading.previous R live v o b U‖*(Real.log (β k))^t
        ≤ ε*L.coeffSize (L.core Z.x):=by
  filter_upwards [WilsonRegisteredAxialChart.measured R simple slow J clear a p base t he,
    (tendsto_add_atTop_nat 1).eventually (torus R simple p (base+1))] with m fare room
  intro N per live d ref v o k b H Z L U cool
  exact fare N per live d ref v o (room per) U fun z hz=>cool z (cells H o hz)

end YM.Integration.WilsonRegisteredAxialRoom
end
