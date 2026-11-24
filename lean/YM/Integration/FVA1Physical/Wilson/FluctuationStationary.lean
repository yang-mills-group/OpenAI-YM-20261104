import YM.Integration.FVA1Physical.Wilson.FluctuationPurchase
import YM.Integration.FVA1Physical.Wilson.StationarySize

/-! The true stationary point has only a polylogarithmic rescaled radius,
even when the coarse boundary moves on the physical fluctuation scale. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Duel MSbar.Bout MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling
open PhysicalNext.Repeat.Legato Push.Uniform Pressure RGComparison.Core16 Next.SectorChange
open scoped Classical Topology
variable {G:Gauge}

theorem fluctuation_stationary (J:Voice G) (clear:Clear G J) (simple:G.Simple)
    (H H':Stage) (P:Patch) (K:KernelChoices) (branch:P.Branches K G) {D:ℝ} (hD:0 ≤ D) :
    ∀ᶠ x:ℝ in atTop, ∀ (A:Mosaic.Issue G), A.S.patch=P → A.S.kernel=K →
      Season J H H' x A.pre A.post A.S (courage G P.L x) →
      let y:=tip G P.L x
      ∀ (z:Positions (Primary A.c G)), ‖z‖ ≤ D*room y → ‖bulkPoint A z‖ ≤ (hatW y)^2 := by
  obtain ⟨v,buy⟩:=purchased_fluctuation_chance J clear simple H H' P K branch hD 0
  let gy:=Work.E09.betaF_growth G P.L
  let M:=1+ceilingP v+shade G
  have M0:0 ≤ M:=by unfold M ceilingP;positivity [shade_pos G]
  have falls:Tendsto (fun x=>D*room (tip G P.L x)) atTop (𝓝 0):=by
    simpa only [Function.comp_def,zero_mul,zero_add] using (hotel_physical_small v J 0 D).comp gy
  have radius:=hotel_scalar 0 D (by norm_num) hD
  filter_upwards [buy,gy.eventually_gt_atTop 1,(Alto.broad.comp gy).eventually_ge_atTop M,
    falls.eventually (eventually_lt_nhds v.first),falls.eventually (eventually_lt_nhds zero_lt_one),gy.eventually radius]
    with x receipt pos wide tiny unit band
  intro A hp hk season y z h
  obtain ⟨paid,_,_,_⟩:=receipt A hp hk season z 0 h
  have law:=season.case_
  rw [hp] at law
  have hy:0<y:=zero_lt_one.trans pos
  have localScale:Mosaic.lensT y A.fClock:=Mosaic.ever hy law.beta law.upper
  have hg:0<A.fClock:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos hy).trans_le law.beta))
  let r:=D*room y/A.fClock
  have grant:A.fClock*r=D*room y:=by dsimp only [r];field_simp
  have hr:0 ≤ r:=div_nonneg ((norm_nonneg _).trans h) hg.le
  have inner:=stationary_size A v paid hr hg (grant.trans_lt tiny) (grant.le.trans unit.le) z (h.trans_eq grant.symm)
  have hvol:r ≤ vol y:= by
    apply (div_le_iff₀ hg).mpr
    simpa only [zero_mul,zero_add,mul_comm A.fClock] using band A.fClock localScale
  have hw:0 ≤ hatW y:=by unfold hatW Alto.flurry; positivity
  calc ‖bulkPoint A z‖ ≤ M*r := inner
       _ ≤ M*hatW y := mul_le_mul_of_nonneg_left (hvol.trans (by unfold vol;linarith only [hw])) M0
       _ ≤ (hatW y)^2 := by rw [sq];exact mul_le_mul_of_nonneg_right (show M ≤ hatW y from wide) hw

end YM.Integration.FVA1Physical.Wilson
