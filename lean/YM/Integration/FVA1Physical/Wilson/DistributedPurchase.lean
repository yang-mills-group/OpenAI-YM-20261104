import YM.Integration.FVA1Physical.Wilson.DistributedCell

/-! The true distributed inherited Wilson action and any rooted polynomial
insertion with a measured support-weighted coefficient budget. Boundary
dependence is superalgebraically small for each individual coefficient,
uniformly in both cutoffs and periods. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Function Filter Finset Matrix MeasureTheory Lattice RG YM.Wilson Exterior Tree Precision
open MSbar MSbar.Whisk MSbar.Cacao MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Lis MSbar.Mosaic MSbar.Bulk MSbar.Kelvin MSbar.Bakery.Film MSbar.Rolling
open PhysicalNext.Repeat.Legato Push.Uniform Pressure RGComparison.Core16 Next.SectorChange
open scoped Classical Topology
variable {G : Gauge}

theorem distributed_columns (J : Voice G) (clear : Clear G J) (χ : ChartRatio G) (hχ : LocalRatio χ)
    (simple : G.Simple) (H H' : Stage) (P : Patch) (K : KernelChoices) (branch : P.Branches K G)
    (p s m q : ℕ) (hm : p+2 ≤ m) {D : ℝ} (hD : 0 ≤ D) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (b : Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      ‖z‖ ≤ A.fClock*D →
      let y:=tip G P.L x
      Kind A.T → Expanse A.T 1 p → Alto.Wedge A.T Alto.Dean (hatW y) (Alto.cWidth y) s p →
      ∀ (src : PowerSeries (Pot (Joint A.F G))),
      (∀ i ≤ p, Vault (address A.F G) {b} (αm y) s m 0 (PowerSeries.coeff i src) y ∧
        (PowerSeries.coeff i src).totalDegree ≤ m) →
      ∀ U∈hotel A.F (boxX y b) (boxY y b) J (represent (tint G (Exterior.Body 1 A.c) z))
        (vest (priced A.F A.v A.pre.clip A.pre.path) z) (pillow y) (room y),
      ∀ i ≤ p, |PowerSeries.coeff i (bulkColumn A χ z src p) -
        PowerSeries.coeff i (innerColumn A χ J y z b U src p)| ≤ y^(-(q:ℝ)) := by
  obtain ⟨v,buy⟩:=purchased_chart_chance J clear simple H H' P K branch hD 0
  by_cases ok : 0<v.gap ∧ 0<v.a ∧ 0<v.density
  swap
  · filter_upwards [buy] with x offer
    intro A z b hp hk hs hz
    have cash:=(offer A hp hk hs z b hz).1.buys
    exact False.elim (ok ⟨cash.pos_m,cash.pos_a,cash.pos_C⟩)
  obtain ⟨C,W,seats⟩:=waiting v H H' J χ hχ clear P 3 s
  have fr:0<frond v.coords v.density v.gap v.a:=div_pos
    (tiltWidth_pos _ ok.1 ok.2.1 ok.2.2.le) (by norm_num)
  let X:=fun x:ℝ=>tip G P.L x
  have rise : Tendsto X atTop atTop:=Work.E09.betaF_growth G P.L
  have stages:=Mosaic.height rise v J
  have slopes:=(stages.2.2.2.2.loosen (by norm_num : -(1:ℝ) ≤ -(1/2))).addR rise stages.2.2.1
  let fees:=∑ i:Fin (p+1),Round2.gridPrice p i
  filter_upwards [buy,seats,distributed_action J χ hχ simple H H' P K p s m (ε:=1) zero_lt_one,
    rise.eventually_ge_atTop (max D (max fees (1+shade G+W))),rise.eventually_ge_atTop 2,
    (slopes.bouquet rise (by norm_num)).eventually (ge_mem_nhds zero_lt_one),
    (stages.2.2.2.1.bouquet rise (by norm_num)).eventually (ge_mem_nhds zero_lt_one),
    (Mosaic.Issue.thorn_top rise m).eventually (ge_mem_nhds (half_pos fr)),
    Mosaic.Issue.gate (tendsto_id : Tendsto (fun x:ℝ=>x) atTop atTop) simple tendsto_id P.L m,
    rise.eventually (rooted_toll p m (q+1) C (W*C) W)]
    with x offer theater action wide high slender small slow bound toll
  intro A z b patch kernel season hz y hkind hp hw src hsrc U live i hi
  obtain ⟨grant,cal,_,_⟩:=offer A patch kernel season z b hz
  obtain ⟨solv,suite⟩:=theater.enter _ _ patch season (boxX y b) (boxY y b) A.F z A.v grant
    (by rw [patch]; exact cal.first)
  rw [patch] at suite
  let sβ:=Mosaic.Issue.thorn y m
  have pos:sβ>0:=bound.1
  have smallrate : sβ ≤ αm y := by
    apply div_le_self (by unfold αm hatW Alto.flurry; positivity)
    exact_mod_cast (show 1 ≤ m+10 by omega)
  have range : sβ ≤ frond v.coords v.density v.gap v.a/2:=slow
  let l:=address A.F G ∘ Sum.inr
  let idx:=includeX (G:=G) A.F (boxX y b)
  let M:=mold A.pre A.F A.v
  have both:=solv sβ pos.le (by linarith)
  have weaken : (0:ℝ)+sβ ≤ sβ+sβ:=by linarith
  let sol : Solver idx l 0 sβ C W s M :=
    ⟨both.bids,both.bsize,both.hsize,both.growth.low weaken,both.sealed.low weaken,both.travels.low weaken⟩
  let flat : Solver idx l 0 0 C W s M :=
    ⟨both.bids,both.bsize,both.hsize,both.growth.low (by linarith),
      both.sealed.low (by linarith),both.travels.low (by linarith)⟩
  have yy:2 ≤ y:=high
  have y1:1 ≤ y:=by linarith
  have y0:0<y:=zero_lt_one.trans_le y1
  have law:=season.case_
  rw [patch] at law
  have g0 : 0<A.fClock:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos y0).trans_le law.beta))
  have scale : 0 ≤ A.fClock⁻¹ ∧ A.fClock⁻¹ ≤ y := by
    change 0 ≤ (Real.sqrt A.pre.beta)⁻¹⁻¹ ∧ (Real.sqrt A.pre.beta)⁻¹⁻¹ ≤ y
    rw [inv_inv]
    exact ⟨Real.sqrt_nonneg _,(Real.sqrt_le_iff).2 ⟨y0.le,law.upper.trans
      (by nlinarith only [mul_nonneg y0.le (sub_nonneg.mpr yy)])⟩⟩
  have span : max D (max fees (1+shade G+W)) ≤ y:=wide
  have size : 1+shade G+W ≤ y:=(le_max_right _ _).trans ((le_max_right _ _).trans span)
  have y3:y ≤ y^3:=by simpa only [pow_one] using (pow_le_pow_right₀ y1 (by decide:1 ≤ 3))
  have y23 : y^2 ≤ y^3:=pow_le_pow_right₀ y1 (by decide : 2 ≤ 3)
  have zu : ‖A.fClock⁻¹•z‖ ≤ y^3 := by
    rw [norm_smul,Real.norm_of_nonneg scale.1]
    refine (mul_le_mul_of_nonneg_left hz scale.1).trans ?_
    rw [←mul_assoc,inv_mul_cancel₀ g0.ne',one_mul]
    exact ((le_max_left ..).trans span).trans y3
  have bud : topP J v y+pillow y ≤ 1:=slender
  have thin : rot v y ≤ 1:=small
  have glue := suite.seat.glued.le.trans suite.seat.lifts
  let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) z
  have ns : ‖ν‖ ≤ 1:=((le_add_of_nonneg_right glue).trans suite.seat.ht).trans thin
  have center (i: Key A.F G): |bulkCoordinate A z i| ≤ 1+shade G := by
    have vv := (suite.seat.sums i.1).trans
      ((mul_le_mul_of_nonneg_left thin (shade_pos G).le).trans_eq (mul_one _))
    change |ν i+(linCash A.F z i.1) i.2| ≤ 1+shade G
    exact (abs_add_le ..).trans (add_le_add ((norm_le_pi_norm ν i).trans ns)
      ((PiLp.norm_apply_le _ _).trans vv))
  have inside(i:Key A.F G): |interiorCoordinate A J y z b U i| ≤ y := by
    have delta := (schur_core_rows A J χ clear y z b suite flat le_rfl i).1 U live
    change |interiorCoordinate A J y z b U i-bulkCoordinate A z i| ≤ _ at delta
    simp only [neg_zero,zero_mul,Real.exp_zero,Eve,one_mul] at delta
    have wi:W*(topP J v y+pillow y) ≤ W:=(mul_le_mul_of_nonneg_left bud flat.hsize).trans_eq (mul_one _)
    have tri:=abs_add_le (interiorCoordinate A J y z b U i-bulkCoordinate A z i) (bulkCoordinate A z i)
    rw [sub_add_cancel] at tri
    linarith only [tri,delta,wi,center i,size]
  have scaled (u:Positions (Key A.F G)) (h:∀ i,|u i| ≤ y): ‖A.fClock⁻¹•u‖ ≤ y^3 := by
    rw [norm_smul,Real.norm_of_nonneg scale.1]
    have nu:‖u‖ ≤ y := (pi_norm_le_iff_of_nonneg y0.le).mpr h
    exact (mul_le_mul scale.2 nu (norm_nonneg _) y0.le).trans
      ((le_of_eq (sq y).symm).trans y23)
  have outside : ‖bulkPoint A z‖ ≤ y^3:=by
    rw [bulkPoint,norm_meet]; exact max_le zu (scaled _ (fun j=> (center j).trans
      ((le_add_of_nonneg_right sol.hsize).trans size)))
  have inward : ‖innerPoint A J y z b U‖ ≤ y^3:=by
    rw [innerPoint,norm_meet];exact max_le zu (scaled _ inside)
  obtain ⟨kind,bank⟩:=action A patch kernel season hkind hp hw
  have cash (i':ℕ)(h:i' ≤ p) := bank i' h
  simp only [Real.rpow_one] at cash
  let q':Fin (p+1):=⟨i,by omega⟩
  have price:=price_from_taste p (bulkColumn A χ z src p) (innerColumn A χ J y z b U src p)
    (B:=y^(-((q+1:ℕ):ℝ))) (fun t ht=>
      (cell_columns A χ J clear y z b s m p suite sol pos.le y0.le scale bud U live outside inward src kind
        (fun i' h=>⟨Tokew.soft (cash i' h).1 smallrate pos.le, (cash i' h).2.trans (by omega)⟩)
        (fun i' h=>⟨Quote.cooled pos.le smallrate (hsrc i' h).1,(hsrc i' h).2⟩) t ht).trans toll) q'
  have grd : Round2.gridPrice p q' ≤ y :=
    (Finset.single_le_sum (f:=Round2.gridPrice p) (fun j _=>sum_nonneg fun _ _=>abs_nonneg _) (mem_univ q')).trans
      ((le_max_left ..).trans ((le_max_right ..).trans span))
  refine price.trans ((mul_le_mul_of_nonneg_right grd (Real.rpow_nonneg y0.le _)).trans_eq ?_)
  nth_rw 1 [←Real.rpow_one y]
  rw [←Real.rpow_add y0]
  congr 1; push_cast; ring
end YM.Integration.FVA1Physical.Wilson
