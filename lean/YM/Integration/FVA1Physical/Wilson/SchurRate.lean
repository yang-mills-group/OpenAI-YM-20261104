import YM.Integration.FVA1Physical.Wilson.SchurCore

/-! Every fixed power is paid uniformly on the inner half of the native box. -/
set_option autoImplicit false
set_option maxHeartbeats 550000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Function Set Finset MeasureTheory Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Mosaic MSbar.Lis MSbar.Whisk MSbar.Bakery.Film MSbar.Kelvin
open Push.Uniform Next.SectorChange Pressure RGComparison.Core16
open scoped Classical Topology
variable {G:Gauge}

theorem schur_wall {r : ℝ} (positive : 0<r) (M Q : ℝ) :
    ∀ᶠ y:ℝ in atTop, ∀ d : ℕ, 2*d ≤ spotN y →
      (Real.exp (-r*spotN y)*Real.exp (r*d))*M≤y^(-Q) := by
  let D:=fun y:ℝ=>Real.exp (-(r/2)*(spotN y:ℝ))
  have hv : Van atTop (fun y:ℝ=>y) D := by
    intro a
    apply ((Van.castE (tendsto_id : Tendsto (fun y:ℝ=>y) atTop atTop) (neg_lt_zero.mpr (half_pos positive))) a).cash
    apply Eventually.of_forall; intro y
    rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]
    apply Real.exp_monotone; apply mul_le_mul_of_nonpos_left _ (neg_nonpos.mpr (half_pos positive).le)
    exact (Nat.le_ceil ((Real.log y)^2)).trans (Nat.cast_le.mpr (Nat.le_self_pow (by decide : (4:ℕ)≠0) _))
  have scaled := (hv (-Q-1)).mulY (tendsto_id : Tendsto (fun y:ℝ=>y) atTop atTop) |M|
  filter_upwards [scaled (-Q) (by linarith)] with y cap
  intro d halfbox
  have hd : 2*(d:ℝ) ≤ spotN y := by exact_mod_cast halfbox
  have h := mul_le_mul_of_nonneg_left hd positive.le
  have e : Real.exp (-r*spotN y)*Real.exp (r*d)≤D y := by
    rw [←Real.exp_add]; apply Real.exp_monotone; change _≤-(r/2)*(spotN y:ℝ); linarith only [h]
  exact (mul_le_mul_of_nonneg_left (le_abs_self _) (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le).trans
    ((mul_le_mul_of_nonneg_right e (abs_nonneg M)).trans ((le_abs_self _).trans cap))

theorem purchased_schur_core (J : Voice G) (clear : Clear G J) (χ : ChartRatio G) (hχ : LocalRatio χ)
    (simple : G.Simple) (H H' : Stage) (P : Patch) (K : KernelChoices) (branch : P.Branches K G)
    (p : ℕ) (Q : ℝ) {D : ℝ} (hD : 0≤D) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (b : Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      ‖z‖≤A.fClock*D →
      let y:=tip G P.L x
      let O:=represent (tint G (Exterior.Body 1 A.c) z)
      let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) z
      let l:=address A.F G ∘ Sum.inr
      let M:=schurCovGap A y b
      ∀ i : Key A.F G, 2*separation b (l i) ≤ spotN y →
      (∀ U∈hotel A.F (boxX y b) (boxY y b) J O ν (pillow y) (room y),
        |schurShift A J y z b U i|≤y^(-Q)) ∧
      (∑ j,|M i j| * liftW 0 p (separation (l i) (l j)))≤y^(-Q) ∧
      (∑ j,|M j i| * liftW 0 p (separation (l j) (l i)))≤y^(-Q) := by
  obtain ⟨v,buy⟩:=purchased_chart_chance J clear simple H H' P K branch hD 0
  by_cases ok : 0<v.gap ∧ 0<v.a ∧ 0<v.density
  swap
  · filter_upwards [buy] with x offer; intro A z b patch ker season cap
    have uses := (offer A patch ker season z b cap).1.buys
    exact False.elim (ok ⟨uses.pos_m,uses.pos_a,uses.pos_C⟩)
  let r:=frond v.coords v.density v.gap v.a/2
  have hr : 0<r:= half_pos (div_pos (tiltWidth_pos _ ok.1 ok.2.1 ok.2.2.le) (by norm_num))
  obtain ⟨C,W,seats⟩:=waiting v H H' J χ hχ clear P 3 p
  have rise:=Work.E09.betaF_growth G P.L
  have h:=Mosaic.height rise v J
  have widths:=(h.2.2.2.2.loosen (by norm_num : -(1:ℝ)≤-(1/2))).addR rise h.2.2.1
  filter_upwards [buy,seats,rise.eventually (schur_wall hr W Q),rise.eventually (schur_wall hr (W*C) Q),
    (widths.bouquet rise (by norm_num)).eventually (ge_mem_nhds zero_lt_one)]
    with x offer theater meanPrice covPrice slender
  intro A z b patch ker season cap y O ν l M i inner
  obtain ⟨give,cal,_,_⟩:=offer A patch ker season z b cap
  obtain ⟨solver,suite⟩:=theater.enter _ _ patch season (boxX y b) (boxY y b) A.F z A.v give (by rw [patch]; exact cal.first)
  rw [patch] at suite
  have sol:=solver r hr.le (by dsimp only [r]; linarith)
  have loosen : (0:ℝ)+r≤r+r:=by linarith
  let weak : Solver (includeX (G:=G) A.F (boxX y b)) l 0 r C W p (mold A.pre A.F A.v) :=
    ⟨sol.bids,sol.bsize,sol.hsize,sol.growth.low loosen,sol.sealed.low loosen,sol.travels.low loosen⟩
  obtain ⟨mean,row,col⟩:=schur_core_rows A J χ clear y z b suite weak hr.le i
  have epos : 0≤Real.exp (-r*spotN y)*Eve r b (l i):=mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  refine ⟨fun U live=>(mean U live).trans ?_, (row.trans (covPrice _ inner)),col.trans (covPrice _ inner)⟩
  apply le_trans _ (meanPrice _ inner)
  apply mul_le_mul_of_nonneg_left _ epos
  have br : topP J v y + pillow y ≤ 1 := slender
  exact (mul_le_mul_of_nonneg_left br weak.hsize).trans_eq (mul_one W)
end YM.Integration.FVA1Physical.Wilson
