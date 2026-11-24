import YM.Integration.FVA1Physical.Wilson.SchurStencil

/-! For any fixed polynomial in rescaled interior field coordinates, the effect
of all exterior data on the true Gaussian part of the inherited Wilson step is
smaller than every inverse power. The native period and cutoffs are unrestricted. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Matrix Function Filter MeasureTheory Set Finset Lattice RG YM.Wilson Tree Precision Exterior
open MSbar MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock MSbar.Whisk MSbar.Bulk
open MSbar.Lis MSbar.Mosaic MSbar.Bakery.Film MSbar.Kelvin MSbar.Cacao
open Push.Uniform Next.SectorChange RGComparison.Core16 Pressure
open scoped Classical Topology
variable {G : Gauge} {σ : Type} [Fintype σ] [DecidableEq σ]

def interiorParameters (A : Mosaic.Issue G) (J : Voice G) (y : ℝ) (z : Positions (Primary A.c G))
    (b : Site A.f) (U : Config G A.f) (s : σ→Lake A.F (boxX y b) G) : WickSlot σ→ℝ :=
  let i:=includeX (G:=G) A.F (boxX y b)
  parameters (fun j=>A.fClock⁻¹*interiorCoordinate A J y z b U (i (s j)))
    (((pinch i (mold A.pre A.F A.v))⁻¹).submatrix s s)

def bulkParameters (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (s : σ→Key A.F G) : WickSlot σ→ℝ :=
  parameters (fun j=>A.fClock⁻¹*bulkCoordinate A z (s j)) (((mold A.pre A.F A.v)⁻¹).submatrix s s)

omit [Fintype σ] [DecidableEq σ] in
theorem purchased_parameters (J : Voice G) (clear : Clear G J) (χ : ChartRatio G) (hχ : LocalRatio χ)
    (simple : G.Simple) (H H' : Stage) (P : Patch) (K : KernelChoices) (branch : P.Branches K G)
    (pol : Pot (WickSlot σ)) (Q : ℕ) {D : ℝ} (hD : 0≤D) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (b : Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      ‖z‖≤A.fClock*D →
      let y:=tip G P.L x
      let idx:=includeX (G:=G) A.F (boxX y b)
      let O:=represent (tint G (Exterior.Body 1 A.c) z)
      let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) z
      ∀ (s : σ→Lake A.F (boxX y b) G),
      (∀ i, 2*separation b (address A.F G (Sum.inr (idx (s i)))) ≤ spotN y) →
      ∀ U∈hotel A.F (boxX y b) (boxY y b) J O ν (pillow y) (room y),
      (mold A.pre A.F A.v).PosDef ∧
      |MvPolynomial.eval (interiorParameters A J y z b U s) pol -
        MvPolynomial.eval (bulkParameters A z (idx ∘ s)) pol| ≤ y^(-(Q:ℝ)) := by
  obtain ⟨M,d,hM,budget⟩:=parameter_stencil_price pol
  let e:ℝ:=((Q+2*d+1:ℕ):ℝ)
  obtain ⟨v,buy⟩:=purchased_chart_chance J clear simple H H' P K branch hD 0
  obtain ⟨C,W,seats⟩:=waiting v H H' J χ hχ clear P 3 0
  have rise:=Work.E09.betaF_growth G P.L
  have thick:= (Mosaic.height rise v J).2.2.2.1
  filter_upwards [buy,seats,purchased_schur_core J clear χ hχ simple H H' P K branch 0 (e+2) hD,
     rise.eventually_ge_atTop (max C (max M (2+shade G))),rise.eventually_ge_atTop 2,
     (thick.bouquet rise (by norm_num)).eventually (ge_mem_nhds zero_lt_one)] with x offer theater core wide high slim
  intro A z b patch kernel season hz y idx O ν s near U hotel
  obtain ⟨gr,cal,_,_⟩:=offer A patch kernel season z b hz
  obtain ⟨solv,suite⟩:=theater.enter _ _ patch season (boxX y b) (boxY y b) A.F z A.v gr (by rw [patch]; exact cal.first)
  rw [patch] at suite
  have fr:0<frond v.coords v.density v.gap v.a:=div_pos
    (tiltWidth_pos _ gr.buys.pos_m gr.buys.pos_a gr.buys.pos_C.le) (by norm_num)
  have sol:=solv 0 le_rfl (by simpa using fr.le)
  have hy : 2≤y:=high
  have hy1 : 1≤y:=by linarith
  have hy0 : 0<y:=zero_lt_one.trans_le hy1
  have span : max C (max M (2+shade G))≤y:=wide
  have hC : C≤y:= (le_max_left ..).trans span
  have hA : M≤y:= ((le_max_left M _).trans (le_max_right C _)).trans span
  have hwidth : 2+shade G≤y:= ((le_max_right M _).trans (le_max_right C _)).trans span
  have hy2 : y≤y^2:=by nlinarith only [mul_nonneg hy0.le (sub_nonneg.mpr hy1)]
  have cap : rot v y≤1:=slim
  let Hm:=mold A.pre A.F A.v
  let V:= (MSbar.Kelvin.pinch idx Hm)⁻¹
  have hp:=season.case_
  rw [patch] at hp
  have scale : 0 ≤ A.fClock⁻¹ ∧ A.fClock⁻¹ ≤ y := by
    change 0 ≤ (Real.sqrt A.pre.beta)⁻¹⁻¹ ∧ (Real.sqrt A.pre.beta)⁻¹⁻¹ ≤ y
    rw [inv_inv]
    exact ⟨Real.sqrt_nonneg _,(Real.sqrt_le_iff).2 ⟨hy0.le,hp.upper.trans (by nlinarith only [mul_nonneg hy0.le (sub_nonneg.mpr hy)])⟩⟩
  let a:=interiorCoordinate A J y z b U
  let c:=bulkCoordinate A z
  let L:=address A.F G ∘ Sum.inr
  have bank:=core A z b patch kernel season hz
  have pos:= Real.rpow_nonneg hy0.le (-(e+2))
  have unit : y^(-(e+2))≤1:=Real.rpow_le_one_of_one_le_of_nonpos hy1 (by dsimp only [e]; have hh : (0:ℝ)≤↑(Q+2*d+1) := Nat.cast_nonneg _; linarith)
  have weight : ∀ i, |a (idx (s i))-c (idx (s i))| ≤ y^(-(e+2)):=fun i=>
    (bank (idx (s i)) (near i)).1 U hotel
  have center : ∀ i, |c i|≤1+shade G := by
    intro i
    have hroom := suite.seat.glued.le.trans suite.seat.lifts
    have ns : ‖ν‖≤1:=((le_add_of_nonneg_right hroom).trans suite.seat.ht).trans cap
    have vv : ‖linCash A.F z i.1‖ ≤ shade G:= (suite.seat.sums i.1).trans
      ((mul_le_mul_of_nonneg_left cap (shade_pos G).le).trans_eq (mul_one _))
    change |ν i+(linCash A.F z i.1) i.2|≤1+shade G
    exact (abs_add_le ..).trans (add_le_add ((norm_le_pi_norm ν i).trans ns)
      ((PiLp.norm_apply_le _ _).trans vv))
  have shifted : ∀ i, |a (idx (s i))|≤y:= by
    intro i
    have de: a (idx (s i))=a (idx (s i))-c (idx (s i))+c (idx (s i)):=by ring
    rw [de]; exact (abs_add_le ..).trans ((add_le_add ((weight i).trans unit) (center _)).trans (by linarith))
  have emb (i j) : extendM idx V (idx i) (idx j)=V i j :=
    congr_fun (congr_fun (embeds idx (secureY A.F (boxX y b) G) V) i) j
  have cv (i j) : |V (s i) (s j) - Hm⁻¹ (idx (s i)) (idx (s j))| ≤ y^(-(e+2)):=by
    rw [abs_sub_comm,←emb]
    exact schur_core_entry L (schurCovGap A y b) _ (idx (s i)) (idx (s j)) (bank _ (near i)).2.1
  have v1 i j : |V (s i) (s j)|≤y^2 := by
    rw [←emb]; exact (LoopNet.single (by norm_num : (0:ℝ)≤0+0) sol.sealed _ _).trans (hC.trans hy2)
  have v2 i j : |Hm⁻¹ (idx (s i)) (idx (s j))|≤y^2 :=
    (LoopNet.single (by norm_num : (0:ℝ)≤0+0) sol.growth _ _).trans (hC.trans hy2)
  have scale2 : y^2*y^(-(e+2))=y^(-e):=by
    rw [←Real.rpow_two,←Real.rpow_add hy0]; congr 1; ring
  have epos:=Real.rpow_nonneg hy0.le (-e)
  refine ⟨sol.bids,?_⟩
  apply le_trans (budget (fun i=>A.fClock⁻¹*a (idx (s i))) (fun i=>A.fClock⁻¹*c (idx (s i)))
    (fun i j=>V (s i) (s j)) (fun i j=>Hm⁻¹ (idx (s i)) (idx (s j))) (y^2) (y^(-e)) (hy1.trans hy2) epos
    (fun i=> by rw [abs_mul,abs_of_nonneg scale.1]; exact (mul_le_mul scale.2 (shifted i) (abs_nonneg _) hy0.le).trans_eq (sq y).symm)
    (fun i=> by rw [abs_mul,abs_of_nonneg scale.1]; exact (mul_le_mul scale.2 ((center _).trans (by linarith)) (abs_nonneg _) hy0.le).trans_eq (sq y).symm)
    v1 v2
    (fun i=> by
        rw [←mul_sub,abs_mul,abs_of_nonneg scale.1]
        exact (mul_le_mul (scale.2.trans hy2) (weight i) (abs_nonneg _) (sq_nonneg _)).trans_eq scale2)
    (fun i j=>(cv i j).trans (Real.rpow_le_rpow_of_exponent_le hy1 (by linarith)))) ?_
  refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA (by positivity)) epos).trans_eq ?_
  rw [←pow_mul,←pow_succ',←Real.rpow_natCast,←Real.rpow_add hy0]; congr 1; dsimp [e]; push_cast; ring

theorem purchased_wick_stencil (J : Voice G) (clear : Clear G J) (χ : ChartRatio G) (hχ : LocalRatio χ)
    (simple : G.Simple) (H H' : Stage) (P : Patch) (K : KernelChoices) (branch : P.Branches K G)
    (pol : Pot σ) (Q : ℕ) {D : ℝ} (hD : 0≤D) :
    ∀ᶠ x:ℝ in atTop, ∀ (A : Mosaic.Issue G) (z : Positions (Primary A.c G)) (b : Site A.f),
      A.S.patch=P → A.S.kernel=K → Season J H H' x A.pre A.post A.S (courage G P.L x) →
      ‖z‖≤A.fClock*D →
      let y:=tip G P.L x
      let idx:=includeX (G:=G) A.F (boxX y b)
      let O:=represent (tint G (Exterior.Body 1 A.c) z)
      let ν:=vest (priced A.F A.v A.pre.clip A.pre.path) z
      ∀ (s : σ→Lake A.F (boxX y b) G),
      (∀ i, 2*separation b (address A.F G (Sum.inr (idx (s i)))) ≤ spotN y) →
      ∀ U∈hotel A.F (boxX y b) (boxY y b) J O ν (pillow y) (room y),
      |interiorReading A J y z b U s pol - bulkReading A z (idx ∘ s) pol| ≤ y^(-(Q:ℝ)) := by
  filter_upwards [purchased_parameters J clear χ hχ simple H H' P K branch (wickStencil pol) Q hD] with x paid
  intro A z b patch kernel season hz y idx O ν s near U hotel
  obtain ⟨pos,r⟩:=paid A z b patch kernel season hz s near U hotel
  have hp : ((pinch idx (mold A.pre A.F A.v))⁻¹).PosDef := (pos.submatrix (secureY A.F (boxX y b) G)).inv
  change |gaussianReading s (fun i=>A.fClock⁻¹ * interiorCoordinate A J y z b U (idx i))
    ((pinch idx (mold A.pre A.F A.v))⁻¹) pol -
    gaussianReading (idx ∘ s) (fun i=>A.fClock⁻¹ * bulkCoordinate A z i) _ pol| ≤ _
  rw [gaussianReading_coeff s _ _ hp pol,gaussianReading_coeff (idx ∘ s) _ _ pos.inv pol]
  exact r

end YM.Integration.FVA1Physical.Wilson
