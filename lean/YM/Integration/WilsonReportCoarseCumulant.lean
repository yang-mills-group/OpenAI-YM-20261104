import YM.Integration.WilsonReportSpectatorModes
import YM.Integration.WilsonReportSeparatedMoments

/-! Connected coarse Wilson truncation with one independently measured spectator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportCoarseCumulant
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi
open Primitives.GCC.Anchor Comparison.RG02.Cumulants
open Extra.Trajectories (connected)
open Next.Rank Next.Rank.Spindle OPE OPE.Yarn OPE.Strobe OPE.Strobe.Vista26
open PhysicalNext.Repeat.Legato MergeProof MergeProof.Ribbons.ManyCopies.Patrol
open WilsonReportSpectatorModes WilsonReportMomentDifference
open scoped BigOperators Classical
variable {G : Gauge} {C : Family G} {W r D} {V : Type} [DecidableEq V]
variable {N p k : ℕ}

private theorem product_gap {I : Type*} [DecidableEq I] (q : Finset I) (f g : I → ℂ)
    {e M : ℝ} (he : 0 ≤ e) (hM : 1 ≤ M) (hf : ∀ i, ‖f i‖ ≤ M) (hg : ∀ i, ‖g i‖ ≤ M)
    (h : ∀ i, ‖f i-g i‖ ≤ e) : ‖(∏ j ∈ q, f j) - (∏ j ∈ q, g j)‖ ≤ q.card*e*M^q.card := by
  induction q using Finset.induction_on with
  | empty => simp
  | @insert i q hi ih =>
    let X := ∏ j ∈ q, f j
    let Y := ∏ j ∈ q, g j
    have hy : ‖Y‖ ≤ M^q.card := by
      dsimp only [Y]
      rw [norm_prod]
      exact (Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hg j)).trans_eq (by simp)
    simp only [prod_insert hi,card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one,pow_succ]
    change ‖f i*X-g i*Y‖ ≤ ((q.card:ℝ)+1)*e*(M^q.card*M)
    calc
      _ = ‖f i*(X-Y)+(f i-g i)*Y‖ := congrArg norm (by ring)
      _ ≤ ‖f i‖*‖X-Y‖+‖f i-g i‖*‖Y‖ := by simpa only [norm_mul] using norm_add_le (f i*(X-Y)) ((f i-g i)*Y)
      _ ≤ M*(q.card*e*M^q.card)+e*M^q.card := add_le_add
        (mul_le_mul (hf i) ih (norm_nonneg _) (zero_le_one.trans hM))
        (mul_le_mul (h i) hy (norm_nonneg _) he)
      _ ≤ _ := by nlinarith only [le_mul_of_one_le_right (mul_nonneg he (pow_nonneg (zero_le_one.trans hM) q.card)) hM]


private theorem partitions [Fintype V] (Γ : Census (Option V)) (s : Γ.Mode) (A B : Poly Γ)
    (au : A.part Γ.quiet=1) (bu : B.part Γ.quiet=1) {e M : ℝ} (he : 0≤e) (hM : 1≤M)
    (ac : ∀q, ‖A.part q‖≤M) (bc : ∀q, ‖B.part q‖≤M) (diff : ∀q, ‖A.part q-B.part q‖≤e) :
    ‖(connected A).part s-(connected B).part s‖ ≤
      multiplicity Γ s * e * M^(Fintype.card (Hot Γ)) := by
  rw [log_partition A au, log_partition B bu, ← Finset.sum_sub_distrib, WilsonReportMomentDifference.multiplicity,
      Finset.sum_mul, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun t _ => ?_)
  rw [← mul_sub, norm_mul]
  have h := product_gap t.val (fun i : Hot Γ => A.part i.val) (fun i : Hot Γ => B.part i.val)
    he hM (fun i => ac i.val) (fun i => bc i.val) (fun i => diff i.val)
  have grow := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM (Finset.card_le_univ t.val))
    (mul_nonneg (Nat.cast_nonneg (α:=ℝ) t.val.card) he)
  exact (mul_le_mul_of_nonneg_left (h.trans grow) (norm_nonneg _)).trans_eq (by ring)


private theorem mass [Fintype V] (Γ : Census (Option V)) (q : Γ.Mode) (hC : C.Makes) (hk : k≤N)
    (Y : Config G (C.side k p)→ℂ) (iY : Integrable Y (Therm.scene C.path N p k))
    (low : (∫ U, ‖Y U‖ ∂(Therm.scene C.path N p k))≤1)
    (F : V → Config G (C.side k p)→ℂ) {a:ℝ} (ha : 1≤a) (hF : ∀ j U, ‖F j U‖≤a) :
    ‖(board (N:=N) Γ Y F).part q‖≤a^(Fintype.card V) := by
  let μ := Therm.scene C.path N p k
  letI : IsProbabilityMeasure μ := Therm.probability hC.wilson hk
  let T := fun U => if none∈q.val then Y U else 1
  have iT : Integrable T μ := by
    by_cases h : none∈q.val
    · simpa only [T,h,if_true] using iY
    · simpa only [T,h,if_false] using (integrable_const (1:ℂ) : Integrable (fun _ => (1:ℂ)) μ)
  have Tcost : (∫ U, ‖T U‖ ∂μ)≤1 := by
    by_cases h : none∈q.val
    · simpa only [T,h,if_true] using low
    · simp [T,h]
  change ‖∫ U,T U*(∏ j∈q.val.eraseNone,F j U) ∂μ‖≤_
  calc
    _ ≤ ∫ U, ‖T U*(∏ j∈q.val.eraseNone,F j U)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ U, ‖T U‖*a^(Fintype.card V) ∂μ := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (iT.norm.mul_const _)
      refine Eventually.of_forall fun U => ?_
      dsimp only
      rw [norm_mul,norm_prod]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hF j U)).trans
        ((Finset.prod_const a).le.trans (pow_le_pow_right₀ ha (card_le_univ _)))
    _ ≤ _ := by rw [integral_mul_const]; simpa using mul_le_mul_of_nonneg_right Tcost (pow_nonneg (zero_le_one.trans ha) (Fintype.card V))

private theorem half (e : ℕ) (hG : G.Simple) :
    ∀ᶠ k : ℕ in atTop,
      Real.exp (-((C.path.levels.budget k).B:ℝ))*C.path.levels.clock.hatBeta k^e ≤
        Real.exp (-((C.path.levels.budget k).B:ℝ)/2) := by
  have grow := Next.Rank.Station.hat_rate C.path.levels hG
  filter_upwards [(Real.tendsto_log_atTop.comp grow).eventually_ge_atTop (2*(e:ℝ))] with k hi
  let b := C.path.levels.clock.hatBeta k
  have hb : 1≤b := (C.path.levels.fits.delayed k).le
  let B := ((C.path.levels.budget k).B:ℝ)
  have sq : (Real.log b)^2 ≤ B := Nat.le_ceil _
  have price : b^e ≤ Real.exp (B/2) := by
    apply (Real.log_le_iff_le_exp (pow_pos (zero_lt_one.trans_le hb) _)).mp
    rw [Real.log_pow]
    change 2*(e:ℝ)≤Real.log b at hi
    have pay := mul_le_mul_of_nonneg_right hi (Real.log_nonneg hb)
    nlinarith
  exact (mul_le_mul_of_nonneg_left price (Real.exp_nonneg (-B))).trans_eq
    (by rw [←Real.exp_add]; congr 1; ring)

/-- The separately scheduled arbitrary gauge exterior is one actual occupied mark in
the measured connected Wilson expectation. Its L¹ cost occurs only once. At all
late stages, before any cutoff, period, placements or true measured exterior, the
complete sum over admissible disconnected partitions costs exp(-B_k/2). -/
theorem purchased [Fintype V] (hG : G.Simple) (hC : C.Makes) (book : Log.OnBudget C.path.levels)
    (citizen : Citizen C W r D) (Γ : Census (Option V)) (d : V→ℕ) (t : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ N p, k<N → ∀ x : V→Site (C.side k p), ∀ v : (j:V)→C.label (d j),
    (∀j,Spindle.paid C (d j) k N p (v j)≤C.path.levels.clock.hatBeta k^t) →
    ∀ X : Config G (C.side k p)→ℂ, Integrable X (Therm.scene C.path N p k) →
    ∀ s : Γ.Mode, none∈s.val →
    ‖(connected (board (N:=N) Γ X (regularPack (N:=N) d x v))).part s -
      (connected (board (N:=N) Γ X (ScenePack (N:=N) d x v))).part s‖ ≤
      (∫ U, ‖X U‖ ∂(Therm.scene C.path N p k)) * multiplicity Γ s *
        Real.exp (-((C.path.levels.budget k).B:ℝ)/2) := by
  let n := Fintype.card V
  let h := Fintype.card (Hot Γ)
  let e := (t+2)*n*h
  have grow := Next.Rank.Station.hat_rate C.path.levels hG
  filter_upwards [WilsonReportExteriorBudget.purchased hG hC book citizen d t,
    (grow.eventually_ge_atTop 4),half (C:=C) e hG,
    eventually_all.mpr (fun j : V => eventually_ge_atTop (C.ref (d j)))] with k subsetPrice large extra refs
  intro N p hk x v funds X iX s active
  let μ := Therm.scene C.path N p k
  letI : IsProbabilityMeasure μ := Therm.probability hC.wilson hk.le
  obtain ⟨Y,iY,low,same⟩ := normalized X iX
  let F := regularPack (N:=N) d x v
  let E := ScenePack (N:=N) d x v
  let L := ∫ U, ‖X U‖ ∂μ
  let b := C.path.levels.clock.hatBeta k
  let B := ((C.path.levels.budget k).B:ℝ)
  let a := b^(t+2)
  have hb : 1≤b := (C.path.levels.fits.delayed k).le
  have ha : 1≤a := one_le_pow₀ hb
  have hL : 0≤L := integral_nonneg (fun _ => norm_nonneg _)
  obtain ⟨σ,χ,H⟩ := Yarn.enroll citizen.toSharper hC hG
  have cap (j) : 4*((C.path.levels.params k).columns*Spindle.paid C (d j) k N p (v j))≤a := by
    have h₁ := mul_le_mul (book.present k) (funds j) (paid_pos C (d j) k N p (v j)) (zero_le_one.trans hb)
    calc
      _ ≤ b*(b*b^t) := mul_le_mul large h₁ (mul_nonneg (zero_le_one.trans (C.path.levels.params k).columns_ge) (paid_pos C (d j) k N p (v j))) (zero_le_one.trans hb)
      _ = _ := by dsimp only [a]; ring
  have hF (j U) : ‖F j U‖≤a := (wholeSize H citizen (v j) (x j) hk (refs j) U).trans
    ((mul_le_mul_of_nonneg_right (by norm_num : (3:ℝ)≤4)
      (mul_nonneg (zero_le_one.trans (C.path.levels.params k).columns_ge) (paid_pos C (d j) k N p (v j)))).trans (cap j))
  have hE (j U) : ‖E j U‖≤a := (beadSize H citizen (v j) (x j) (C.path.levels.budget k).B hk (refs j) U).trans (cap j)
  have gap (q : Γ.Mode) : ‖(board (N:=N) Γ Y F).part q-(board (N:=N) Γ Y E).part q‖≤Real.exp (-B) := by
    by_cases z : none∈q.val
    · have price := subsetPrice N p hk x v funds q.val.eraseNone Y iY
      exact (show ‖(board (N:=N) Γ Y F).part q-(board (N:=N) Γ Y E).part q‖≤(∫ U,‖Y U‖ ∂μ)*Real.exp (-B) by
        change ‖(∫ U, (if none∈q.val then Y U else 1)*fineJob F q.val.eraseNone U ∂μ)-
          (∫ U, (if none∈q.val then Y U else 1)*fineJob E q.val.eraseNone U ∂μ)‖≤_
        simpa only [z,if_true] using price).trans ((mul_le_mul_of_nonneg_right low (Real.exp_nonneg _)).trans_eq (one_mul _))
    · have price := subsetPrice N p hk x v funds q.val.eraseNone (fun _ => 1) (integrable_const (1:ℂ))
      change ‖(∫ U, (if none∈q.val then Y U else 1)*fineJob F q.val.eraseNone U ∂μ)-
        (∫ U, (if none∈q.val then Y U else 1)*fineJob E q.val.eraseNone U ∂μ)‖≤_
      have one : (∫ _U : Config G (C.side k p), ‖(1:ℂ)‖ ∂μ)=1 := by simp
      have hp : ‖(∫ U, fineJob F q.val.eraseNone U ∂μ)-(∫ U, fineJob E q.val.eraseNone U ∂μ)‖ ≤
          (∫ _U : Config G (C.side k p), ‖(1:ℂ)‖ ∂μ)*Real.exp (-B) := by
        simpa only [one_mul] using price
      simpa only [z,if_false,one_mul] using hp.trans_eq ((congrArg (·*Real.exp (-B)) one).trans (one_mul _))
  have paid := partitions Γ s (board (N:=N) Γ Y F) (board (N:=N) Γ Y E) (quiet hC hk.le Y F) (quiet hC hk.le Y E)
    (Real.exp_nonneg (-B)) (one_le_pow₀ ha) (fun q => mass Γ q hC hk.le Y iY low F ha hF)
    (fun q => mass Γ q hC hk.le Y iY low E ha hE) gap
  have bill : (a^n)^h=b^e := by dsimp only [a,e]; rw [←pow_mul,←pow_mul,mul_assoc]
  have tariff : ‖(connected (board (N:=N) Γ Y F)).part s-(connected (board (N:=N) Γ Y E)).part s‖≤
      multiplicity Γ s*Real.exp (-B/2) :=
    paid.trans (calc
      _ = multiplicity Γ s*(Real.exp (-B)*b^e) := by rw [←bill]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left extra (WilsonReportSeparatedMoments.count_nonneg Γ s))
  change ‖(connected (board (N:=N) Γ X F)).part s-(connected (board (N:=N) Γ X E)).part s‖≤_
  rw [linear hC hk.le s active X Y (L:ℂ) same F,linear hC hk.le s active X Y (L:ℂ) same E,←mul_sub,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hL]
  exact (mul_le_mul_of_nonneg_left tariff hL).trans_eq (mul_assoc _ _ _).symm

end YM.Integration.WilsonReportCoarseCumulant
end

