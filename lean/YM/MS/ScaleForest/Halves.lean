import YM.MS.ScaleForest.LineSums
/-!
# Ghost and gauge lines of the calculation

The actual Feynman rules split by sectors. Include BOTH orders of FP
contraction as usual and no extra loop sign besides the Grassmann algebra.
"true" here means the FP odd lines, UNRELATED to the GraphSum Boolean.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open scoped Topology ContDiff
variable {G : Gauge} {m n h : ℕ} {K : Rip G} {b : Bool}

def pickLine (p : Bool) (K : Rip G) : Rip G := fun m i j q => if parity i=p then K m i j q else 0

variable (p : Bool)

private theorem travels_line {S : Pilot ℂ (SectorP m) (Landau.parity (A:=L m) (C:=G.ColorIndex))}
    (ht : Transport S (K m) (K m)) : Transport S (pickLine p K m) (pickLine p K m) := by
  intro i a b; unfold pickLine; split <;> rename_i h
  · rw [ht]; refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun k _=> ?_
    split; rfl; next hv=>
      have he : S.fieldC j a=0:= by by_contra hp; exact hv (( S.pair_zero j a hp ).trans h)
      rw [he]; simp
  symm; refine Finset.sum_eq_zero fun j _=> Finset.sum_eq_zero fun k _=> ?_
  split; next hv =>
    rw [ show S.fieldC j a=0 from (by by_contra hp; exact h (( S.pair_zero j a hp ).symm.trans hv))]; simp
  simp

theorem pulse_line (t : ℝ) (a : ℂ) (K : Rip G) : pulse a t (pickLine p K)=pickLine p (pulse a t K) := by
  funext m i j q; unfold pickLine pulse; split <;> simp [*]

theorem halves (K : Rip G) : pickLine false K+pickLine true K=K := by
  funext m i j q; cases h:parity i <;> simp [pickLine,h]

theorem pick_quality (ht : HalfKernel K) : HalfKernel (pickLine p K) := by
  constructor
  · intro b
    obtain ⟨hp,he⟩:= ht.forms b
    refine ⟨?_, fun m x hx=> travels_line p (he.turn m x hx), fun h i j q=> ?_⟩
    · intro m i j; dsimp only; by_cases h : parity i=p
      · rw [show pickLine p K m i j=K m i j from funext fun _=>if_pos h]; exact hp m i j
      rw [show pickLine p K m i j=0 from funext fun _=>if_neg h]; exact Knot.zero (G:=G) (b:=b) |>.price m i j
    unfold pickLine; rw [risesP,he.grows]
  · intro m i j q h; refine ht.ghost m i j q ?_; unfold pickLine at h; split at h; exact h; contradiction
  · intro m i j q; unfold pickLine; split; exact ht.real m i j q; exact (star_zero _).symm
  · intro m g; exact travels_line p (ht.color m g)
  · intro m i j q h; refine ht.even m i j q ?_; unfold pickLine at h; split at h; exact h; contradiction
  · intro m i j q; unfold pickLine; rw [ht.rev m i j q];
    by_cases he: K m j i q=0
    · rw [he]; split_ifs <;> ring
    have hh := ht.even m j i q he; rw [show parity i=parity j by grind]; split <;> simp
  intro m i j q; simp_rw [pulse_line,pickLine]; split; exact ht.falls m i j q; exact tendsto_const_nhds

def cursor (p : Bool) : LineRule G := ⟨ pickLine p (A0 G 0), pick_quality p (wick G)⟩

def bicolor (G : Gauge) : Palette G := ⟨ [cursor true,cursor false],
  by rw [ List.map_cons,List.map_cons,List.sum_cons,List.sum_cons ]; exact Eq.trans (calc
    _ = pickLine false (A0 G 0)+pickLine true _ := by unfold cursor; dsimp; abel) (halves _)⟩

theorem line_smul (K : Rip G) (x : ℂ) : pickLine p (x•K)= x•pickLine p K:= by
  funext m i j q; unfold pickLine; split <;> simp [*]

theorem pick_zero (G : Gauge) : pickLine p (0: Rip G)=0:= by funext m i j q; unfold pickLine; split <;> rfl

theorem selected_deriv (i j : Cfield G n) (q : SectorP n) (r : ℝ) : HasDerivAt (fun s => pickLine p (halfP G s) n i j q)
      (pickLine p (radial G r) n i j q) r := by
  unfold pickLine; split; exact shell_deriv ..; exact hasDerivAt_const ..

theorem continuous_half (i j : Cfield G n) (q : SectorP n) : Continuous fun t=> pickLine p (radial G t) n i j q := by
  unfold pickLine; split; exact continuous_radial ..; exact continuous_const

private theorem diff_pick (w : Legs (Shore G m)) (F H : Mob G) (r : ℝ) :
    HasDerivAt (fun v => bridgeG (pickLine p (halfP G v)) F H m w) (bridgeG (pickLine p (radial G r)) F H m w) r := by
  have he (w : Legs (Shore G m)) (L : ℝ → Shared (Shore G m) ℂ) {L' : Shared (Shore G m) ℂ}
      (h : ∀ i j, HasDerivAt (fun x => L x i j) (L' i j) r) :
      HasDerivAt (fun x=> scatter (field parity) w (L x)) (scatter (field parity) w L') r := by
    induction w generalizing L L' with
    | nil => exact h [] []
    | cons i w ih => simp only [scatter_cons]; exact ih _ (fun l s => (h (i::l) s).add ((h ..).const_mul _))
  apply he; intro l s
  exact HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
    ((((selected_deriv p i j _ r).const_mul (2 : ℂ)).mul_const _).mul_const _)

theorem continuous_pick (w : Legs (Shore G m)) (F H : Mob G) : Continuous fun t =>
    bridgeG (pickLine p (radial G t)) F H m w := by
  have he (w : Legs (Shore G m)) (L : ℝ → Shared (Shore G m) ℂ) (h : ∀ i j, Continuous (fun x => L x i j)) :
      Continuous (fun x=> scatter (field parity) w (L x)) := by
    induction w generalizing L with
    | nil => exact h [] []
    | cons i w ih => simp only [scatter_cons]; exact ih _ (fun l s => (h (i::l) s).add (continuous_const.mul (h l (i::s))))
  apply he; intro l s
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (((continuous_const.mul (continuous_half p i j (-net l))).mul continuous_const).mul continuous_const)

theorem integrated_pick (b : Bool) (w : Legs (Shore G m)) (F H : Mob G) (s a : ℝ) :
    let c : ℂ := factor b
    (∫ t in a..s, c * bridgeG (pickLine p (A0 G t)) F H m w) =
      ∫ r in (exp a)..(exp s), c * bridgeG (pickLine p (radial G r)) F H m w := by
  intro c
  simp_rw [radial_log, line_smul, bridgeG_smul,Pi.smul_apply,smul_eq_mul]; rw [intervalIntegral.integral_congr
    (g:=fun t : ℝ => exp t • (c * bridgeG (pickLine p (radial G (exp t))) F H m w))
    (fun i _ => by simp only [Complex.real_smul]; rw [mul_left_comm])]
  exact intervalIntegral.integral_deriv_smul_comp (fun t _ => Real.hasDerivAt_exp t)
    continuous_exp.continuousOn (continuous_const.mul (continuous_pick p w F H))

theorem aux_pick (b : Bool) (w : Legs (Shore G m)) (F H : Mob G) (s : ℝ)
    (hp : IntegrableOn (fun t => (factor b : ℂ) * bridgeG (pickLine p (A0 G t)) F H m w) (Set.Iic s)) :
    (∫ t in Set.Iic s, (factor b : ℂ) * bridgeG (pickLine p (A0 G t)) F H m w) =
      (∫ t in (0:ℝ)..exp s, (factor b : ℂ)* bridgeG (pickLine p (radial G t)) F H m w) := by
  let c : ℂ := factor b
  let A (t:ℝ) := c* bridgeG (pickLine p (A0 G t)) F H m w
  let B (t:ℝ) := c* bridgeG (pickLine p (radial G t)) F H m w
  have hC : Continuous B := continuous_const.mul (continuous_pick p w F H)
  let X (a:ℝ) := ∫ t in (0:ℝ)..a, B t
  have hX : X 0=0:= intervalIntegral.integral_same
  have he : ∀ᶠ a:ℝ in atBot, (∫ t in Iic s,A t) - ∫ t in Iic a,A t = X (exp s)-X (exp a) := by
    filter_upwards [eventually_le_atBot s] with a ha
    rw [intervalIntegral.integral_Iic_sub_Iic (hp.mono_set (Iic_subset_Iic.mpr ha)) hp]
    rw [integrated_pick p b w F H s a]
    linear_combination
      intervalIntegral.integral_add_adjacent_intervals (a:=0) (b:= exp a) (c:=exp s)
        (μ:=MeasureTheory.volume) (hC.intervalIntegrable _ _) (hC.intervalIntegrable _ _)
  have ht : Tendsto (fun a => (∫ t in Iic s,A t) - ∫ t in Iic a,A t) atBot (𝓝 (∫ t in Iic s,A t)) := by
    simpa only [sub_zero,id_eq] using (tendsto_integral_Iic_zero (f:=A) (μ:=MeasureTheory.volume) tendsto_id).const_sub
      (∫ t in Iic s,A t)
  have hT : Tendsto (fun a => X (exp a)) atBot (𝓝 0) := by
    rw [← hX]
    exact (( intervalIntegral.continuous_primitive (μ:=MeasureTheory.volume) (fun a b => (hC.intervalIntegrable ..)) _).continuousAt.tendsto).comp tendsto_exp_atBot
  refine tendsto_nhds_unique_of_eventuallyEq ?_ ?_ he
  · exact ht
  simpa only [sub_zero] using hT.const_sub (X (exp s))

theorem selected_radial (A : LocalVertex G true 4) (B : LocalVertex G b h) (s : ℝ) :
    let R := firstSymbol A B (cursor p)
    let c : ℂ := factor b
    plow (-(h:ℂ)) s R = (fun m w => ∫ t in (0:ℝ)..exp s, c* bridgeG (pickLine p (radial G t)) A.symbol B.symbol m w) ∧
      plow (-(h:ℂ)) s R = c • bridgeG (pickLine p (halfP G (exp s))) A.symbol B.symbol := by
  intro R c
  obtain ⟨hx,hp,hV⟩ := first_integral A B (cursor p) s
  dsimp only [cursor] at hx hp
  simp_rw [pulse_line, pA] at hx hp
  have H : plow (-(h:ℂ)) s R = (fun m w => ∫ t in (0:ℝ)..exp s, c* bridgeG (pickLine p (radial G t)) A.symbol B.symbol m w):= by
    unfold R cursor; rw [hx]; funext m w; exact aux_pick p b w _ _ _ (hp m w)
  refine ⟨H,?_⟩
  rw [H]; funext m w
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun i _=> (diff_pick p w A.symbol B.symbol i).const_mul c)
    ((continuous_const.mul (continuous_pick p w A.symbol B.symbol)).intervalIntegrable _ _)]
  have hZ : bridgeG (pickLine p (halfP G 0)) A.symbol B.symbol = 0 := by
    rw [show halfP G 0=0 from funext (fun n=>halfP_nil G n),pick_zero,← zero_smul ℂ (0 : Rip G),
      bridgeG_smul,zero_smul]
  rw [hZ]; simp

end YM.MS.ScaleForest
