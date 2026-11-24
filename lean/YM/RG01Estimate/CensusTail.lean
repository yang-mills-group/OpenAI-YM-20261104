import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Wing
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Census.Coffer

/-!
# High component-census, seed overlap, and long-support tail, at arbitrary order

Use the SAME eligibility/footprints and the full left-derivative `p.supBounds`; not a
bound only at a globally trivial vacuum germ. No Taylor assumption on any of the factors.
This is a useful alternative to rescaling these tails inside the exponential. The remaining
local integrals are still nontrivial: see `seed_free` and PROGRESS. In particular NOT *all*
exceptions in a Taylor comparison have been discarded here (cost still needed for WarningAt,
profile or Gaussian replacements, etc.).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.VacuumCensus

open Function Filter Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Control Window Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Shoot Precision SectorMeasure Oriented Reserves
open PhysicalNext PhysicalNext.Repeat Height
open Next.Scheduling
open ConnectedActivityE6.Blaze Blaze.March Captain Silica
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f : Side} {S : StepData c f} {L : Side} {P : Teller G} {T : Tube G S}
    {Q : YM.ConnectedActivityE6.Target G P} {W : ℝ} {o : ConnectedActivityE6.Target.Order G W}
    {R : RG.Rep G f} {μ q C' d v Y A b r B s α a δ e i : ℝ} {k j n ℓ : ℕ} {χ : Chi}
    {H : Cash W s μ L Q o α T R}

/-- Predicate on a single log component. Cut the depth in E6 shape price (cover number and
costs including paths), not just the apparent cardinality. Enlarging by a fixed order factor
lets one pay here at every order with the same aperture on the paid schedule. -/
def tail (H : Cash W s μ L Q o α T R) (p : ℕ) (z : H.fragrances) :=
    p ≤ Height.degree H z ∨ 1 ≤ Height.overlap H z ∨
      (p:ℝ) * Pressure.Stores.till s ≤ Height.depth H z

lemma beacon_charge {p : ℕ} (hd : 1 ≤ grow G L s) (he : grow G L s^p ≤ Real.exp (Q.mark L μ s))
    (hu : grow G L s^3 ≤ Real.exp (Q.ε*Pressure.Stores.till s))
    {z : H.fragrances} (hz : tail H p z) : grow G L s^p ≤ beacon H z := by
  let g := grow G L s
  have hg : 0 < g := zero_lt_one.trans_le hd
  have hε := Q.usable
  have hm : 0 ≤ Q.mark L μ s:= H.laws.acquired.marked
  have ht : 1 ≤ Real.exp (Q.mark L μ s*Height.overlap H z) := Real.one_le_exp (mul_nonneg hm (Nat.cast_nonneg _))
  have hv : 1 ≤ Real.exp (Q.ε*Height.depth H z) := Real.one_le_exp (mul_nonneg hε.le
    (sum_nonneg fun i _=> H.positive_volume _))
  rcases hz with h|h|h
  · let x:=g^Height.degree H z
    have h' : 0 ≤ x := pow_nonneg hg.le _
    exact (pow_le_pow_right₀ hd h).trans ((le_mul_of_one_le_right h' ht).trans
      (le_mul_of_one_le_right (mul_nonneg h' (zero_le_one.trans ht)) hv))
  · exact he.trans ((Real.exp_monotone (le_mul_of_one_le_right hm
      (show (1:ℝ) ≤ Height.overlap H z by exact_mod_cast h))).trans
      ((le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ hd)).trans
        (le_mul_of_one_le_right (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd) ht |>.trans' zero_le_one) hv)))
  calc
    _ ≤ (Real.exp (Q.ε*Pressure.Stores.till s)) ^ p := pow_le_pow_left₀ hg.le
      ((le_self_pow₀ hd (show 3 ≠ 0 by decide)).trans hu) _
    _ ≤ Real.exp (Q.ε*Height.depth H z) := by
      rw [← Real.exp_nat_mul]; apply Real.exp_monotone
      rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left h hε.le
    _ ≤ _ := le_mul_of_one_le_left (Real.exp_pos _).le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hd) ht)

variable (N : Captain H j C' d v Y A b r B q k χ)

/-- An absolute hit budget with the beacon STILL in the weight. This is an arbitrary-grade
cut estimate after dropping the matching part of the beacon. `n` pays any fixed derivative
spatial power requested subsequently. -/
theorem weighted (ht : Armada Q L μ a s i B j k) (hd : 1 ≤ grow G L s) (hh' : Heavy N.conduit)
    (hs : degreePrice (radiusB s) (grow G L s*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (hp : degreePrice (radiusB s) (grow G L s*salary Q L μ B s j k) i ≤ 1/2) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=> beacon H z * N.markΦ z n) a
        (collars G i s j n*(grow G L s*salary Q L μ B s j k*(1-1/2)⁻¹)) := by
  intro x
  have hy:= log_hit_tail _ _ _ H.testS (stable N hd hh' i a ht.delta ht.little ht.earned hs hp)
    (add_nonneg ht.gain ht.delta.le) 0 x
  simp only [pow_zero,mul_one] at hy
  let v:= collars G i s j n
  have he:0 ≤ shiftG s:=by unfold shiftG; positivity
  have hv:0 ≤ v:=by unfold v collars Reserves.polyPrice; have he' := ht.delta; positivity
  have hz z : 0 ≤ N.markΦ z n:= mul_nonneg (pow_nonneg (by positivity) _) (N.pvc _)
  have hθ z : 0 ≤ beacon H z := mul_nonneg
    (mul_nonneg (pow_nonneg (zero_le_one.trans hd) _) (Real.exp_pos _).le) (Real.exp_pos _).le
  have hh:= budget_scale hv hy
  refine budget_mono hh (fun z=> ?_) fun z=> ?_
  · dsimp only; split
    next => exact mul_nonneg (mul_nonneg (hθ z) (hz z)) (Real.exp_pos _).le
    exact le_rfl
  dsimp only; split
  next hx=>
    rw [if_pos (show 0 ≤ z.fst ∧ x∈unionOf H.smallAt z.snd from ⟨Nat.zero_le _,hx⟩), Height.wield N]
    let K:= reachability (H:=H) z
    let c:ℝ:=coverNumber (radiusB s) K
    let m:=beacon H z
    have hg:0 ≤ c:= Nat.cast_nonneg _
    change m * ((shiftG s*(1+c))^(n*j)*N.design z) * Real.exp (a*c) ≤ v*(m*N.design z*Real.exp ((a+i)*c))
    calc
      _ ≤ m*((shiftG s^(n*j)*(Reserves.polyPrice i (n*j)*Real.exp (i*c)))*N.design z) * Real.exp (a*c) := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (polynomial_cost ht.delta hg _)
            (by positivity)) (N.pvc _)) (hθ _)) (Real.exp_pos _).le
      _ = _ := by rw [add_mul a i c, Real.exp_add]; unfold v collars; ring
  exact hh.1 z

lemma charge_predicate (Z : H.fragrances → Prop) (ρ : ℝ)
    (ht : Armada Q L μ a s i B j k) (hd : 1 ≤ grow G L s) (hh' : Heavy N.conduit)
    (hs : degreePrice (radiusB s) (grow G L s*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (hp : degreePrice (radiusB s) (grow G L s*salary Q L μ B s j k) i ≤ 1/2)
    (hr : 0 < ρ) (he : ∀ z, Z z → ρ ≤ beacon H z) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=>if Z z then N.markΦ z n else 0) a
        (ρ⁻¹*(collars G i s j n*(grow G L s*salary Q L μ B s j k*(1-1/2)⁻¹))) := by
  intro x
  have ht:= budget_scale (inv_pos.mpr hr).le (weighted N (n:=n) ht hd hh' hs hp x)
  have hv:0 ≤ shiftG s:=by unfold shiftG; positivity
  have hy z:0 ≤ N.markΦ z n := mul_nonneg (pow_nonneg (by positivity) _) (N.pvc _)
  refine budget_mono ht (fun z=> ?_) fun z=> ?_
  · dsimp only; split
    next =>
      apply mul_nonneg _ (Real.exp_pos _).le
      split
      next => exact hy _
      next => rfl
    exact le_rfl
  dsimp only; split
  next hx =>
    by_cases hh: Z z
    · rw [if_pos hh]
      apply le_trans _ (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (he z hh) (hy z)) (Real.exp_pos _).le)
        (inv_pos.mpr hr).le)
      rw [mul_assoc ρ, inv_mul_cancel_left₀ hr.ne']
    rw [if_neg hh,zero_mul]; simpa only [hx,if_true] using ht.1 z
  simp

lemma charged (ht : Armada Q L μ a s i B j k) (hd : 1 ≤ grow G L s) (hh' : Heavy N.conduit)
    (hs : degreePrice (radiusB s) (grow G L s*(Q.costs L μ 1 s 0).rootHit) Q.δ ≤ 1/2)
    (hp : degreePrice (radiusB s) (grow G L s*salary Q L μ B s j k) i ≤ 1/2) (p : ℕ)
    (he : grow G L s ^ p ≤ Real.exp (Q.mark L μ s))
    (hu : grow G L s ^ 3 ≤ Real.exp (Q.ε*Pressure.Stores.till s)) :
    Ac.Hit (Captain.reachability (H:=H)) (radiusB s) (fun z=> if tail H p z then N.markΦ z n else 0) a
        ((grow G L s^p)⁻¹*(collars G i s j n*(grow G L s*salary Q L μ B s j k*(1-1/2)⁻¹))) :=
  charge_predicate N _ _ ht hd hh' hs hp (pow_pos (zero_lt_one.trans_le hd) _)
    (fun _ hh => beacon_charge hd he hu hh)

-- Classification of the residual *problem* after tail removal.
lemma seed_free {p : ℕ} (z : H.fragrances) (V : Config G c) (h : stream H χ V z ≠ 0)
    (hz : ¬ tail H p z) :
    Height.depth H z < (p:ℝ)*Pressure.Stores.till s ∧ Height.degree H z < p ∧
    z.fst+1 < p ∧ ∀ j,
      Ac.Spark H.supportP (z.2 j).val ∧ troupe T R Q.halo (radiusB s) (z.2 j).val ∧
        (z.2 j).val.card < p ∧ (z.2 j).val.toLeft = ∅ ∧ own (z.2 j).val = ∅ := by
  have hi : Height.depth H z < (p:ℝ)*Pressure.Stores.till s := lt_of_not_ge (fun h=> hz (Or.inr (Or.inr h)))
  have hp : Height.degree H z < p := lt_of_not_ge (fun h=> hz (Or.inl h))
  have hr : Height.breadth H z < p := lt_of_le_of_lt (Nat.le_add_left ..) hp
  have hh i : leaflet H χ V (z.2 i) ≠ 0:= fun he=> h (by unfold stream Gas.term; rw [prod_eq_zero (Finset.mem_univ i) he,mul_zero,zero_div])
  have hv i : Ac.Spark H.supportP (z.2 i).val ∧ troupe T R Q.halo (radiusB s) (z.2 i).val := by
    by_contra h; apply hh i; unfold leaflet likely; simp_rw [Height.vacuity V (z.2 i) h,sum_const_zero,mul_zero]
  have hb : z.fst+1 ≤ Height.breadth H z := by
    refine le_trans ?_ (Finset.sum_le_sum (s:=univ) (fun i _ => Finset.card_pos.mpr (hv i|>.1.1): ∀ i∈univ, 1≤(z.2 i).val.card))
    simp
  refine ⟨hi,hp,lt_of_le_of_lt hb hr,fun j=>?_⟩
  let q := z.2 j
  have ha : q.val.toLeft = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun ⟨i,hj⟩=> by
    have hx : 1 ≤ i.shares:= by rw [← Packets.seeds_card]; exact Finset.card_pos.mpr ((hv j).2.1.checkpoints i hj).1
    have he : 1 ≤ Cash.numP q.val := hx.trans (Finset.single_le_sum (f:=Mixed.shares S) (fun _ _=> Nat.zero_le _) (mem_toLeft.mp hj))
    exact hz (Or.inr (Or.inl (he.trans (single_le_sum (f:=fun i=> Cash.numP (z.2 i).val) (fun _ _=> Nat.zero_le _) (mem_univ j)))))
  refine ⟨(hv j).1,(hv j).2,lt_of_le_of_lt (Finset.single_le_sum (f:=fun i=> (z.2 i).val.card)
    (fun _ _=> Nat.zero_le _) (mem_univ j)) hr, ha, Finset.not_nonempty_iff_eq_empty.mp ?_⟩
  rintro ⟨i,hj⟩; obtain ⟨x,hx⟩:= (R.activities.forced i).inventory_ne
  obtain ⟨x,hx,hw⟩:= (hv j).2.2.2 _ hj _ hx
  unfold roster Packets.store at hx; rw [ha] at hx; simp at hx

end YM.RG01Estimate.VacuumCensus
