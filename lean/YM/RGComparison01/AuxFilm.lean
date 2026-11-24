import YM.RGComparison01.AuxInsert

/-! # Envelopes in constructed auxiliary chart units. -/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison01.AuxFabric
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Lattice Wilson RG Pressure PhysicalNext.Repeat Push.AbsoluteSums
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Work.G05
open AuxJets AuxCurtain AuxStage WilsonStartup Tensor AuxConstant Matrix
open ConnectedActivityE6.Coat Sienna Lantern
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local notation "Y" => Poll.Body ι
variable {Q : Matrix ι ι ℝ} {W f : Poll.Body ι → ℝ×E → ℝ}
    {p w j n i k q q' : ℕ} {U A K D a b v : ℝ}
-- grade zero normalization of unmarked integral
lemma intent_unit (H: Probe W k p 0 (a*b) D K K) (hf : Probe f k j (q+1) (a*b) D v v) (hp : n+(0+q*n)<k) (hz : ∀ z:Y,W z 0=1) : intent Q W f 1 q 0 n 0=fun _=>1:= by
  ext x; unfold intent; simp_rw [Finset.sum_apply]; rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.zero_lt_succ n))]
  · simp only [mul_zero,pow_zero,mul_one,zero_add,Pi.smul_apply]
    have ht : point_co Real.exp 0=1:= (Tensor.coeff_apply_zero Real.exp 0 (fun _=>1)).trans Real.exp_zero
    rw [ht,one_smul]
    unfold readsH ritual; rw [Nat.zero_add, Tensor.diagonal, Tensor.coeff_apply_zero]
    unfold AuxConstant.mean; rw [Nat.zero_add,Finset.sum_range_one]; unfold Tensor.diagonal
    let T (z:Y) := Tensor.coeff (W z) 0 0; let L:= ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0=>ℝ × E) ℝ (fun _=>0)
    have he : (∫ z, L (T z) ∂Poll.sweep Q)=1:= by
      rw [show (fun z=>L (T z))=(fun _=>1) from funext fun z=> (Tensor.coeff_apply_zero (W z) 0 (fun _=> 0)).trans (hz z)]; simp
    rw [L.integral_comp_comm] at he; exact he
    let u:=T 0; have h : T=fun _=> u:= by
      funext z; ext1 x; unfold u T; rw [Tensor.coeff_apply_zero,Tensor.coeff_apply_zero,hz,hz]
    change Integrable T _; rw [h]; exact integrable_const _
  intro i hi h; simp only [Pi.smul_apply]
  have ht:= H.crew hf (g:=1) Probe.unit hp (Nat.le_of_lt_succ (Finset.mem_range.mp hi)); simp only [reads_null ht (show 0+(0+q*i)<_ by omega),Pi.zero_apply, smul_zero]

variable {G : Gauge} {L : Side} {C u v d F W : ℝ→ℝ} {g : ℝ}
lemma each_fee (hp : Geo G L u) (he : Geo G L v) (h : Geo G L W) : Geo G L (fun t=> each i k (W t) (u t) (v t)) := by unfold each; exact ((((h.times he).times (Geo.fixed _)).times ((hp.times (Geo.fixed _)).power i)).times (Geo.fixed _))
lemma aid_geo (hp : Geo G L u) (he : Geo G L v) (h : Geo G L W) (hh : Geo G L d) (c:ℝ) (n k q q' : ℕ): Geo G L (fun t=> aid c (u t) (v t) (d t) (W t) n k q q') := by
  have hf:=(((hp.times (hh.power (q+1))).joins (Geo.fixed 2)).power (n+1)); unfold aid
  exact ((((h.times (he.times (hh.power q'))).times (Geo.fixed _)).times (((Geo.fixed _).times ((Geo.fixed _).times hf)).times (Geo.fixed _))).times (Geo.fixed _))
lemma fare_geo (hp : Geo G L u) (he : Geo G L v) (h : Geo G L W) (hh : Geo G L d) (c:ℝ) (n k q q' : ℕ): Geo G L (fun t=> fare c (u t) (v t) (d t) (W t) n k q q') := by
  unfold fare; apply (aid_geo hp he h hh c n k q q').joins; refine Geo.expel _ (fun (i:ℕ) t=>_) ?_; intro i hi
  let u(i:ℕ):= q'+q*i; have ht:= each_fee (k:=k) (i:=i) hp he h; let m:= u i+n+1; have hf:=hh.power m
  exact (Geo.fixed _).times ((((Geo.fixed _).times (ht.joins ht)).times hf).joins ((ht.times hf).joins ((Geo.fixed _).times ht)))
-- policy fixed stage
variable (n k j w q q' : ℕ)
lemma within_core (hp : Geo G L C) (hw : Bolt G L W) (he : Geo G L u) (hf : Geo G L v) (hh : Geo G L d) (hD : 0<D) (hA : 0 < A)
    (hk : n+(q'+q*n)<k) (hn : 1 ≤ n) : ∃ Q:ℝ→ℝ,Geo G L Q∧ ∀ᶠ t in atTop, let z:= betaF G t L; let r:= D*Delay.fineMonitor G L t; let s:= eaves G L t
      ∀ (β:ℝ), z/2 ≤ β → β ≤ 2*z → 1 < d t →
       let b:=gStep β; let m:=d t*b
       ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (ι: Type) [Fintype ι] [DecidableEq ι]
       (ϕ ψ:E×Poll.Body ι→ℝ) (ρ:E→Poll.Body ι) (M:E→Matrix ι ι ℝ) (V f : Poll.Body ι→ℝ×E→ℝ), (Fintype.card ι:ℝ) ≤ W t → Golf ϕ ψ ρ M k r s s (C t) →
       (∀ z:ι→ℝ, dotProduct z ((M 0)⁻¹*ᵥ z)≤A*dotProduct z z) →
       Probe V k j (q+1) m r (u t) (u t)→Probe f k w q' m r (v t) (v t)→
       ∀ x:E, ‖x‖ < m → AuxStage.Points (Q t) m⁻¹ b n k
         (fun x:E=> intake ((M 0)⁻¹) (numeric b (AuxGrace.nodes ϕ ψ ρ M) f V q q' Real.exp) r (b,x)) x
          (intent ((M 0)⁻¹) (AuxGrace.nodes ϕ ψ ρ M) V f q q' n) := by
  obtain ⟨p,hp0,hO⟩:= Brush.compact (f:=Real.exp) (k:=k) (s:=Icc (-1) 1) isCompact_Icc (fun y _=> Real.contDiff_exp.contDiffAt)
  have hs : ∀ y∈ball (0:ℝ) 1, Brush k p 1 Real.exp y:= fun y hy=> hO y (abs_le.mp (mem_ball_zero_iff.mp hy).le)
  let D' x:= wick G L D x; let B t:= Lantern.clump k (Lantern.fee k (C t) (D' t)) p
  have ht := Geo.fee k hp ((Geo.fixed D).times Geo.by_delay); let N:=n+(q'+q*n)+1
  let φ:ℝ:=-((N:ℝ)/2+1); have hr:= Geo.advance (G:=G) (L:=L) N
  have h := AuxGaussian.walls G L hw hA hD φ (AuxGrace.zgrade k+w+j*n)
  have hV := ((ht.rate).mul (Sienna.edge G L)).below (by linarith only [Sienna.vow_ok]) _ zero_lt_one
  have hK : Geo G L (fun t=> bite (u t) (d t) q):= (he.times (hh.power _)).joins (Geo.fixed _)
  have hZ:= (Sienna.contraction G L (a:=1) zero_lt_one ((hh.rate).mul (Sienna.glim G L)) (show 0+ -(1/2:ℝ) < Sienna.vow by norm_num [Sienna.vow])); simp only [one_mul] at hZ
  refine ⟨_, fare_geo he hf (Geo.rot k ht (Geo.fixed p)) hh p n k q q',?_⟩
  filter_upwards [Geo.wiggle (G:=G) (L:=L) D hD,hK.uniform zero_lt_one,Delay.shift_pos G L,hZ,h,hV,hr] with t ht0 hz hX hZ hg hε hB z r s β hβ hx hP b m E _ _ _ ι _ _ ϕ ψ ρ M V f hW hk' hA' hv hq x hD'
  have hh:= Sienna.lamp G L hX β hβ; have he' : 0<β:=(half_pos hX).trans_le hβ
  have hi : m ≤ s:= le_trans (mul_le_mul_of_nonneg_left hh.2 (zero_le_one.trans hP.le)) hZ.le
  have hj:= AuxGrace.shrink hk' hk'.off le_rfl (mul_pos (zero_lt_one.trans hP) hh.1) hi (mul_pos (zero_lt_one.trans hP) hh.1) hi (le_refl k)
  have hY: Probe (AuxGrace.nodes ϕ ψ ρ M) k (AuxGrace.zgrade k) 0 m r (B t) (B t):= shape hj hO (by
    have ht:= (AuxGrace.buds hj ht0 (hO 0 (by norm_num)) 0).nonneg
    have ht': 0≤Lantern.fee k (C t) r:= (Lantern.compel _ (z:=0) (x:=((0,0):ℝ×E)) hj (by rw [norm_zero]; exact hj.pos) (by rw [norm_zero]; exact hj.pos') (by rw [norm_zero]; exact hj.off)).nonneg
    exact (mul_le_mul_of_nonneg_left hi ht').trans ((le_abs_self _).trans hε)) (by omega) ht0
  have hy : bite (u t) (d t) q * b ≤ 1:= (mul_le_mul_of_nonneg_right (le_abs_self _) hh.1.le).trans (hz β hβ).le
  have hp' := (hk'.gram 0 (by rw [norm_zero]; exact hk'.pos)).1.inv
  exact proceeds hY hv hq hk hn hh.1 hP (hi.trans hk'.small) (fun y h=> hs y (ball_subset_ball hy h)) hy ((M 0)⁻¹) hD' hp' hA' hk'.off ((hg ι _ hW hp' hA').trans (hB β he' hx))
end YM.RGComparison01.AuxFabric
