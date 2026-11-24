import YM.RG12.Arche.Illuminate
/-!
# Lamp overshoot still within first Gram pricing precision.

Leading tests can be at FIXED shape: no numeric interpolation of the actual correlation at
coincident points. The error against free incurs only another constant on the same (NOT
summable over dyadic UV steps) rate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Arche
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Marker Source Extra.Histories
open Extraction Bid Push Next.Extract Dash Cells Next.Rank Next.Rank.Tapes PhysicalNext.RankCovariance
   PhysicalNext.InteractingRank PhysicalNext.InteractingRank.Soft Next.Rank.Price Precision
open Org Spec PhysicalNext.Repeat.Legato.Bandage
open Next.Rank Tapes.West Perch Atlas Station Cells Edition Glyph Rise Alarm Paint Vac.Numbers
open Next.Rank.East Further.CorrectedLift
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
open MergeProof Analysis Next.UVStress Climb Ward MergeProof.East
variable {G:Gauge}{C:Family G}{ϕ : Filter UVIndex}{l:Filter UVIndex}[l.NeBot] {M:∀ d, ℕ→RepChart C d}
  {d e n D k N p m:ℕ}
  {ι:Type}[Fintype ι] {W:Bid.Worth}{u ψ β δ:ℕ→ℝ}{r:ℕ→ℕ} {L:∀ N p m:ℕ,m<N→MergeProof.GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (P:ι → Tapes.Panel D) (B:Binding C)(H:C.Makes)(h:G.Simple)(hp:Scrim C W u ψ β δ (fly C.path.levels) r L) (O:HaarBudget G)(J:ChartRatio G)
local notation "A" => C.path.levels
local notation "F!"=> standard C
variable (z:ℝ) (hZ : ∀ i≤D,MergeProof.Accent.generator G i≤ z) (index:ι)
set_option quotPrecheck false
local notation "a!"=> (P index).arc
local notation "κ" k:max=> C.S.a k
variable {S : Table C.book} {f: Extraction.Order}(F:Final C f S)(hQ:Observing C H ϕ M)(hb:ϕ ≤ f.fuse)
variable (ax:Axis) (i₀ N₀:ℕ) (hN:0<N₀)(hi:0 < i₀)(hn:2≤n)
open Shapes YM.RG12.Desk.Paired Extra.FD

private lemma local_leading (x₁ x₂:E4)(h:x₁≠x₂)(v:(F!).Field d)(w:(F!).Field e) {s:ℝ}(hs:0<s): ContDiffAt ℝ 1 (fun k:ℝ=> paired (F!) d e (k • couple x₁ x₂) v w) s:=by
   let t:= ![(⟨d,v⟩:(F!).Tag),⟨e,w⟩]
   simp_rw [pair_at]
   have hg:= Next.UVStress.smoothDisc (Maxwell.table_smooth C.labels) t
   have hl: s • couple x₁ x₂∈ conf _:=by
      intro i j he; apply couple_ok h
      have he':s • (couple x₁ x₂ i)=s • (couple x₁ x₂ j):=he
      exact (smul_right_injective _ hs.ne') he'
   have hc := hg.contDiffAt ((conf_open _).mem_nhds hl)
   exact (hc.comp (f:=fun k:ℝ=> k • couple x₁ x₂) _ (by fun_prop)).of_le (by simp)

-- reciprocal of magnification meets budget
private lemma enough {b:ℝ}(h:6 ≤ b)(D : Levels G)(k n:ℕ) : (mag D b k)⁻¹≤ Ship.budget D n k:=by
  let m:=D.clock.monitor k; have hm: 1 ≤ m:= Real.one_le_exp (sq_nonneg _); have hP:=zero_lt_one.trans_le hm
  unfold mag Ship.budget Ship.pot; rw [Real.rpow_def_of_pos (show 0 < m from hP), ←Real.exp_neg,Real.exp_le_exp];change -(Real.log m*b) ≤ -(Real.log m/(16*↑n))
  have hp:= Real.log_nonneg hm
  by_cases hi:n=0
  · subst n; norm_num; nlinarith
  have hv:1≤(n:ℝ):= Nat.one_le_cast.mpr (Nat.pos_of_ne_zero hi)
  nlinarith [div_le_self hp (show 1 ≤16*(n:ℝ) by linarith)]

private lemma fixed_length {v:E4} {w:E4}(hx:v≠w)(i₀:C.label d)(i₁:C.label e) {s b:ℝ} (h:G.Simple)(hs:0<s)(hb:6≤b)(N n:ℕ)(hN:0<N): ∃ c:ℝ,0≤ c ∧ ∀ᶠ k:ℕ in atTop,
    let P(t:ℝ) := freePair C ((Shapes.ratio N (mag A b k)*s*t) • couple v w) i₀ i₁
    let Q:=freePair C (s • couple v w) i₀ i₁
    ‖P 1-Q‖ ≤ c*Ship.budget A n k:=by
    let P(t:ℝ):=freePair C (t • couple v w) i₀ i₁
    obtain ⟨K,T,hT,hK⟩:= (local_leading v w hx ((F!).project d i₀) ((F!).project e i₁) hs).exists_lipschitzOnWith
    have hL:LipschitzOnWith K P T:= by
        intro a ha u hu
        specialize hK ha hu
        have hf (t): P t=paired (F!) d e (t • couple v w) ((F!).project d i₀) ((F!).project e i₁):=(pair_at (F!) (_ • couple v w) _ _).symm
        rw [hf,hf]; exact hK
    let μ(k):=mag A b k; let u(k):= Shapes.ratio N (μ k)-1
    have hp(k):0 < μ k:=mag_pos ..
    have hz (k):=ticketed N (μ k) (hp k) hN
    have hu:Tendsto (fun k=> N*(μ k)⁻¹: ℕ→ℝ) atTop (𝓝 0):= by simpa using (tendsto_inv_atTop_zero.comp (mag_rate A h (b:=b) (by linarith))).const_mul (N:ℝ)
    have he:Tendsto u atTop (𝓝 0):=squeeze_zero (fun k=> sub_nonneg.mpr (hz k).1) (fun k=>
     (sub_le_iff_le_add').2 ((hz k).2.trans_eq (by rw [div_eq_mul_inv]))) hu
    have ht:Tendsto (fun k=>Shapes.ratio N (μ k)*s) atTop (𝓝 s):=by simpa [u] using (he.add_const 1).mul_const s
    have HH:0≤ (K:ℝ):=NNReal.coe_nonneg _
    refine ⟨K*N*s,by positivity,?_⟩
    filter_upwards [ht hT] with k hk
    intro r q; unfold r q; rw [mul_one]
    have Hs:= hL.dist_le_mul _ hk _ (mem_of_mem_nhds hT)
    rw [dist_eq_norm,Real.dist_eq,abs_of_nonneg (show 0≤Shapes.ratio N (μ k)*s-s from sub_nonneg.mpr (le_mul_of_one_le_left hs.le (hz k).1))] at Hs
    apply Hs.trans
    have hQ:= enough hb (A) k n
    have hZ:Shapes.ratio N (μ k)≤1+(N:ℝ)*Ship.budget (A) n k:= (hz k).2.trans (by rw [div_eq_mul_inv]; gcongr)
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hZ hs.le) HH]

private def proto (C:Family G)(d e:ℕ)(x y:E4)(s:ℝ) : C.label d →ₗ[ℂ] (C.label e→ₗ[ℂ] ℂ) :=
    spread (standard C) (s • couple x y) ((standard C).project d) ((standard C).project e)
private lemma out (C:Family G)(i:C.label d)(j:C.label e)(x y:E4)(s:ℝ) : proto C d e x y s i j=freePair C (s • couple x y) i j:=pair_at _ _ ((standard C).project d i) ((standard C).project e j)
private lemma mass_length {v w:E4}(hx:v≠w)(d e:ℕ) {s b:ℝ} (h:G.Simple)(hs:0<s)(hb:6≤b)(N n:ℕ)(hN:0<N): ∃ c:ℝ,0≤ c ∧ ∀ᶠ k:ℕ in atTop, ∀ (i:C.label d)(j:C.label e),
    let P(t:ℝ) := freePair C ((Shapes.ratio N (mag A b k)*s*t) • couple v w) i j
    let Q:=freePair C (s • couple v w) i j
    ‖P 1-Q‖ ≤ c*Ship.budget A n k*mass C d i * mass C e j:=by
    let I(i):=(C.labels.level i).Index
    let D{i : ℕ}(j:I i):C.label i:=Pi.single j 1
    choose c hc he using fun i j=> fixed_length hx (D i:C.label d) (D j:C.label e) h hs hb N n hN
    let a i:=∑ j,c i j; let K:=∑ i,a i
    have ha i:0≤a i:=sum_nonneg fun j _=>hc i j
    refine ⟨K,sum_nonneg (fun i _=>ha _),?_⟩
    filter_upwards [eventually_all.mpr (fun i=>eventually_all.mpr (he i))] with k hk i j p q
    let t:= Shapes.ratio N (mag A b k)*s
    let L:= proto C d e v w t - proto C d e v w s
    have hX(i:C.label d)(j:C.label e): L i j= freePair C (t • couple v w) i j-freePair C (s • couple v w) i j:=by unfold L; simp only [LinearMap.sub_apply,out]
    unfold p q; rw [mul_one,← hX]; apply mass_two
    intro i j; rw [hX]; change ‖freePair _ _ (D i) (D j)-freePair _ _ (D i) (D j)‖ ≤ _
    specialize hk i j; dsimp only at hk; rw [mul_one] at hk; exact hk.trans (mul_le_mul_of_nonneg_right
       ((show c i j ≤ a i from single_le_sum (fun j _=>hc i j) (mem_univ j)).trans (single_le_sum (fun i _=>ha i) (mem_univ i))) (Ship.budget_pos ..).le)

-- yes reflected. uniform in both vectors and horizons
private lemma rung {b:ℝ}(H:G.Simple)(L:6≤b)(hn:0 < i₀) (hN:0<N₀)(n:ℕ): ∃ c:ℝ,0≤ c ∧∀ᶠ k in atTop,∀ (i:C.label d)(j:C.label e),
    let s:= Shapes.ratio N₀ (mag A b k)*i₀;let Q:=fun t=> polished C.labels d e ax (N₀:ℝ)⁻¹ t ((F!).project _ i) ((F!).project _ j)
    ‖Q s-Q i₀‖ ≤ c*Ship.budget A n k*mass C d i *mass C e j:=by
   let v:= basis ax;let w:= Ortho.move (Signed.reflect ax) (other ax (N₀:ℝ)⁻¹)
   have hv: v≠ w:=fun hh=> by
      have he:= congr_arg (fun a:E4=>a ax) hh
      have hq: v ax=1 := by simp [v]
      change v ax=w ax at he
      simp [hq, w, other] at he; linarith
   obtain ⟨c,hc,hT⟩:= mass_length (C:=C) hv d e H (s:=i₀) (by positivity) L N₀ n hN
   let M:= C.book.adj e ax
   have hZ:∃ B:ℝ,0≤ B∧∀ j:C.label e,mass _ _ (M j) ≤ B*mass _ _ j:= mass_adj C e ax -- private from another file make public
   obtain ⟨D,hD,hY⟩:=hZ
   refine ⟨c*D,mul_nonneg hc hD,?_⟩
   filter_upwards [hT] with k hk i j s q
   have he (a:ℝ) : q a=freePair C (a • couple v w) i (M j):=by
       unfold q polished;rw [pair_at,Shapes.scaling]; have h':(F!).adj (Extra.FD.table_spin _) e ax ((F!).project e j)=(F!).project e (M j):=rfl
       rw [h']; unfold freePair; refine congr_arg _ ?_; congr 1; unfold bearing compass YM.RG12.Desk.Paired.arrangement; rw [one_smul,one_smul]; rfl
   rw [he,he]
   have ht:= hk i (M j); dsimp only at ht; rw [mul_one] at ht
   exact ht.trans ((mul_le_mul_of_nonneg_left (hY j) (mul_nonneg (mul_nonneg hc (Ship.budget_pos ..).le) (mass_nonneg ..))).trans_eq (by ring))

include F H h hp hZ hQ hb hi hN hn
lemma fixed_shapes :∃ c:ℝ,0 ≤ c ∧ ∀ᶠ k in atTop,∀ T: ℕ→ℕ→TableL C D,Poised P B H O J n z k T→
      ∀ (Z:∀ i:Fin (D+1),Module.End ℂ (C.label i)), let μ:= mag A a! k
      Comparer (ϕ:=ϕ) (hC:=H) l k D T μ Z→∀ (j i:Fin (D+1))(v:C.label j)(w:C.label i), let t:= lamp C N₀ k μ
      ‖illumination _ F.room.kernel.spin j i ax N₀ (t*i₀) (glowH M k (Z j) v) (glowH M k (Z i) w)-
        polished C.labels j i ax (N₀:ℝ)⁻¹ i₀ ((F!).project j v) ((F!).project i w)‖ ≤ c* Ship.budget A n k*mass C j v*mass C i w:=by
  obtain ⟨c,hc,hK⟩:= surface (l:=l) P B H h hp O J z hZ index F hQ hb ax i₀ N₀ hN hi hn
  have he : 6 ≤ a!:=by have h:= (P index).huge; linarith [Nat.cast_nonneg (α:=ℝ) D]
  choose v hv hx using fun d e:Fin (D+1)=> (rung (N₀:=N₀) (i₀:=i₀) (C:=C) (d:=d) (e:=e) ax h he hi hN n) -- variable params
  let w i:=∑j,v i j; let W:=∑ i,w i
  have hw i:0≤ w i:=sum_nonneg fun _ _=>hv ..
  refine ⟨c+W,add_nonneg hc (sum_nonneg fun _ _=>hw _),?_⟩
  filter_upwards [hK,eventually_all.mpr (fun i=> eventually_all.mpr (hx i))] with k hk Hk T hT Z μ hΨ j i x y t
  apply (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add (hk T hT Z hΨ j i x y) (Hk j i x y)).trans ?_)
  rw [add_mul,add_mul,add_mul]; gcongr
  · exact mass_nonneg C _ _
  · exact mass_nonneg C _ _
  · exact (Ship.budget_pos ..).le
  · exact le_trans (show v j i≤ w j from single_le_sum (fun i _=>hv _ i) (mem_univ _)) (single_le_sum (fun i _=>hw i) (mem_univ _))
end YM.RG12.Arche
