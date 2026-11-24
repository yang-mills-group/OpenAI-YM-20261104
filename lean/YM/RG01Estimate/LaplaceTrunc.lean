import YM.RG01Estimate.PolyGauss
/-!
# Integrate the measured b-jets and replace cut coefficients by full ones. Coupling grading
`b` real, normalized held probes; every fixed volume, small-torus receipts below for
uniformity. No analyticity hypothesis in complex b. The polynomial-log nature of these
prices is important, not just a scalar norm on a far integral. See also `priced_pole`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Laplace
open Function Filter Set Metric Finset MeasureTheory
open PhysicalNext.Repeat Lantern ConnectedActivityE6 Blaze Shield Brush RealTaylor Office Matrix
open scoped Topology ENNReal ContDiff BigOperators Classical Interval
variable {A E F : Type} [MeasurableSpace A] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
local notation "X" => ℝ×E
variable (f : A → ℝ × E → F) (s:Set A)(Z:Set E) (μ:Measure A)
variable {b t c C D R : ℝ} {k j m n : ℕ}
-- keep costs uniform for whole family.
def toric (x:X):= ∫ i, held f s x i ∂μ
def step (i:ℕ)(y:E):= ∫ z in s, piece (f z) i y ∂μ

def chart (k : ℕ) (t:ℝ) (y:E) := ∑ i∈Finset.range k, t^i • step f s μ i y
section finite
variable [IsProbabilityMeasure μ]
variable (p:Roll f s Z b C j) (hp:IsOpen Z) (hx : MeasurableSet s) (hv: 0 ≤ C)
local notation "Y" => corridor b Z
include p hv
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma internal (x:X) (he:x∈ Y) : Integrable (held f s x) μ:= by
  refine (integrable_const C).mono' (p.tested x he).aestronglyMeasurable (ae_of_all _ ?_)
  intro y; by_cases hy:y∈s
  · unfold held; rw [indicator_of_mem hy]; exact (p.occupied y hy x he).bound
  unfold held; rw [indicator_of_notMem hy,norm_zero]; exact hv
include hp
lemma price_area (x:X) (he:x∈ Y) : Brush j C 1 (toric f s μ) x:= by
   have hf (x:X) (ht:x∈Y) i : Brush j C 1 (fun x=> held f s x i) x:= by
      unfold held; by_cases h:i∈s
      · simp_rw [indicator_of_mem h]; exact p.occupied _ h _ ht
      simp_rw [indicator_of_notMem h]; exact (Brush.certified zero_le_one _).climb (by simpa) le_rfl
   have hX:∀ᶠ y in 𝓝 x, y∈ Y:= (isOpen_ball.prod hp).mem_nhds he
   have hQ := UVExt.EnergyRay.Thermal.Core.meristem_complex (f:=held f s) (μ:=μ)
       (hX.mono fun x hx=> p.tested x hx) ⟨fun _=> C,integrable_const _,hX.mono fun x hx=>hf _ hx⟩
   exact hQ.1.buds (fun _=> C) (integrable_const _) zero_le_one (by simp) (ae_of_all _ (hf _ he))
lemma page_charge (n:ℕ)(hn:n≤ j)(x:X)(hy:x∈Y) :
   Brush (j-n) C 1 (toric (fun i=> pages (f i) n) s μ) x ∧ Integrable (held (fun i=> pages (f i) n) s x) μ:= by
  have hc : Roll (fun i=> pages (f i) n) s Z b C (j-n):=(p.of_le le_rfl le_rfl (show j-n+n≤j by omega)).further hp
  exact ⟨price_area _ _ _ _ hc hp hv _ hy,internal _ _ _ _ hc hv _ hy⟩
include hx
lemma step_inside (y:E)(hy:y∈ Z)(hd : 0<b) (n:ℕ)(hn:n≤j) : Brush (j-n) C 1 (step f s μ n) y:= by
  have hf (y:E): step f s μ n y= toric (fun i=> pages (f i) n) s μ (0,y):= Eq.symm (integral_indicator hx)
  rw [funext hf]; let H:= toric (fun i=> pages (f i) n) s μ
  have ht:=page_charge f s Z μ p hp hv n hn (0,y) ⟨mem_ball_self hd,hy⟩
  -- Lantern.markArc requires real output use skim
  let L:= ContinuousLinearMap.inr ℝ ℝ E; have he x:(0,(0:E))+L x=(0,x):= by simp [L]
  have h:= Lantern.skim (P:=L) y ((he y) ▸ ht.1) n_hook; simpa only [he] using h

lemma renewal (y:E)(hY:(t,y)∈ Y)(k:ℕ)(hk:k≤j) :
      toric f s μ (t,y)= chart f s μ k t y+t^k • toric (fun i=> pages (f i) k) s μ (t,y) := by
    -- use function equality atpoint; no swapping differential identity
    let u n := held (fun i=> pages (f i) n) s
    let x : X:=(t,y)
    let w (n:ℕ) (z:A):= t^n • u n (0,y) z
    let q (z:A):= ∑ i∈ range k, w i z; let f' i:= held f s x i
    have hb : 0 < b:= (norm_nonneg _).trans_lt (mem_ball_zero_iff.mp hY.1)
    have hh (z:A): f' z = q z+t^k • u k x z:= by
       unfold f' u q held w; dsimp only [u] -- reduce z
       by_cases h:z∈ s
       · unfold held; simp only [indicator_of_mem h]
         exact priced (f z) Z b hp x hY k (fun i hx=> (p.occupied z h i hx).smaller (j:=j-k+k) (by omega)) -- arg j? 
       unfold held; simp [indicator_of_notMem h]
    have hu(n:ℕ)(hn:n≤j): Integrable (u n (0,y)) μ:= page_charge f s Z μ p hp hv n hn (0,y) ⟨mem_ball_self hb,hY.2⟩|>.2
    have hw i (hi:i∈ Finset.range k): Integrable (w i) μ:= ((hu _ ((Finset.mem_range.mp hi).le.trans hk)).smul _)
    change (∫ i,f' i ∂μ)=_
    simp_rw [hh]; rw [integral_add (show Integrable q μ from integrable_finsetSum _ hw) (show Integrable (fun i=> t^k • u k x i) μ from (page_charge f s Z μ p hp hv k hk x hY).2.smul _),integral_smul]
    apply congr_arg (fun v:F=> v+_) -- shadow F
    unfold chart q; rw [integral_finsetSum _ hw]; apply Finset.sum_congr rfl
    intro i hi; unfold w u; rw [integral_smul]; exact congr_arg (t^i • · ) (integral_indicator hx)
lemma peeled (y:E) (hY:(t,y)∈ Y)(k:ℕ)(hk:k≤j):
      Brush (j-k) (|t|^k*C) 1 (fun y=> toric f s μ (t,y) - chart f s μ k t y) y := by
   let H:= toric (fun i=> pages (f i) k) s μ; let L:=ContinuousLinearMap.inr ℝ ℝ E; have he x:(t,(0:E))+L x=(t,x):=by simp [L]
   have h:= Lantern.skim (P:=L) y ((he y) ▸ (page_charge f s Z μ p hp hv k hk _ hY).1) n_hook
   have h:=h.smul (t^k); rw [Real.norm_eq_abs,abs_pow] at h; refine h.shimmy ?_
   filter_upwards [hp.mem_nhds hY.2] with x hx'
   change toric f s μ (t,x)- chart _ _ _ k t x=t^k • H _; rw [renewal f s Z μ p hp hx hv x (by exact ⟨hY.1,hx'⟩) k hk,add_sub_cancel_left,he]
end finite
section tail
variable {ι : Type} [Fintype ι][DecidableEq ι]
local notation "Y₀" => Poll.Body ι
variable (f : Poll.Body ι→ℝ×E→F) (s : Set (Poll.Body ι))(Q : Matrix ι ι ℝ)(p:Atlas f Z k j C)
local notation "m₁" => Poll.sweep Q
local notation "x" => RealTaylor.piece
local notation "weight" => fun i:Y₀=> (1+(‖i‖+1))^k
variable (hp:IsOpen Z) (hc:0≤C)
include p hc hp
lemma receives (y:E)(hy:y∈Z)(n:ℕ)(hn:n≤j)(hF:IntegrableOn (fun i:Y₀=> (1+(‖i‖+1))^k) s m₁):
      IntegrableOn (fun i=>x (f i) n y) s (Poll.sweep Q) ∧
      Brush (j-n) (C*(∫ i in s, weight i ∂Poll.sweep Q)) 1 (step f s (Poll.sweep Q) n) y:= by
   let g y' i := x (f i) n y'; let M i:= C*(weight i); let μ:= m₁
   have hI : Integrable M (μ.restrict s):= hF.const_mul _
   have hj:j-n+n≤j:= by omega
   have p' := p.of_le le_rfl hj le_rfl hc
   have hx : ∀ᶠ y in 𝓝 y, y∈ Z:= hp.mem_nhds hy
   have hz := UVExt.EnergyRay.Thermal.Core.meristem_complex (f:=g) (μ:=μ.restrict s)
       (hx.mono fun y hy=> p'.measured hp y hy) ⟨M,hI,hx.mono fun y hy i=>p'.cost hp i y hy⟩
   exact ⟨hz.2.self_of_nhds,hz.1.buds M hI zero_le_one (integral_const_mul ..).le (ae_of_all _ (fun i=>p'.cost hp i y hy))⟩

-- used for `chart` polynomial after cutting and reweighting
lemma add_charts {l:ℕ} (hv : l≤j) (y:E)(hy:y∈Z)(a:ℝ)(hs:MeasurableSet s)
     (hT:Integrable (fun i:Y₀ => (1+(‖i‖+1))^k) (Poll.sweep Q)) :
      chart f Set.univ m₁ l a y = chart f s m₁ l a y + chart f sᶜ m₁ l a y:= by
   unfold chart; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun i hi=>?_)
   rw [← smul_add]; unfold step
   rw [MeasureTheory.integral_add_compl hs (by
        apply integrableOn_univ.mp; exact (receives Z f Set.univ Q p hp hc y hy i ((mem_range.mp hi).le.trans hv) hT.integrableOn).1),setIntegral_univ]

lemma paid_chart (l:ℕ) (hv:l≤j) (y:E)(hy:y∈Z)(a:ℝ)(ha:‖a‖≤1)(hF:IntegrableOn (fun i:Y₀=> (1+(‖i‖+1))^k) s m₁ ): Brush (j-l)
    (l*(C*(∫ i in s,(1+(‖i‖+1))^k ∂m₁))) 1 (chart f s m₁ l a) y:= by
   let T:= C*(∫ i in s,(1+(‖i‖+1))^k ∂m₁)
   unfold chart; rw [show l*T= ∑ _i∈Finset.range l,T by simp]
   refine Brush.spree _ _ _ zero_le_one fun i hi=> ?_
   have hi' := Finset.mem_range.mp hi
   have hz:= (receives Z f s Q p hp hc y hy i (hi'.le.trans hv) hF).2.smaller (show j-l≤ j-i by omega)
   apply (hz.smul _).climb (mul_le_of_le_one_left hz.nonneg ?_) le_rfl
   rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha

lemma chart_defect (μR R S:ℝ) {t v:ℝ} (hl : Roll f s Z t D j) (hl' : n≤j) (ht:‖v‖≤ 1)
    (y:E) (hy:(v,y)∈ corridor t Z) (hs:MeasurableSet s)(hD:0≤ D)(he:(Fintype.card ι:ℝ)≤ S)(hS:1≤S)(h:Q.PosDef) (hm:∀ z:ι→ℝ, dotProduct z (Q*ᵥ z) ≤ μR * dotProduct z z)
    (hr: (∫ i in sᶜ, (1+(‖i‖+1))^k ∂Poll.sweep Q)≤R):
    Brush (j-n) (|v|^n*D+n*(C*R)) 1 (fun y=> toric f s m₁ (v,y)-chart f Set.univ m₁ n v y) y:= by
   have hT:= peeled f s Z m₁ hl hp hs hD y hy n hl'; let T:=PolyGauss.total hm h k S hS he
   have hx := paid_chart Z f sᶜ Q p hp hc n hl' y hy.2 v ht T.1.integrableOn
   apply (hT.separating (hx.climb (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr hc) (Nat.cast_nonneg _)) le_rfl)).shimmy
   filter_upwards [hp.mem_nhds hy.2] with z hz
   erw [add_charts Z f s Q p hp hc hl' z hz v hs T.1]; abel
end tail
end YM.RG01Estimate.Laplace
