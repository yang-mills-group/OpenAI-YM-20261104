import YM.FormalBulk08.Spigot.Slope
/-! Finances of field, address and path measures in kme.
All preimages for a test profile kept. Root is movable by translation,
here fixed at origin. ∥w∥ Euclidean native norm. Card axis fixed.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spigot
open Function Filter Lattice RG Laurent Bloch Exterior Wilson
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North Cork City Wine Flat Glide Bank Chapel Rift Kemp Dawn MeasureTheory
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I:Type*}{G:Gauge}{n:Side}{r t u e E D:ℕ}{A B C σ η:ℝ}

abbrev Halo (D:ℕ) := Brush D→Measure Pier
def record (μ ν:Halo D)(p:Studio D):=∑ i, ((∫ t,p.val i t ∂(μ i)) - ∫ t,p.val i t ∂(ν i))
def district (μ ν:Halo D):=∑ i, ((μ i).real Set.univ+(ν i).real Set.univ)
def Fleet (μ:Halo D):Prop:= ∀ i,IsFiniteMeasure (μ i)
def rush (u:ℕ)(σ:ℝ)(v:ℝ):= (1+v)^u * Real.exp (σ*v)
lemma rush_paid (u:ℕ)(σ:ℝ){v:ℝ}(h:0≤v): 0≤rush u σ v:=mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le
lemma rush_more (u:ℕ){x y:ℝ}(h:0≤x)(hs:0≤σ)(hp:x≤y): rush u σ x≤rush u σ y := by
       unfold rush; have hh : 0≤ (1+y)^u:= by have hb:0≤y:=h.trans hp; positivity
       refine mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) _) (Real.exp_monotone ?_) (Real.exp_pos _).le hh; exact mul_le_mul_of_nonneg_left hp hs
lemma rush_hi (u:ℕ){x:ℝ}(h:0≤x): Real.exp (σ*x) ≤ rush u σ x:= le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ (by linarith))

def stub (μ:Halo D)(u:ℕ)(n:ℝ)(σ:ℝ)(i:Brush D):= ∫ t:Pier, rush u σ (n+‖t.val‖) ∂(μ i)
lemma district_pos (μ ν: Halo D):0≤district μ ν:= Finset.sum_nonneg fun i _=>by positivity
lemma stub_price {μ:Halo D}(u:ℕ)(h:0≤A)(_hp:Fleet μ)(i:Brush D):0≤stub μ u A σ i:= by
    apply integral_nonneg; intro t; exact rush_paid u σ (add_nonneg h (norm_nonneg t.val))
lemma stub_low {μ:Halo D}(u:ℕ)(h:0≤A)(hs:0≤σ)(hp:Fleet μ)(i:Brush D):Real.exp (σ*A) * (μ i).real Set.univ ≤ stub μ u A σ i := by
    have hh:=hp i; let f (t:Pier):= rush u σ (A+‖t.val‖)
    have hf : Continuous f:= by unfold f rush; fun_prop
    have he : Integrable f (μ i):= hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    have hw:= integral_mono (integrable_const (Real.exp (σ*A))) he fun x=> (rush_hi u h).trans (rush_more u h hs (show A≤A+‖(x:Pier).val‖ by simp)); simpa only [f,stub,integral_const, smul_eq_mul, mul_comm ((μ i).real _)] using hw
lemma stub_high {μ:Halo D}(u:ℕ)(h:0≤A)(hs:0≤σ)(hp:Fleet μ)(i:Brush D): stub μ u A σ i ≤ rush u σ (A+8)*(μ i).real Set.univ:= by
    have hh:=hp i
    have he t: 0≤ A+‖(t:Pier).val‖:=add_nonneg h (norm_nonneg _)
    rw [← abs_of_nonneg (stub_price u h hp i),←Real.norm_eq_abs]; unfold stub
    exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun p=> by rw [Real.norm_eq_abs, abs_of_nonneg (rush_paid u σ (he p))]; exact rush_more u (he _) hs (by linarith only [still p]))
lemma record_prices {μ ν:Halo D}(h:Fleet μ)(hp:Fleet ν)(p:Studio D):‖record μ ν p‖≤district μ ν*‖p‖:= by
    unfold record district; rw [Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=>?_)); rw [add_mul]; have hk:=h i; have hz:=hp i
    rw [mul_comm _ ‖p‖, mul_comm ((ν i).real _)]; exact (norm_sub_le ..).trans (add_le_add (norm_integral_le_of_norm_le_const (Eventually.of_forall fun x : Pier=> le_panel p i x)) (norm_integral_le_of_norm_le_const (Eventually.of_forall fun x : Pier=> le_panel p i x)))

def burse (u:ℕ)(n σ:ℝ)(μ ν:Halo D):= ∑ i,(stub μ u n σ i + stub ν u n σ i)
lemma burse_below (u:ℕ){μ ν:Halo D}(h:0≤A)(H:Fleet μ)(P:Fleet ν):0≤burse u A σ μ ν:= Finset.sum_nonneg (fun i _=> add_nonneg (stub_price u h H i) (stub_price u h P i))
lemma burse_hot (u:ℕ){μ ν:Halo D}(h:0≤A)(hs:0≤σ)(H:Fleet μ)(P:Fleet ν): burse u A σ μ ν≤ rush u σ (A+8)*district μ ν:= by
    unfold district burse; rw [Finset.mul_sum]; simp_rw [mul_add (rush u σ _)]; exact Finset.sum_le_sum (fun i _=> add_le_add (stub_high u h hs H i) (stub_high u h hs P i))
lemma burse_cold (u:ℕ){μ ν:Halo D}(h:0≤A)(hs:0≤σ)(H:Fleet μ)(P:Fleet ν): Real.exp (σ*A)*district μ ν≤ burse u A σ μ ν:= by
    unfold district burse; rw [Finset.mul_sum]; simp_rw [mul_add (Real.exp _)]; exact Finset.sum_le_sum (fun i _=> add_le_add (stub_low u h hs H i) (stub_low u h hs P i))

structure Kme (μ ν:chain (Biglot I) r→Halo D)(u:ℕ)(σ C:ℝ)(f:Studio D→Tile (Biglot I) r):Prop where
    plus:∀ x,Fleet (μ x)
    minus:∀ x,Fleet (ν x)
    earn: SumBudget (fun x=>burse u (acres x) σ (μ x) (ν x)) C
    code : ∀ p x,f p x=record (μ x) (ν x) p
variable {μ ν:chain (Biglot I) r→Halo D}{f:Studio D→Tile (Biglot I) r}
lemma billing (h:Kme μ ν u σ C f)(x:I)(hs:0≤σ)(p:Studio D): Knoxville (fame _) (σ/2) (0,x) (f p) (C*‖p‖):= by
    refine actual_penn (sum_tier ⟨fun i=>mul_nonneg (h.earn.1 i) (norm_nonneg _), h.earn.2.1.mul_right ‖p‖,le_trans (Eq.le (tsum_mul_right ..)) (mul_le_mul_of_nonneg_right h.earn.2.2 (norm_nonneg p))⟩ (fun i=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (fun i=>?_))
    rw [h.code]; apply le_trans (mul_le_mul ((Real.exp_monotone (?_))) (record_prices (h.plus _) (h.minus _) p) (norm_nonneg _) (Real.exp_pos (σ*acres i)).le); swap
    · have hp : (herb (fame _) (0,x) i:ℝ)≤2*acres i:= by exact_mod_cast barn_small i x
      nlinarith
    rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (burse_cold _ (Nat.cast_nonneg _) hs (h.plus _) (h.minus _)) (norm_nonneg _)
-- upper exp accounting covers polynomial u arbitrarily. Width contraction estimate remains in smoother first norm.
open Planned.PrimaryIntegral295.Carrier
lemma rush_power (o:I)(u:ℕ)(h:0<σ):∃ (η C:ℝ),0<η∧0≤C∧ ∀ x:chain (Biglot I) r,
    rush u η ((acres x:ℝ)+8) ≤ C * Real.exp (σ * herb (fame _) (0,o) x):= by
    let R:ℝ:=r+1;have hr : 0 < R:=by unfold R; positivity
    let s:=σ/2/R;have ht : 0<s:=by unfold s; positivity
    let M:=widthCost s u
    have hM:0≤ M := zero_le_one.trans (widthCost_ge ht u); refine ⟨s,M*Real.exp (16*s),ht,mul_nonneg hM (Real.exp_pos _).le,fun x=>?_⟩
    have he:0≤ (acres x:ℝ)+8:= by positivity
    unfold rush; apply (mul_le_mul_of_nonneg_right (widthBill s ht u _ he) (Real.exp_pos _).le).trans; rw [mul_assoc M,mul_assoc M,←Real.exp_add,←Real.exp_add]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) hM
    have hx : (acres x:ℝ) ≤ R*herb (fame _) (0,o) x:= by unfold R; exact_mod_cast acres_barn x o
    have hz : s*R=σ/2:= div_mul_cancel₀ _ hr.ne'; nlinarith
lemma explain_Kme [Fintype I] (o:I)(u:ℕ)(h:0<σ): ∃ η K:ℝ,0<η∧0≤K∧ ∀ (f:Studio D→ₗ[ℝ]Tile (Biglot I) r) (A:ℝ),0≤A→ (∀ p, Knoxville (fame _) σ (0,o) (f p) (A*‖p‖)) → ∃ μ ν,Kme μ ν u η (K*A) f:= by
   obtain ⟨η,C,hE,hC,H⟩:= rush_power (r:=r) o u (half_pos h)
   obtain ⟨K,hK,he⟩:=cut_barn (r:=r) o (show σ/2<σ by linarith)
   let T:ℝ:=Fintype.card (Brush D);have hT:0≤T:=Nat.cast_nonneg _; refine ⟨η,C*K*T,hE,mul_nonneg (mul_nonneg hC hK) hT, fun f A hA hF=>?_⟩
   let G x:= (LinearMap.proj x) ∘ₗ f; let z (x:chain (Biglot I) r):= σ*herb (fame _) (0,o) x; let W (x:chain (Biglot I) r):= A/ Real.exp (z x); choose μ ν hμ hν hp ht using fun i=>address_account (W i) (show 0 ≤ W i from div_nonneg hA (Real.exp_pos _).le) (G i) (fun p=> show ‖f p i‖≤ W i*‖p‖ from (le_trans ((le_div_iff₀ (Real.exp_pos _)).mpr (penn_chill i (hF p))) (by unfold W; ring_nf;rfl)))
   let v:= fun i=> district (μ i) (ν i); let g i:= burse u (acres i) η (μ i) (ν i)
   have hh := he v (T*A) (mul_nonneg hT hA) (fun i=> district_pos ..) fun i=> (hp i).trans_eq (by
        change T*W i=T*A*Real.exp (-σ*herb (fame _) (0,o) i); rw [neg_mul, ← show z i=σ*herb _ _ _ from rfl,Real.exp_neg]; unfold W; ring)
   have hd i: g i ≤ C*(Real.exp (σ/2*herb (fame _) (0,o) i)*v i):= (burse_hot u (by positivity : 0≤(acres i:ℝ)) hE.le (hμ _) (hν _)).trans ((mul_le_mul_of_nonneg_right (H i) (district_pos ..)).trans_eq (by rw [mul_assoc]))
   exact ⟨μ,ν,hμ,hν,sum_tier ⟨fun i=>mul_nonneg hC (hh.1 i), hh.2.1.mul_left C,by rw [tsum_mul_left]; exact (mul_le_mul_of_nonneg_left hh.2.2 hC).trans_eq (by rw [mul_assoc C, mul_assoc, mul_assoc])⟩ (fun i=>burse_below u (Nat.cast_nonneg _) (hμ i) (hν i)) hd,fun p i=> ht i p⟩
end YM.FormalBulk08.Spigot
