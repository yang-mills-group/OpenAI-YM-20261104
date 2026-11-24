import YM.OPE.Coverage.Pairs

/-!
## Non-singularity estimate by the joint smeared silver family

Even on shelves selected near an arbitrary spacing sequence up to length
log-powers (if this finite demand includes sufficient aperture & depth).
The family is independent of the spacing. This does not yet price the
fixed-field inverse at polynomial costs: one still needs control of the
actual correlations on BOTH slots to bound that change of frame.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Coverage
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb RG Next.UVStress Spec Levy MeterTest
open Maxwell Push.FiniteDetection.Free
open scoped ContDiff Topology BigOperators Classical ComplexOrder
variable {G:Gauge} {C:Family G}{F:Order}{S:Table C.book}
set_option quotPrecheck false
local notation "mCb" => Bel C.book
local notation "Q" => (mCb).Field
variable (H:Final C F S){d D n:ℕ}{R:ℝ} {r:ℕ→ℝ} (p:Shelf H r D n R)
variable (hn:2 ≤ n) (hd:d ≤ D)(ha:∀ t∈silver C d,tsupport t ⊆ Scaling.window R 2)
local notation "Ul" => p.maps
local notation "Pyth" => Q d -- nested notation might misparse

abbrev live {r D n R}(p:Shelf H r D n R) (t:Test 2) (i:ℕ):S.Field d →ₗ[ℂ] S.Field d →ₗ[ℂ]ℂ :=credits S H.room.kernel.smooth d (p.path i) (p.window.1 i) t

def payPair(t:Test 2)(i:ℕ) : Pyth →ₗ[ℂ] (Pyth) →ₗ[ℂ] ℂ:=
    let u:=p.maps i d
    (LinearMap.llcomp ℂ (Pyth) (S.Field d) ℂ |>.flip u).comp ((live H p t i).comp u)

lemma paySlot_eq (t:Test 2)(i:ℕ)(x y:Pyth):payPair H p t i x y= t.applyTo (Next.UVStress.tested (p.path i) (p.maps i) (blit (mCb) d x y)) :=by
    let g:=Ul i d; change scene S d (p.path i) t (g x) (g y) =_
    unfold scene pointwise Next.UVStress.tested
    have he : blit S d (g x) (g y)= Next.UVStress.panels (p.maps i) ∘ (blit (mCb) d x y):=by
         funext j; fin_cases j <;> rfl
    rw [he]

include hn hd ha
lemma panel_cap (t:Test 2)(ht:t∈silver C d)(x y:Pyth): Tendsto (fun i=> payPair H p t i x y) atTop (𝓝 (minted C d t x y)):=by
   simp only [mint_exact,paySlot_eq]
   exact p.smears 2 hn (blit (mCb) d x y) (fun i=>by fin_cases i <;> exact hd) _ (ha t ht)

lemma dominates: ∃ B:ℝ,1 ≤ B ∧ ∀ᶠ i in atTop,∀ (x:Pyth), ‖x‖=1 → ∃ t∈silver C d,1 ≤ B * ‖payPair H p t i x (Levy.reflect d x)‖ := by
   by_contra! he -- witness bad subsequence
   have hz(i:ℕ):∃ u:ℕ,i≤u ∧ ∃ x:Pyth, ‖x‖=1 ∧ ∀ t∈silver C d,(i+1:ℝ)*‖payPair H p t u x (Levy.reflect d x)‖ < 1 := frequently_atTop.mp (he (i+1:ℝ) (by linarith only [Nat.cast_nonneg (α:=ℝ) i])) i
   choose u hu x hr hX using hz
   have hu:Tendsto u atTop atTop:= tendsto_atTop_mono (f:=id) hu tendsto_id
   obtain ⟨y,hy,f,hf,hW⟩ := (isCompact_sphere (0:Pyth) 1).tendsto_subseq fun k=> mem_sphere_zero_iff_norm.mpr (hr k)
   obtain ⟨t,ht,h₀⟩:= (silver_tests C d).choose_spec y (mem_sphere_zero_iff_norm.mp hy)
   let z:ℂ:= grant C d t y
   have hv : Tendsto (fun k=> payPair H p t (u (f k)) (x (f k)) (Levy.reflect d (x (f k)))) atTop (𝓝 z) :=
      bilinear_collision (P:=payPair H (d:=d) p t ∘ u ∘ f) (minted C d t) (fun v w=>(panel_cap H p hn hd ha t ht v w).comp (hu.comp hf.tendsto_atTop)) hW (Levy.reflect_limit _ hW)
   have hz:Tendsto (fun k=> (f k:ℝ)+1) atTop atTop:= tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.comp hf.tendsto_atTop)
   have ho:= Filter.Eventually.of_forall (f:=atTop) (fun k=>(hX (f k) t ht).le)
   have hs : ‖z‖ ≤ (0:ℝ) := by
     apply le_of_tendsto_of_tendsto hv.norm (tendsto_const_nhds (x:=(1:ℝ)) |>.div_atTop hz) (ho.mono fun i hi=>?_) -- can use exact
     exact (le_div_iff₀ (by positivity : 0<(f i:ℝ)+1)).mpr (le_trans (mul_comm _ _).le hi)
   exact not_le_of_gt (norm_pos_iff.mpr h₀) hs

def replay (p:Shelf H r D n R)(i:ℕ)(d:ℕ)(x:Q d):ℝ:= ∑ t∈silver C d, ‖payPair H p t i x (Levy.reflect d x)‖ -- p binder shadows

lemma replay_bound (i:ℕ)(x:Pyth)(t:Test 2)(ht:t∈silver C d): ‖payPair H p t i x (Levy.reflect d x)‖ ≤ replay H p i d x:=by
     apply Finset.single_le_sum (f:=fun t=> ‖payPair H p t i x (Levy.reflect d x)‖) (fun t _=> norm_nonneg _) ‹t∈silver C d›
omit ha hn hd
lemma shifts (i d:ℕ)(x:Q d)(a:ℝ) : replay H p i d ((a:ℂ) • x) = a^2 * replay H p i d x :=by
     have he(v:Q d):Levy.reflect d ((a:ℂ) • v)= ((a:ℂ) • Levy.reflect d v):=by
         unfold Levy.reflect
         rw [LinearMap.map_smulₛₗ]; simp
     unfold replay; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t ht=>by
         rw [he, (payPair H p t i).map_smul, LinearMap.smul_apply,(payPair H p t i x).map_smul,norm_smul,norm_smul,Complex.norm_real]; rw [←mul_assoc]; simp [Real.norm_eq_abs,←pow_two,sq_abs]
include ha hn hd

/-- One common constant, no adjustment by the vector or after the placement. -/
lemma determinant: ∃ B:ℝ,1 ≤ B ∧ ∀ᶠ i in atTop,∀ x:Pyth,‖x‖^2 ≤ B * replay H p i d x :=by
    obtain ⟨B,hB,hv⟩:= dominates H p hn hd ha
    refine ⟨B,hB,?_⟩
    filter_upwards [hv] with i hi x
    rcases eq_or_ne x 0 with rfl|hx
    · simp [replay]
    let q:=‖x‖; have hq:0<q:=norm_pos_iff.mpr hx
    let a:=q⁻¹; have hp : a*q=1:= inv_mul_cancel₀ hq.ne'
    let y:= (a:ℂ) • x; have hz:‖(a:ℂ)‖ = q⁻¹:=Complex.norm_real _ |>.trans (Real.norm_of_nonneg (inv_pos.mpr hq).le)
    obtain ⟨t,ht,h₀⟩:=hi y (by unfold y;rw [norm_smul, hz,hp])
    have hf := h₀.trans (mul_le_mul_of_nonneg_left (replay_bound H p hn hd ha i y t ht) (zero_le_one.trans hB))
    rw [show replay H p i d y=a^2 * replay H p i d x from shifts ..] at hf
    have hq' : 0<‖x‖:=hq
    dsimp only [a,q] at hf; rw [inv_pow, inv_mul_eq_div, ← mul_div_assoc,le_div_iff₀ (by positivity)] at hf; linarith only [hf]
end YM.OPE.Coverage
