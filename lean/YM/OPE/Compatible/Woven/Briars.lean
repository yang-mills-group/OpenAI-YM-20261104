import YM.OPE.Compatible.Woven.Vessel
/-!
# Budget driven from one flight. Use full weight. Aggregate cancellation at both root and volume.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Flume
open Function Lattice Laurent Filter MeasureTheory RG Finset Tree Next.Free Bloch Exterior Precision Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Carrier Planned.PrimaryIntegral295.Trellis
open scoped Topology BigOperators Classical
variable {r j m n:ℕ}{L:Side}{η B:ℝ}
def shrill (r m:ℕ)(σ b:ℝ):=(2+8*r:ℝ)^m*(widthCost σ m*b)^r
-- directly both near/far estimates through arbitrary ℉ with derivatives. Survey. 
variable {X:Lines L}
local notation "Y"=> (fun _ : Fin r=>X)
lemma budget_direction (x:Bin r) (a b: Fin r→Axis)(c : Fin r→Cover)(l: List (Keys r)) (hh:l.length ≤ j) (hm:size x ≤ L.val)(hc:∀ i:Fin r,size (c i) ≤ 4*L.val)(hv:0<η) (hb:0≤B)(h:horn η B j X)(ho:Odd L.val)(m:ℕ):
   Sack (poise m) (dvol l (parcelK Y a b c) x) (shrill r m η B/(L.val:ℝ)^r/(L.val:ℝ)^l.length):=by
   have he:= parcel_rescue a b c j m l (fun i=>h) hh ho hv x
   have hp: 0 ≤ widthCost η m:= zero_le_one.trans (widthCost_ge hv m)
   have hr:0 < (L.val:ℝ):=by positivity
   have hY: poise m (parcelY c L x)≤ (2+8*r:ℝ)^m:=by
       unfold poise; apply pow_le_pow_left₀ (by positivity); unfold notch; push_cast
       have he:= (div_le_one hr).2 (show (size x:ℝ)≤ (L.val:ℝ) by exact_mod_cast hm); linarith only [he, heft (L:=L) c hc x]
   apply he.tips; apply (mul_le_mul_of_nonneg_right hY (?_)).trans_eq ?_
   · positivity
   unfold shrill; rw [pow_add]; ring
lemma budget_long (x:Bin r) (a b: Fin r→Axis)(c : Fin r→Cover)(hx:L.val<size x)(hc:∀ i:Fin r,size (c i) ≤ 4*L.val)(hv:0<η) (hb:0≤B)(h:horn η B j X)(ho:Odd L.val) (m:ℕ): Sack (poise m) (parcelK Y a b c x) (((size x:ℝ)/L.val)^m*(shrill r m η B/(L.val:ℝ)^r)):=by
   let p:= (parcelY c L x); have he:= parcel_rescue a b c j m [] (fun i=>h) (by simp) ho hv x
   apply he.tips
   have hr:0 < (L.val:ℝ):=by positivity
   let v:= ((size x:ℝ)/L.val);have hw:1≤v:= (one_le_div hr).2 (by exact_mod_cast hx.le)
   have hh: (notch p:ℝ) ≤ v*(2+8*r:ℝ):=by unfold notch p;push_cast; linarith only [hw,mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg (α:=ℝ) r), heft c hc x]
   have hg:0 ≤ widthCost η m:= zero_le_one.trans (widthCost_ge hv m)
   simp only [List.length_nil, Nat.add_zero]; apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hh m) ?_).trans_eq ?_
   · positivity
   unfold shrill; rw [mul_pow]; unfold v; ring
lemma hornsAt (x:ℝ)(hx:0<x)(hj:4≤j){u:ℕ}(ht:4≤u)(hn:n≤j-2): ∃ B:ℝ,0 ≤ B ∧ ∀ (P:Flight j u) (a b: Fin r→ Axis)(c:Fin r→Cover), (∀ i:Fin r,size (c i) ≤ 4*P.L.val) → Survey (Bin r) (parcelK (fun _=>linesOf P x) a b c) P.L.val n m (B/(P.L.val:ℝ)^r) (poise m):=by
    obtain ⟨η,B,he,hB,h⟩:= horns x hx j u hj ht; have hx:0 ≤ widthCost η m:= zero_le_one.trans (widthCost_ge he m)
    refine ⟨shrill r m η B,by unfold shrill; positivity,fun P a b c hc=> ⟨fun x hx=> budget_long x a b c hx hc he hB.le (h P) P.odd m,fun l hl x hx=>budget_direction x a b c l (hl.trans hn) hx hc he hB.le (h P) P.odd m⟩⟩
lemma parcel_budget0 (m:ℕ)(x:Bin r)(a b:Fin r→Axis)(c:Fin r→Cover)(hc:∀ i:Fin r,size (c i) ≤ 4*L.val)(hv:0<η)(hb:0≤B)(h:horn η B j X)(ho:Odd L.val):
   Sack (poise m) (parcelK Y a b c x) (poise m x*(shrill r m η B/(L.val:ℝ)^r)):=by
   have he:0 < (L.val:ℝ):=by positivity
   have hx :0 ≤ shrill r m η B:=by
       unfold shrill; have hp:=widthCost_ge hv m; have hz:= zero_le_one.trans hp; positivity -- indent
   have hy := div_nonneg hx (pow_nonneg he.le r)
   by_cases h':L.val<size x
   · apply (budget_long x a b c h' hc hv hb h ho m).tips
     apply mul_le_mul_of_nonneg_right _ hy; apply pow_le_pow_left₀ (by positivity); apply le_trans (b:=(size x:ℝ)); exact div_le_self (by positivity) (by exact_mod_cast L.property); unfold notch; push_cast; linarith
   have ht:= budget_direction x a b c [] (by simp) (Nat.le_of_not_gt h') hc hv hb h ho m
   rw [List.length_nil,pow_zero,div_one] at ht; exact ht.tips (le_mul_of_one_le_left hy (poise_one m x))
end YM.OPE.Flume
