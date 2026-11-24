import YM.WilsonCoeffUV.Vacuum.UV.LogAge
/-!
# Stipulated fixed-order uniform schedules

`Craft` barriers and positive widths independent of L; at most one fine
lookahead ALSO in smoothing predecessor of J (so in total three
smoothing indices). No dependencies here on values of kernels of generated
formal perturbations. Delay/floor hypotheses explicit about realised schedule.
Any parallel fixed-arity moment demands registered as *additional* post costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonCoeffUV.Bank
open Filter Function Matrix Lattice Wilson RG Laurent Bloch Exterior Metric Blue FreeResolvent Work.F08 Precision
open Gauge Power Next.Free Extension.UV.Linear PathCost
open scoped ContDiff Topology BigOperators
variable {G:Gauge}{n N M e m i k r b j l:ℕ}{U:Credit}

def oreD (G:Gauge)(r k:ℕ)(s:ℝ)(h:0<s):= (moon_bill G k r s h.le).choose
lemma ore_buy (G:Gauge)(r k:ℕ)(s:ℝ)(h:0<s): Amber terrain s (oreD G r k s h) (moon G k r):= (moon_bill G k r s h.le).choose_spec

def outerD (G:Gauge)(e r:ℕ) := (Satin.delta_full (show lowerGrade e r (e+1) (e+3) from Or.inl (by omega)) (G:=G)).choose
def outerF (e r:ℕ)(I: Gear G) := ((Satin.delta_full (show lowerGrade e r (e+1) (e+3) from Or.inl (by omega)) (G:=G)).choose_spec I).choose
lemma outer_price (I:Gear G)(R:Rally (e+1) (e+3) I) (r): PairA I.σ (outerF e r I* R.x^outerD G e r) R.σ (R.P.driftU e r) (R.Q.driftU e r):= ((Satin.delta_full (show lowerGrade e r (e+1) (e+3) from Or.inl (by omega)) (G:=G)).choose_spec I).choose_spec.2 R

structure Escrow {A: Levels G}{Ñ:ChartRatio G}{m:ℕ}(I:Usage A Ñ m) (e : ℕ) (c:ℝ): Prop where
   gain j: j≤e  →  I.gear.gain j / (A.S.block m).val ≤ Real.exp (-(PathCost.arc A.S m)/2)
   enough j: j≤e  →  I.gear.towing j
   capital : Real.sqrt (Dcost A.clock.kernel.penalty (A.clock.J m))≤c
   stowage k r: k≤e → r≤ e+2 → oreD G r k I.σ I.width ≤ c
   burst k r: k+1≤ e → r≤ e → carryF G k r I.gear≤ c
   boom k r:k≤ e →  r≤ e+2  →  outerF k r I.gear ≤ c
   height : ((A.S.block m).val:ℝ)≤c
   width_bill: I.σ⁻¹ ≤ c
   flash : ceilPoly 2 (I.σ/2)*sheetPay (I.σ/2)≤c
   freight : I.D ≤ c
-- additional demands for downstream moments also known after L. logger Ace.

-- All width choices (i,j at adjacent phases). step m, m+1, L.
variable {K:KernelChoices}{A:Levels G}
namespace Tokenizer
def outlet (T:Tokenizer K G i j):= T.s/2
lemma o_pos (T:Tokenizer K G i j):0<T.outlet:=by unfold outlet; linarith [T.sigma]
lemma o_lt (T:Tokenizer K G i j):T.outlet<T.s:=by unfold outlet; linarith [T.sigma]
-- `W.outlet` used adjoining
end Tokenizer
structure Craft (T:Tokenizer K G i j) (W:Tokenizer K G j l) (e L:ℕ) : Prop where
    tow i: i≤e  →  ((i+2:ℕ):ℝ)*T.s/L≤ W.outlet/2
    serve i: i≤e →  tauV G i T.preB T.s W.outlet T.outlet *ruby T.outlet T.sig / (L:ℝ) ≤ Real.exp (-Real.log L/2)
lemma Craft.demand (T:Tokenizer K G i j) (W:Tokenizer K G j l) (e:ℕ): ∀ᶠ L:ℕ in atTop, Craft T W e L:= by
    have hv i:∀ᶠ L:ℕ in atTop,((i+2:ℕ):ℝ)*T.s/L≤ W.outlet/2 := by
       have H : Tendsto (fun L:ℕ=> ((i+2:ℕ):ℝ)*T.s/L) atTop (𝓝 0):= tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
       exact H.eventually_le_const (by linarith [W.o_pos])
    have he (B:ℝ):∀ᶠ L:ℕ in atTop, (B/L) ≤ Real.exp (-Real.log L/2) := by
       have H: Tendsto (fun L:ℕ=>Real.exp (Real.log L/2)) atTop atTop := Real.tendsto_exp_atTop.comp (Tendsto.atTop_div_const (by norm_num) (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
       filter_upwards [H.eventually_ge_atTop B,eventually_gt_atTop 0] with L h hL; rw [div_le_iff₀ (by positivity)]
       refine h.trans_eq ?_; nth_rw 3 [← Real.exp_log (show 0<(L:ℝ) by positivity)]; rw [←Real.exp_add]; congr 1; ring
    let S:= Finset.range (e+1)
    filter_upwards [ (eventually_all_finset S).mpr (fun i hi=>hv i), (eventually_all_finset S).mpr (fun i hi=> he (tauV G i T.preB T.s W.outlet T.outlet * ruby T.outlet T.sig))] with L h ht
    exact ⟨fun i hi=> h _ (Finset.mem_range.mpr (by omega)),fun i hi=> ht _ (Finset.mem_range.mpr (by omega))⟩

def visits (Ñ:ChartRatio G)(T:Tokenizer A.clock.kernel G (A.clock.J m) (A.clock.J (m+1)))(W:Tokenizer A.clock.kernel G (A.clock.J (m+1)) (A.clock.J (m+2)))(h:Craft T W e (A.S.block m).val) : Usage A Ñ m := by
    have ht:= h.tow 0 (by omega)
    refine ⟨W.outlet,T.s,T.outlet,T.preB,T.sig,T.bid (loose A m),T.o_pos,T.o_lt,W.o_pos,T.bid_pos _, T.pre_nn,T.sig_nn,?_,T.port A m rfl rfl rfl⟩
    change T.s/(A.S.block m).val ≤ _; exact (slope₁ (r:=1) (L:=A.S.block m) T.sigma ht).trans (by linarith [W.o_pos])

lemma cooled (Ñ:ChartRatio G)(T:Tokenizer A.clock.kernel G (A.clock.J m) (A.clock.J (m+1)))(W:Tokenizer A.clock.kernel G (A.clock.J (m+1)) (A.clock.J (m+2)))(h:Craft T W e (A.S.block m).val) : ∀ᶠ c:ℝ in atTop, Escrow (visits Ñ T W h) e c := by
    let Z:= visits Ñ T W h
    let s:= Finset.range (e+1); let v:=Finset.range (e+3)
    have hh (K:ℕ → ℕ → ℝ): ∀ᶠ c:ℝ in atTop, ∀ i∈s,∀ j∈v,K i j≤ c:= (eventually_all_finset _).mpr (fun i _=> (eventually_all_finset _).mpr fun j _=>eventually_ge_atTop (K i j))
    filter_upwards [hh (fun i j=>oreD G j i Z.σ Z.width),hh (fun i j=>carryF G i j Z.gear),hh (fun i j=>outerF i j Z.gear),eventually_ge_atTop ((A.S.block m).val:ℝ),eventually_ge_atTop (Real.sqrt (Dcost A.clock.kernel.penalty (A.clock.J m))),eventually_ge_atTop Z.σ⁻¹,eventually_ge_atTop (ceilPoly 2 (Z.σ/2)*sheetPay (Z.σ/2)),eventually_ge_atTop Z.D] with c ha hb hc H f g t x
    refine ⟨fun i hi=>?_,fun i hi=>h.tow i hi,f,fun i j hi hj=> ha _ (Finset.mem_range.mpr (by omega)) _ (Finset.mem_range.mpr (by omega)),fun i j hi hj=>hb _ (Finset.mem_range.mpr (by omega)) _ (Finset.mem_range.mpr (by omega)),fun i j hi hj=>hc _ (Finset.mem_range.mpr (by omega)) _ (Finset.mem_range.mpr (by omega)),H,g,t,x⟩
    rw [arch]; exact h.serve i hi

structure Realm (G:Gauge)(e:ℕ)(T:Credit) where
   draws :Levels G
   paid : ChartRatio G
   hG: G.Simple
   green : LocalRatio paid
   anchor :ℕ
   y:ℕ → ℝ
   depth m:anchor≤m  → 1≤y m
   age m n:anchor≤m  → m≤n  →  y n≤ y m+(draws.S.scale n-draws.S.scale m)
   mint m: anchor≤m  →  Usage draws paid m
   crossing m (h:anchor ≤ m): (mint m h).past ≤ (mint (m+1) (by omega)).σ
   taxes m (h:anchor≤ m): Escrow (mint m h) e (T.buy (y m))
namespace Realm
variable (R:Realm G e U)
abbrev tempC (m b:ℕ):= trailC R.draws.S m b
abbrev cash (V:Credit)(m:ℕ):= V.buy (R.y m)
lemma changes (h:R.anchor≤m): R.y (m+1)≤(Credit.leanC.plus U).buy (R.y m) := by
   have he:= R.age m (m+1) h (by omega); rw [Schedule.scale_succ] at he
   have ht:= (R.taxes m h).height; have hh:= Real.log_le_sub_one_of_pos (x:=((R.draws.S.block m).val:ℝ)) (by positivity)
   have hf:= Credit.fuel Credit.leanC U (R.depth m h); rw [Credit.lean_cost] at hf; linarith
abbrev jump (U V:Credit):= V.usingC (Credit.leanC.plus U)
lemma shift_z (V:Credit)(h:R.anchor≤m): R.cash V (m+1)≤ R.cash (jump U V) m := by unfold cash jump; rw [Credit.stock_up]; exact Credit.elder V (R.depth _ (by omega)) (R.changes h)
abbrev dome (U:Credit):= U.finances 1 le_rfl
lemma won (h:R.anchor≤m)(p:m≤b): rag R.draws m b ≤ R.cash (dome U) m * R.tempC m b:=by
   have he: Real.sqrt (Dcost _ _) ≤ R.cash U b:= (R.taxes b (by omega)).capital
   rw [rag,Real.sqrt_mul (Dcost_pos _ _).le,rag_rep]; have hh:= R.age m b h p
   exact (mul_le_mul_of_nonneg_right he (by positivity)).trans (Credit.rag_fee U (R.depth _ h) (R.depth _ (by omega)) hh (sub_nonneg.mpr (scales _ p)))
lemma missed (h:R.anchor≤m): R.tempC (m+1) b ≤ R.cash U m*R.tempC m b:= (skipping ..).trans (mul_le_mul_of_nonneg_right (R.taxes m h).height (trail_pos ..).le)
-- one fee at m for both W & Wnext.
def doubling (U:Credit):= (dome U).plus ((jump U (dome U)).prodC U)
lemma dominates_both (h:R.anchor≤m)(p:m<b):
     rag R.draws m b ≤ R.cash (doubling U) m * R.tempC m b ∧ rag R.draws (m+1) b ≤ R.cash (doubling U) m * R.tempC m b:=by
    refine ⟨(R.won h p.le).trans (mul_le_mul_of_nonneg_right (Credit.thickens _ (R.depth _ h)) (trail_pos ..).le),le_trans (R.won (by omega) p) ?_⟩
    calc
      _ ≤ R.cash (jump U (dome U)) m *(R.cash U m * R.tempC m b) := mul_le_mul (shift_z R (dome U) h) (missed R h) (trail_pos ..).le (zero_le_one.trans (Credit.purchase _ (R.depth _ h)))
      _ ≤ _:= by rw [← mul_assoc,cash,cash,←Credit.products]; exact mul_le_mul_of_nonneg_right (Credit.thickened _ (R.depth _ h)) (trail_pos ..).le
lemma also_temp (h:R.anchor≤m): R.tempC (m+1) b≤ R.cash (doubling U) m*R.tempC m b:=by
   refine (missed R h).trans (mul_le_mul_of_nonneg_right ?_ (trail_pos ..).le)
   have hp:= R.depth m h
   refine le_trans ?_ (Credit.thickened (dome U) (V:=(jump U (dome U)).prodC U) hp)
   rw [Credit.products]; exact le_mul_of_one_le_left (zero_le_one.trans (Credit.purchase _ hp)) (Credit.purchase _ hp)
end Realm
end YM.WilsonCoeffUV.Bank
