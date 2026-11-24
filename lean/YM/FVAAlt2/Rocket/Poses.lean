import YM.FVAAlt2.Rocket.Ice
/-! # Request typed positions & cover tests. Equality of arity volumes at those budgets. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.FVAAlt2.Lodge.Track
open Function Set Filter MeasureTheory Topology Real
open Lattice RG Precision Gauge
open Oracle Epoch Calibration Rocket Uniform Binding Diagram Ledger Ledger.Sky Taping Atlas Spatial
open MS MS.Plane MS.Dial MS.Orbit MS.Tide MS.Vista MS.Fleet MS.Land MS.High MS.Rake MS.Tone
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius
variable {X I:Type}(T:Track X){G:Gauge}
variable [LinearOrder I][Fintype I]
-- exact integer spacing. If real points would round to same one on the earliest
-- regulators, extend path with a fallback, without generating new phases or
-- orientations. Makes using EVERY packed allocator routine legitimate.
def penny(x:X):ℕ:= (T.L x).val^(T.batch x)
lemma expense(x:X): (T.penny x:ℝ)= exp (T.Θ x):=by change _= T.fill x; rw [exp_th,penny,Nat.cast_pow,surface]
def landing (i:I): Cover:= fun j=> if j=0 then ((Fintype.equivFin I i).val:ℤ) else 0
def bulk (u: ℝ)(p:Tone.QP): Cover:= fun i=> ⌊exp u*p i⌋
lemma screen_cash (u:ℝ)(x:QP): ‖Tone.embed (bulk u x)- exp u • x‖≤1:=by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr; intro i; rw [Real.norm_eq_abs]; apply abs_le.mpr; have he:= Int.floor_le (exp u*x i); have hv:= Int.lt_floor_add_one (exp u*x i); change -(1:ℝ) ≤ ↑(⌊exp u*x i⌋) - exp u*x i ∧ (↑(⌊exp u*x i⌋):ℝ)-exp u*x i ≤1; constructor <;> linarith
lemma configs : Injective (Tone.embed ∘ (landing: I→ Cover)):=by
 intro i j h; apply (Fintype.equivFin _).injective; apply Fin.ext
 have he:= congr_fun h (0:Axis); simp only [Tone.embed,Function.comp_apply,landing,if_true] at he; exact_mod_cast he
lemma replicate (x:X)(w:I): ‖Tone.embed (T.penny x • landing w)‖= exp (T.Θ x)*‖Tone.embed (landing w)‖:=by
 rw [← T.expense, show Tone.embed _=(T.penny x:ℝ) • Tone.embed (landing w) from funext (fun i=>by simp [Tone.embed,Pi.smul_apply,nsmul_eq_mul]),norm_smul_of_nonneg (by positivity)]
variable (U:X→ Cover)(a:ℝ)(k:I→QP)(l:Filter X)
def pin(x:X):I→QP:= fun i=> exp (-(T.Θ x)) • Tone.embed (bulk (T.Θ x) (k i))
lemma returns (h: Tendsto T.batch l atTop): Tendsto (T.pin k) l (𝓝 k):=by
 apply tendsto_pi_nhds.mpr; intro w; apply tendsto_iff_dist_tendsto_zero.mpr; refine squeeze_zero (fun i=>dist_nonneg) (g:=fun i=> Real.exp (-(T.Θ i))) (fun i=>?_) (tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (T.θ_runs h)))
 rw [dist_eq_norm]; set c:= exp (-(T.Θ i)); have he: c≠0:= (exp_pos _).ne'; have ht: exp (T.Θ i)= c⁻¹:= by unfold c; rw [Real.exp_neg, inv_inv]
 calc
    _= c * ‖Tone.embed (bulk (T.Θ i) (k w))- exp (T.Θ i) • k w‖:=by rw [ ← norm_smul_of_nonneg (show 0≤c from (Real.exp_pos _).le),smul_sub (r:=c), ht, smul_inv_smul₀ he ]; rfl
    _ ≤ _:= mul_le_of_le_one_right (exp_pos _|>.le) (screen_cash ..)
-- beware notation!
def video (w:I)(x:X):Cover:= if Clamp k (T.pin k x) then bulk (T.Θ x) (k w) else T.penny x • landing w
abbrev picture := T.PoseT a U (T.video k)
lemma screenT(w:I)(x:X): testP (picture T U a k) x w= if Clamp k (T.pin k x) then T.pin k x w else Tone.embed (landing w):=by
 change exp (-(T.Θ x)) • Tone.embed (video T k w x)=_; unfold video; split; · rfl
 rw [show Tone.embed _= exp (T.Θ x) • Tone.embed (landing w) from ?_, Real.exp_neg, inv_smul_smul₀ (exp_pos _|>.ne')]; funext i; rw [← T.expense]; simp [Tone.embed,Pi.smul_apply,nsmul_eq_mul]
-- ordinary mkΠ
lemma comeback (h:Tendsto T.batch l atTop) (hx:Injective k): Tendsto (testP (picture T U a k)) l (𝓝 k):=by
 have he:= T.returns k l h; refine he.congr' (( he.eventually ( Dial.earlyW hx ) ).mono fun x hx=>?_); funext i; rw [screenT, if_pos hx]
lemma profile_ok : MS.Tide.Profile (picture T U a k).profile (T.video k) :=by
 intro i; refine ⟨1+‖k i‖ + ‖Tone.embed (landing i)‖,by positivity,fun w=>?_⟩
 have hs: 1 ≤ exp (T.Θ w):= T.filled w; set c:= exp (T.Θ w); have hc:0<c:= exp_pos _
 change ‖Tone.embed _‖ ≤ _ * c; unfold video; split
 · obtain he:= norm_add_le (Tone.embed (bulk (T.Θ w) (k i))- c • k i) (c • k i); rw [sub_add_cancel,norm_smul_of_nonneg hc.le] at he
   apply he.trans; nlinarith only [hs,screen_cash (T.Θ w) (k i), mul_nonneg (norm_nonneg (Tone.embed (landing i))) hc.le, show ‖Tone.embed (bulk (T.Θ w) (k i))- c • k i‖≤1 from screen_cash ..] -- hs expr c
 next h=> rw [T.replicate]; change c* _≤ _; nlinarith [norm_nonneg (k i)]
lemma useful (h:T.VenueT U) (hx:Injective k)(ht: Tendsto T.batch l atTop): Dial.Uses (picture T U a k) l a:=by
 apply T.launch a U (T.video k) l h ht ( T.profile_ok U a k ); apply MS.Dial.unpose (v:=a); intro i j hij
 let r:= ‖k i-k j‖; let s:= ‖Tone.embed (landing i)-Tone.embed (landing j)‖
 let f:= picture T U a k; let g(x):= ‖testP f x i-testP f x j‖
 have hc : 0<r:= norm_pos_iff.mpr (sub_ne_zero.mpr (hx.ne hij)); have hp:0<s:= norm_pos_iff.mpr (sub_ne_zero.mpr (configs.ne hij))
 have he (x:X): min (r/2) s ≤ g x ∧ g x ≤ max (2*r) s:=by
    unfold g f; rw [screenT,screenT]; split
    next h=> exact ⟨ le_trans (min_le_left ..) (h i j hij|>.1.le), (h i j hij|>.2.le).trans (le_max_left ..)⟩
    next h=> exact ⟨ min_le_right .., le_max_right ..⟩
 refine ⟨⟨max (2*r) s,by positivity,fun x=> ?_⟩,⟨ min (r/2) s,by positivity,fun x=>?_⟩⟩ <;> (simp only [Geo.roots,Pi.zero_apply,exp_zero, frameF,mul_one]; first|exact (he _).1|exact (he _).2 )
end YM.RegulatorIR.FVAAlt2.Lodge.Track
