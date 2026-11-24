import YM.MS.Dial.Set
/-! Geometry realizations of profile path for every physical separated tuple. Arbitrary degree tests.Knobs locality. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real High
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Fleet -- order
open Lattice
open scoped Topology ContDiff
variable {W I:Type} {μ:ℝ}{i h n:ℕ}[LinearOrder W][Fintype W] {x:W→ QP}
def Ball (i:ℕ): ℕ:= Nat.ceil (Real.exp ( (i:ℝ)^2 ))
def side (i:ℕ): Side:= Fleet.walkway (Ball i)
def center (i:ℕ): Cover:= Fleet.crane (Ball i)
abbrev ann (μ:ℝ): Geo ℕ := ⟨ fun i=>i, fun i=>μ-i, fun _=>by exact_mod_cast Nat.zero_le _ ⟩
lemma SuperA (μ:ℝ): Super atTop side (ann μ).θ:= by
   intro a; filter_upwards [ (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually ( eventually_ge_atTop a ) ] with i hi; let x:=Ball i; have ht:(i:ℝ)^2 ≤ log ( tickA side i ):= by
       rw [ ← Real.exp_le_exp ]; have hp := Vista.δ_p side i; rw [exp_log hp, tickA, show (dimT side i).val= _ from Fleet.fullC x ]; apply ( Nat.le_ceil ( Real.exp ( (i:ℝ)^2 ) ) ).trans; change (x:ℝ)≤ _; push_cast; linarith [ Nat.cast_nonneg ( α:=ℝ ) x ]
   apply le_trans _ ht; rw [pow_two]; exact mul_le_mul_of_nonneg_right hi ( Nat.cast_nonneg i )
-- point replace support round any with error ≤1 
def assign (s:ℕ)(p:QP): Cover:= fun i=> ⌊exp (s:ℝ)*p i⌋
abbrev Screen (p:W→ QP)(i:W)(v:ℕ):= assign v (p i)
abbrev Movie (v:ℝ)(x:W→QP)(n:ℕ): Trial ℕ W where
   profile:= { θ:= fun i=> ( ( i+n :ℕ ):ℝ), η:=fun i=> v-( (i+n:ℕ):ℝ), room i:=Nat.cast_nonneg _ }
   side i:= Dial.side (i+n)
   off w i:= Screen x w (i+n)
   head i:=center (i+n)
lemma Screen_price (i:ℕ)(x:QP) : ‖Tone.embed (assign i x) - Real.exp ( i:ℝ ) • x‖ ≤ 1:= by
   apply ( pi_norm_le_iff_of_nonneg zero_le_one ).mpr; intro j; apply abs_le.mpr; have he := Int.floor_le ( exp (i:ℝ)*x j ); have hv:= Int.lt_floor_add_one ( exp (i:ℝ)*x j ); change -(1:ℝ)≤ ((⌊exp (i:ℝ)*x j⌋:ℤ):ℝ) - exp (i:ℝ)* x j ∧ ((⌊exp (i:ℝ)*x j⌋:ℤ):ℝ) - exp (i:ℝ)* x j ≤ 1; constructor <;> linarith
lemma costR (x:QP)(a:ℕ): ‖( exp (-(a:ℝ)) • Tone.embed (assign a x))-x‖≤ exp (-(a:ℝ)):= by
   let r:=exp ( a:ℝ ); have ht:r≠0:=( exp_pos _ ).ne'; rw [exp_neg,show r⁻¹ • Tone.embed (assign a x) - x=r⁻¹ • (Tone.embed (assign a x) - r • x) from (by rw [smul_sub,inv_smul_smul₀ ht]), norm_smul_of_nonneg (inv_nonneg.mpr (exp_pos _|>.le)) ]; exact mul_le_of_le_one_right (by positivity) (Screen_price a x)
omit [LinearOrder W] in
lemma filmed (x:W→ QP)(μ:ℝ): Tendsto (testP (Movie μ x n)) atTop (𝓝 x):= by
   let a(i:ℕ):= ( (i+n:ℕ):ℝ ); have ht:Tendsto (fun i:ℕ=> i+n) atTop atTop := StrictMono.tendsto_atTop fun i j h=> by exact Nat.add_lt_add_right h n;
   have hv:Tendsto ( fun i=> exp (-a i) ) atTop (𝓝 0):= tendsto_exp_atBot.comp ( tendsto_neg_atTop_atBot.comp ( tendsto_natCast_atTop_atTop.comp ht ) );
   apply tendsto_pi_nhds.mpr; intro w; apply tendsto_iff_dist_tendsto_zero.mpr; simp_rw [ dist_eq_norm ]; exact squeeze_zero (fun i=> norm_nonneg _) (fun i=> costR ( x w ) ( i+n )) hv
lemma crew (x:W→ QP) (h:Injective x) (μ:ℝ): ∃ F:Trial ℕ W,Uses F atTop μ∧Tendsto (testP F) atTop (𝓝 x):= by
   obtain ⟨n,hv⟩:= eventually_atTop.mp ((filmed x μ (n:=0)).eventually (earlyW h)); let F:=Movie μ x n; have hh(v:ℕ): Clamp x ( testP F v ) := hv (v+n) (by omega); let P:=F.profile; have he:Tendsto (fun i:ℕ=>i+n) atTop atTop:= StrictMono.tendsto_atTop fun i j h=> Nat.add_lt_add_right h n
   refine ⟨F,⟨ ?_,?_,fun _=>rfl,tendsto_natCast_atTop_atTop.comp he, fun c=> he.eventually ( SuperA μ c ),fun i=> Cleared (i+n |> Ball), centered_size _ _ fun i=> Fleet.centerD (Ball (i+n)) ⟩, filmed .. ⟩
   · intro w; refine ⟨ 1+‖x w‖,by positivity,fun i=>?_⟩; let b := Movie μ x n; let z:=exp (P.θ i); let Y:=assign (i+n) ( x w ); change ‖Tone.embed Y‖ ≤ _; have ht := Screen_price (i+n) ( x w ); apply le_trans ( b:=1+ z*‖x w‖ ) _ _; ·  obtain hg:= norm_add_le ( Tone.embed Y-z • x w ) ( z • x w ); rw [sub_add_cancel] at hg; apply hg.trans; rw [ norm_smul_of_nonneg ( by unfold z; positivity ) ]; gcongr
     have H : 1≤ z:= Real.one_le_exp ( P.room _ ); change _ ≤ (1+_)*z; linarith
   apply unpose ( v:=μ ) F.off; intro i j hi; refine ⟨ ⟨ 2*‖x i-x j‖,mul_pos (by norm_num) ( norm_pos_iff.mpr (sub_ne_zero.mpr (h.ne hi))),fun k=>?_⟩,⟨‖x i-x j‖/2, div_pos ( norm_pos_iff.mpr ( sub_ne_zero.mpr ( h.ne hi ) )) (by norm_num ),fun k=>?_⟩⟩ <;> simp only [roots,frameF,Pi.zero_apply,exp_zero,mul_one]; exact ( hh k i j hi|>.2 ).le; exact ( hh k i j hi |>.1 ).le
end YM.MS.Dial
