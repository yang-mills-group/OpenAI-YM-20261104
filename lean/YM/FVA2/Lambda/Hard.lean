import YM.FVA2.Lambda.Ray
/-!
# Heat-parameter calculation for the d=4 slope

Preliminaries: the `link` in that calculation, verification of the derivative
in this representation (`levy`,`sweep`) etc. No other dim-reg convention intended.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.Shells
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Plane.Wire
open MS.City MS.Logarithm
open Complex (I)
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n:ℕ}
def steam (z:ℝ) (a:ℝ) := a / 2 * exp (-a*z)
def pond (z r:ℝ):ℝ:= ∫ a in 0..r^2, steam z a
def hot (t:ℝ)(z:ℝ):= exp t ^ (4:ℕ) *exp (-(exp t^(2:ℕ))*z)
lemma tapping (z r:ℝ): HasDerivAt (pond z) (steam z (r^(2:ℕ)) * (2*r) ) r:= by
   have he:Continuous (steam z):= by unfold steam; fun_prop
   refine HasDerivAt.comp r ( intervalIntegral.integral_hasDerivAt_right ( he.intervalIntegrable 0 _ ) (he.aestronglyMeasurable.stronglyMeasurableAtFilter) he.continuousAt) ?_; convert! (hasDerivAt_id' r).pow 2 using 1; simp
abbrev melt (t z:ℝ):ℝ:= pond z (exp t)
lemma meltdown (z:ℝ): Tendsto (fun t:ℝ=> melt t z) atBot (𝓝 0):= by obtain h:= ( (tapping z 0).continuousAt.tendsto ).comp tendsto_exp_atBot; rw [show pond z 0=0 from (by simp [pond]) ] at h; exact h
lemma temp (z t:ℝ): HasDerivAt (fun s=> melt s z) (hot t z) t:= by convert! (tapping z (exp t)).comp t (hasDerivAt_exp t) using 1; unfold steam hot; ring
-- general even scalar Z weight
abbrev MK (D:ℝ→ℝ): Flux (Landau.Atom Axis) QP ℂ
| (some i,false),(some j,false),p=> (↑(D p.sq * precision i j p):ℂ)
| (some i,true), (none,false),p=> (↑(D p.sq * p.sq * p i):ℂ) * I
| (none,false), (some i,true),p=> (↑(D p.sq * p.sq * p i):ℂ) * I
| _, _, _=>0
def link (G:Gauge)(D:ℝ→ℝ) : Latch.Edge G := Landau.choir (MK D) id
lemma z (D:ℝ→ℝ)(i j:BH G) : link G D i j 0=0:= by
    unfold link Landau.choir; split; swap; · rfl
    rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> simp [MK,Momentum.sq,precision,delta]
lemma sweep (G:Gauge)(t:ℝ) : (spaceD G).meter t= link G (hot t):= by
   ext i j q; change (if _ then Landau.line _ _ _ _ else _ )=_; unfold link Landau.choir; split; swap; · rfl
   -- unfold dimension
   rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> simp [MK,Landau.line, coat,k_scale,hot,scaling] <;> ring
lemma closure (G:Gauge)(D:ℝ→ℝ) : Flux.closed (link G D) parity false:= by
    intro i j q; unfold link Landau.choir; split; swap; · tauto
    rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> first | exact fun _=>rfl | exact fun h=>(h rfl).elim
lemma flipped (G:Gauge)(D:ℝ→ℝ) : Reverse (link G D) parity:= by
    intro i j q; unfold link Landau.choir; by_cases h:i.2=j.2; swap; · rw [ if_neg h, if_neg (Ne.symm h),mul_zero ]
    rw [ if_pos h, if_pos h.symm ]
    rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> simp [MK,cross];
    all_goals exact Or.inl (realK ..)
lemma levy (G:Gauge)(t:ℝ): Heat.Jet (fun s=> link G (melt s)) (link G (hot t)) t:= by
   intro i j q; have hx (z v:ℝ): HasDerivAt (fun t=> ((↑(melt t z * v)):ℂ)) (↑(hot t z * v):ℂ) t:= Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t ((temp z t).mul_const v)
   unfold link Landau.choir; by_cases h:i.2=j.2; swap; · simp only [h,↓reduceIte]; apply hasDerivAt_const
   simp only [h,↓reduceIte]; rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> simp only [MK,id_eq] <;> first | exact hasDerivAt_const .. | exact hx .. | (simp only [mul_assoc]; exact (hx _ _).mul_const _ )
lemma xray (i j:BH G)(p:QP): Tendsto (fun s=> link G (melt s) i j p) atBot (𝓝 0):= by
    have hm (v w:ℝ)(z:ℂ): Tendsto (fun s=> (((( melt s v*w):ℝ):ℂ)*z)) atBot (𝓝 0):= by obtain h:= ( Complex.continuous_ofReal.continuousAt.tendsto.comp ( (meltdown v).mul_const w ) ).mul_const z; simp only [zero_mul, Complex.ofReal_zero] at h; exact h
    unfold link Landau.choir; split
    swap; · simp [*]; -- cont const
    rcases i with ⟨⟨_|i,_|_⟩,a⟩ <;> rcases j with ⟨⟨_|j,_|_⟩,b⟩ <;> simp only [MK,id_eq] <;> first | exact tendsto_const_nhds | (simp only [mul_assoc]; apply hm) | (simpa only [mul_one] using hm p.sq ( precision i j p ) 1)
end YM.FVA2.Lambda.Shells
