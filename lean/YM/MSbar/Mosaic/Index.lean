import YM.MSbar.Mosaic.Velocity
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Mosaic
open Function Filter MeasureTheory Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress Topology
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film
variable {G:Gauge}(s:Side){ι τ:Type*}{X f g:ι→ℝ}{φ: Filter ι}{L:ℝ}
variable (hX:Tendsto X φ atTop)
include hX
namespace Run
lemma Ymul (h:Run φ X f 0)(hp:Run φ X g 0):Run φ X (fun i=> f i*g i) 0:=by simpa using! mulR hX h hp
lemma Ypow (h:Run φ X f 0)(p:ℕ):Run φ X (fun i=>f i^p) 0 := by simpa using! raise hX h p
lemma Yrat {a:ℝ}(h:Run φ X f a)(hp:Run φ X g 0):Run φ X (fun i=>f i*g i) a:=by simpa using! mulR hX h hp
lemma Ycost {a:ℝ}(hp:Run φ X f 0)(h:Run φ X g a):Run φ X (fun i=>f i *g i) a:=by simpa using! mulR hX hp h
lemma Yneg (h:Run φ X f 0): Run φ X (fun i=>-f i) 0 := by simpa only [neg_one_mul] using! mulK hX h (-1)
lemma absA {a:ℝ} (h:Run φ X f a):Run φ X (fun x=>|f x|) a:=h.cash (Eventually.of_forall fun x=>by rw [abs_abs])
lemma Yplus (h:Tendsto f φ (𝓝 L)):Run φ X f 0:=by
    refine (Run.token hX (|L|+1)).cash ?_; filter_upwards [h.abs.eventually (ge_mem_nhds (lt_add_one (|L|)))] with i hi; exact hi.trans (le_abs_self _)
lemma Ymax (h:Run φ X f 0)(hv:Run φ X g 0) :Run φ X (fun i=>max (f i) (g i)) 0:=by refine (addR hX (absA hX h) (absA hX hv)).cash ?_; filter_upwards with i; apply le_trans _ (le_abs_self _); rcases le_total (f i) (g i) with hp|hp <;> simp [hp]
lemma Yceil (h:Run φ X f 0)(hv:∀ᶠ i in φ,0≤ f i): Run φ X (fun i=> (Nat.ceil (f i):ℝ)) 0:=by
    refine (addR hX h (token hX 1)).cash ?_; filter_upwards [hv] with i he; rw [abs_of_nonneg (by positivity : 0 ≤ (Nat.ceil (f i):ℝ))]; exact (Nat.ceil_lt_add_one he).le.trans (le_abs_self _)
end Run
-- uniform cofinal subsequence helper nested
omit hX in
lemma cofy {m:ℕ→Type*} {P Q:(j:ℕ)→ m j→Prop} (h:∀ (g:ℕ→ℕ)(a:(j:ℕ)→m (g j)), Tendsto g atTop atTop → (∀ j,P (g j) (a j)) → ∀ᶠ i in atTop,Q (g i) (a i)) : ∀ᶠ i in atTop,∀ p:m i,P i p→ Q i p :=by -- omit hX
   by_contra he; rw [eventually_atTop] at he; push Not at he; choose c hc a ha hP using he; have hf:= tendsto_atTop_mono hc (tendsto_id (x:=atTop)); obtain ⟨i,hi⟩:= (h c a hf ha).exists; exact hP i hi
-- physical widths
abbrev hatW:= Alto.flurry
noncomputable def vol (x:ℝ):= hatW x/32
noncomputable def hull (x:ℝ):=4*vol x
noncomputable def αm (x:ℝ):= (hatW x)^(-3:ℤ)
noncomputable def pawn(p:ℕ):ℝ:= -((p:ℝ)+1/4)/2
noncomputable def Ht (x:ℝ):= Heath.Stock.cue x
noncomputable def goalP(x:ℝ)(p:ℕ):= x^pawn p
abbrev ξy (x:ℝ)(G:Gauge)(L:Side):= Heath.Stock.tip G L x
namespace Run
lemma stanza : Run φ X (fun i=>hatW (X i)) 0:= Ypow hX (logP hX) _
lemma tempo : Run φ X (fun i=> (hatW (X i))⁻¹) 0:= Yplus hX (tendsto_inv_atTop_zero.comp (Alto.broad.comp hX))
lemma plans(k:ℕ) : Run φ X (fun i=> (Nat.ceil ((hatW (X i))^k): ℝ)) 0:= Yceil hX (Ypow hX (stanza hX) k) ((Alto.broad.comp hX|>.eventually_ge_atTop 0).mono (fun i hi=> pow_nonneg hi _))
lemma alpha_p : Run φ X (fun i=> αm (X i)) 0 ∧Run φ X (fun i=> (αm (X i))⁻¹) 0:=by unfold αm; simp only [_root_.zpow_neg,inv_inv]; exact ⟨by simp_rw [←_root_.inv_zpow]; exact Ypow hX (tempo hX) 3,Ypow hX (stanza hX) 3⟩ -- names
lemma waxing : Run φ X (fun i=> cue (X i)) (-(1/2)) ∧ Run φ X (fun i=> (cue (X i))⁻¹) (1/2) :=by
    simp_rw [cue, Real.sqrt_eq_rpow, inv_inv]; refine ⟨(core hX _).alter (?_:_),core hX _⟩; filter_upwards [hX.eventually_gt_atTop 0] with i hi; rw [Real.rpow_neg hi.le]
lemma shift (h:Tendsto (fun i=>X i) φ atTop) (G:Gauge)(hp:G.Simple)(g:Side)(p:ℝ): Tendsto (fun i=> ξy (X i) G g) φ atTop ∧ Tendsto (fun i=> (ξy (X i) G g)^p/(X i)^p) φ (𝓝 1):=by
    let Y:=fun i=>ξy (X i) G g; let C:=G.slopeConstant* Real.log g.val; have he:Tendsto (fun i=> (Y i)/(X i)) φ (𝓝 1):=by
         have hz:= ((tendsto_const_nhds (x:=(1:ℝ)) (f:=φ)).add (tendsto_const_nhds (x:=C)|>.div_atTop h)); rw [add_zero] at hz; refine hz.congr' ?_; filter_upwards [h.eventually_gt_atTop 0] with i hi; unfold Y ξy; change _=(X i+C)/X i; rw [add_div,div_self hi.ne']; -- congr
    have hp:= (tendsto_atTop_add_const_right φ C h); have hz: Tendsto Y φ atTop:=hp; refine ⟨hz, ?_⟩; refine (show Tendsto (fun i=>(Y i/X i)^p) φ (𝓝 1) from (by simpa only [Real.one_rpow] using! he.rpow_const (p:=p) (Or.inl one_ne_zero))).congr' ?_; filter_upwards [hz.eventually_ge_atTop 0,h.eventually_ge_atTop 0] with i hi hh; exact Real.div_rpow hi hh _
omit hX in
lemma wander (h:Tendsto X φ atTop)(G:Gauge)(hp:G.Simple)(g:Side) (a:ℝ) (f:ι→ℝ) : Run φ X f a ↔ Run φ (fun i=> ξy (X i) G g) f a:= by
    let Y:= fun i=> ξy (X i) G g; have hU :=(shift h h G hp g a).1; constructor <;> intro E b hb <;> obtain ⟨x,hx,hA⟩:= exists_between hb
    · have he: Tendsto (fun i=>X i^x/Y i^x) φ (𝓝 1):=by
           have hx: Tendsto (fun i=> ((Y i)^x/(X i)^x)⁻¹) φ (𝓝 1) := by simpa only [inv_one] using! (shift h h G hp g x).2.inv₀ one_ne_zero
           simpa only [inv_div] using hx
      filter_upwards [E x hx, hU.eventually_gt_atTop 0,he.eventually (ge_mem_nhds (one_lt_two)), (mulK hU (core hU x) 2) b hA] with i h₀ h₁ hu he; refine (h₀.trans ((div_le_iff₀ (Real.rpow_pos_of_pos h₁ x)).mp hu)).trans ((le_abs_self _).trans he)
    filter_upwards [E x hx, h.eventually_gt_atTop 0,(shift h h G hp g x).2.eventually (ge_mem_nhds one_lt_two), (mulK h (core h x) 2) b hA] with i h₀ h₁ hu he; refine (h₀.trans ((div_le_iff₀ (Real.rpow_pos_of_pos h₁ x)).mp hu)).trans ((le_abs_self _).trans he)
end Run
end YM.MSbar.Mosaic
