import YM.FVA2.Rank.Kappa
/-!
# Finite Λ scaling for all degrees. From the one-regulator prescription

 Uniform degree of the pole and action log-polynomials & exact reexpression yield an exact
 bulk reset identity under comparing two MS reference scales. This strengthens the continuum
 limit assertion: the Team's bare reparameterization satisfies the FULL formal group
 law already, **at finite log**. Use the applications in `Register/Pressroom.lean` to any Team
 satisfying their authorities and H & Unit conditions. Describe argument scale signs explicitly:
 `ν` is log ν (MS convention) relative to X measurement, `x` its value at the lattice regulator in
 Top units, `t>0` probes shorter distances. Same coupling as used at all orders.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda
open Function Filter Set MeasureTheory Maxwell Maxwell.Free Maxwell.Wick
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Unique Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta
namespace Engine
variable {p q:Cn} {k:ℕ} (hp: Rooted p)(hq: Rooted q) (he:∀ i<k,coeff i p= coeff i q)
include he
lemma relate (j:ℕ)(i:ℕ)(hi:i<k): coeff i (p^j)=coeff i (q^j):= by
  induction j generalizing i with
  | zero=> simp
  | succ j ih=> rw [pow_succ,pow_succ,coeff_mul, coeff_mul]; refine Finset.sum_congr rfl fun a ha => ?_; obtain hx:= Finset.mem_antidiagonal.mp ha; rw [ih _ (by omega), he _ (by omega)]
include hp hq
lemma only (j:ℕ) (hj:j≠1): coeff k (p^j)= coeff k (q^j):= by
  cases j with | zero=> simp | succ j=>
   rw [pow_succ, pow_succ, coeff_mul,coeff_mul]; refine Finset.sum_congr rfl fun a ha=>?_ ; obtain hx:= Finset.mem_antidiagonal.mp ha
   by_cases hv:a.1=0; · rw [hv, show coeff 0 (p^j)=0 from blocked hp (by omega), show coeff 0 (q^j)=0 from blocked hq (by omega), zero_mul, zero_mul]
   by_cases hz:a.2=0; · rw [hz,hp,hq,mul_zero,mul_zero]
   rw [relate he _ _ (by omega), he _ (by omega)]
lemma one_time (F:Cn)(hk:0<k): coeff k ( F.subst p )- coeff k ( F.subst q )= coeff 1 F * ( coeff k p- coeff k q ):= by
  simp_rw [ ← Constants.actual_subst _ _ hp, ← Constants.actual_subst _ _ hq, coeff_mk,rules ]; rw [← Finset.sum_sub_distrib, Finset.sum_eq_single 1 ]; · dsimp [Program.cut]; simp only [pow_one]; ring
  · intro b _ hb; unfold Program.cut; rw [only hp hq he b hb,sub_self]
  intro h; simp at h; omega
omit hp hq he
lemma follow {X:Type*}{F:Filter X}{q:Cn}{f:X→ Cn}(g:Cn)(hp:Rooted g)(h: Harmony F f q): Harmony F (fun x=> (f x).subst g) (q.subst g):= by
  intro i; simp_rw [← Constants.actual_subst _ _ hp, coeff_mk, rules,smul_eq_mul ]; exact tendsto_finsetSum _ fun j _=> ( h j ).const_mul _
end Engine
namespace Time
variable {G:Gauge}(ν:ℝ)(Y:XSpace.Initialize G){V:XSpace.Normalize.Store G}(K:XSpace.Rose.Pick V){O: Booked (Press.portDeck G)}(T:MS_Data G O)
variable (S:Prescription (Press.portDeck G)) (t:ℝ)(h:G.Simple)(hs:TaylorOKF T (Press.wickInput Y) S)(hr:Favors.Horder S)(hu:Ace.UnitP S)
local notation "τ" => Measure.chi K
local notation "ψ" => Scale.GroupS.ψ K T ν
local notation "π" => Scale.GroupS.Ψ K T ν
local notation "σ" => Program.shift S.team
include h hs hr hu
local notation "φ"=> Measure.f K ν T
local notation "Q"=> true_m ν Y K T S h hs hr hu
local notation "F"=> Measure.chi K ν T
lemma use_χ : (F).subst (π t)=τ (ν-t) T:= by
  rw [Ψ, ← Tangent.steps F ( (Specific.vigor_f Y K ν T S h hs hr hu ).compose ( true_ψ ν Y K T S h hs hr hu t )) ( Specific.vigor_x Y K ν T S h hs hr hu ), ← Tangent.steps F (Specific.vigor_f Y K ν T S h hs hr hu) ( true_ψ ν Y K T S h hs hr hu t ), ( Select.vigor Y K ν T S h hs hr hu ).right, subst_X (licence _ (true_ψ ν Y K T S h hs hr hu t).start), Scale.GroupS.ψ, Tangent.steps _ ( Specific.vigor_f Y K ν T S h hs hr hu ) ( Specific.vigor_x Y K ν T S h hs hr hu ), ( Select.vigor Y K ν T S h hs hr hu ).left, X_subst ]
omit h hs hr hu
lemma runs_S (p:Team): Meter.Clear (Program.shift p):= by
    intro i; unfold Program.shift; simp_rw [coeff_mk]; split_ifs <;> try exact Pace.narrow _
    convert! Pace.prime (fun (_:Unit)=>0) (p i).coupling using 1; simp
lemma almost : Tendsto Schedule.theta Front atTop:= by
  have hz:= ( Schedule.speed ( z:= (0:Points 0)) ); exact hz.comp ( points_at _ )
-- uniqueness of polynomial even when only a cofinal limit. along log native scale. sign from minus theta.
lemma stationary (ν:ℝ){f:ℝ→ℂ}(h:Rhythm f)(hs:Tendsto (fun m:Mesh=> f (ν-Schedule.theta m)) Front (𝓝 0)) : f=0:= by
  obtain ⟨p,rfl⟩:= Rhythm.from_poly.mp h; by_cases ht:p.degree≤0
  · have hz(p':ℂ): p.eval p'=p.coeff 0:= by conv_lhs=>rw [Polynomial.eq_C_of_degree_le_zero ht, Polynomial.eval_C]
    simp_rw [hz] at hs ⊢; rw [ tendsto_nhds_unique tendsto_const_nhds hs ]; rfl
  have hn: Tendsto (fun m:Mesh=> -(ν-Schedule.theta m)) Front atTop:= by simp_rw [neg_sub]; simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right Front (-ν) almost
  have hv: Tendsto (fun i:Mesh=> ‖((ν-Schedule.theta i:ℝ):ℂ)‖ ) Front atTop:= tendsto_atTop_mono ( f:=fun i=> -(ν-Schedule.theta i) ) (fun i=> by simpa only [Complex.norm_real, Real.norm_eq_abs] using neg_le_abs (ν-Schedule.theta i) ) hn
  exact False.elim (not_tendsto_atTop_of_tendsto_nhds (continuous_norm.continuousAt.tendsto.comp hs) (Polynomial.tendsto_norm_atTop p (lt_of_not_ge ht) hv))
include h hs hr hu
lemma horizon (k:ℕ): ∀ x:ℝ, coeff k (σ (x-t)) = coeff k ((σ x).subst (π t)):= by
  induction k using Nat.strong_induction_on with
  | _ k ih=>
   let P:=π t; obtain he:Tangent P:= Q t
   let A(x:ℝ):= (σ x).subst P; let B(x:ℝ):= σ (x-t)
   have hA x:Rooted ( A x ):= circle _ _ (share ..) he.start
   by_cases hk:k=0; · intro x; subst k; exact (show coeff 0 ( B x )=_ from share .. ) |>.trans (hA x).symm
   let l(m:Mesh) := Rose.chosen Y K m; let y(m:Mesh):= ν-Schedule.theta m
   let g(x:ℝ):= coeff k (B x)-coeff k (A x);
   have hv m: Dframe.reset (ν-t) S m=B (y m):= by simp only [Dframe.reset,B,y]; rw [ sub_right_comm ]
   have hs₁: Harmony Front (fun m:Mesh=> (l m).subst (B (y m))) (τ (ν-t) T):= by simp_rw [ ← hv ]; exact forecast (ν-t) Y K S T h hs hr hu
   have hs₂: Harmony Front (fun m:Mesh=> (l m).subst (A (y m))) (τ (ν-t) T):= by
     have ht (i:Mesh): (l i).subst (A (y i))= ( prospects ν Y K S i ).subst P:= by
       unfold A; rw [ ← subst_comp_subst_apply ( licence _ ( share .. ) ) ( licence _ he.start ) ]
     simp_rw [ht]; rw [← use_χ ν Y K T S t h hs hr hu]; exact Engine.follow P he.start ( forecast ν Y K S T h hs hr hu )
   have hfg: Tendsto (fun m:Mesh=> g (y m) ) Front (𝓝 0):= by
     have ht m: coeff k ((l m).subst ( B (y m))) - coeff k ((l m).subst ( A (y m) ))= g ( y m ) * coeff 1 (l m):= (Engine.one_time (share ..) ( hA _ ) (fun j hj=> ih j hj _) (l m) (by omega)).trans (mul_comm ..)
     obtain hz:= ((hs₁ k).sub (hs₂ k)).div (Rose.xc Y K h) one_ne_zero; rw [sub_self, zero_div] at hz; apply hz.congr'; filter_upwards [ Rose.usable Y K h ] with m hm; apply (div_eq_iff hm).mpr; exact ht m
   let L:= runs_S S.team;
   have hT:Rhythm g:= by
     apply Rhythm.sub; · have hr':= ( Rhythm.unit.mpr (L k) ).pre ( Polynomial.X-Polynomial.C t ); simpa only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C] using hr'
     exact Rhythm.unit.mpr ( Pace.formal.substitute L ( Pace.formal.fixed (fun _: Unit=>P) ) (fun i _=> he.start) k )
   have hgm:= stationary ν hT hfg; exact fun x=> sub_eq_zero.mp ( congr_fun hgm x )
theorem scale (x:ℝ): σ (x-t) = (σ x).subst (π t):= PowerSeries.ext fun k=> horizon ν Y K T S t h hs hr hu k x
end Time
end YM.FVA2.Lambda
