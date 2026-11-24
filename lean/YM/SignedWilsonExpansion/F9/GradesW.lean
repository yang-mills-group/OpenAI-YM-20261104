import YM.SignedWilsonExpansion.F9.Wage
/-!
# Finite hor. salary utilities for comparisons even on varying periods
Big O interest (relative U-power) without positivity requirements on B. 
Keep FitsZ for fixed purchase currencies. 
-/
set_option autoImplicit false
set_option maxHeartbeats 410000
noncomputable section
namespace YM.SignedWilsonExpansion.Commission
open Filter Function Set Metric Asymptotics WilsonCoeffUV.Bank
open scoped Topology ContDiff BigOperators Classical
variable {ι σ η E F K R T:Type*}
variable [NormedField K] [AddCommGroup E][Module K E] [AddCommGroup F][Module K F]
variable {L:Filter ι}{u g x B Y:ι→ℝ}[Fintype σ]
abbrev Salary (L:Filter ι)(τ B:ι→ℝ)(K:Type*) [NormedField K][Module K E] (x:ι→E) := ∀ f: Module.Dual K E,Wage L τ B (fun i=> f (x i))
lemma Across.salary {Z:ι→E} (p:Across L u K Z): Salary L u 1 K Z:= fun f=> billed_wage (p f)
lemma Salary.shift {Z:ι→E} (v₀:Salary L u B K Z)(h:u=O[L] g): Salary L g B K Z:=fun f=> Wage.transfer (v₀ f) h
lemma Wage.ornament (C:Credit)(p:ι→ ℝ)(hu: Wage L u 1 p) : Wage L u 1 (C.buy ∘ p):=by
    let hx:=Wage.mul (Wage.unitC C.x) (hu.power C.d); refine Wage.fix hx (Eventually.of_forall (fun i=> (?_))) (Eventually.of_forall (fun i=> (?_)))
    · rfl
    change (1:ℝ)*1^_=_; simp
lemma Wage.reals {A:ι→ℝ}: Wage L u B A ↔Wage L u B (fun i=> (A i:ℂ)):=by
    constructor
    · intro p; exact Wage.rel p (IsBigO.of_bound' (Eventually.of_forall fun i=> by simp))
    intro p; exact Wage.rel p (IsBigO.of_bound' (Eventually.of_forall fun i=> by simp))
lemma Wage.posPart {A:ι→ℂ}(p: Wage L u B A): Wage L u B (fun i=>(A i).re):= Wage.rel p (IsBigO.of_bound' (Eventually.of_forall fun _=> Complex.abs_re_le_norm _))
lemma center_zero (h:Maxer L u){p:ι→K}(v:p=ᶠ[L] fun _=>0): Wage L u B p:= Wage.fix Wage.nil v.symm (.refl ..)
namespace Salary
variable {P W:ι→E}
lemma born (c:E): Salary L u 1 K (fun _=>c):= fun i=> Wage.unitC _
lemma via (p:Salary L u B K P)(v:P=ᶠ[L] W)(hx:B=ᶠ[L] Y): Salary L u Y K W:=fun i=> Wage.fix (p i) (v.fun_comp i) hx
lemma transfer (p:Salary L u B K P) (v: Wage L u Y B): Salary L u Y K P:=fun i=> Wage.ascend (p i) v
lemma spend (p: Salary L u B K P)(v:∀ n:ℕ,(fun i=> u i^n*B i)=o[L] Y): Salary L 1 Y K P:=fun i=> Wage.enroll ((Wage.spend (p i) v).isBigO)
lemma tilt {x:ι→ K} (p: Wage L u B x) (v:Salary L u Y K P) : Salary L u (B*Y) K (fun i=> x i • P i):=fun Q=>by simp_rw [map_smul]; exact Wage.smul p (v Q)
lemma pass (v:Salary L u B K P)(Y:E→ₗ[K] F): Salary L u B K (Y∘P):= fun i=> v (i ∘ₗ Y)
lemma negative (v:Salary L u B K P):Salary L u B K (fun i=> -P i):= by intro i; simp_rw [map_neg]; exact Wage.neg (v i)
lemma add (h:Maxer L u)(v: Salary L u B K P)(w: Salary L u B K W): Salary L u B K (fun i=>P i+W i):=by intro i; simp_rw [map_add]; exact Wage.plus h (v i) (w i)
lemma diff (h:Maxer L u)(v: Salary L u B K P)(w: Salary L u B K W): Salary L u B K (fun i=>P i-W i):=by intro i; simp_rw [map_sub]; exact Wage.minus h (v i) (w i)
lemma many (h:Maxer L u)(Q:ι→η→E)(S:Finset η)(v:∀ i∈S,Salary L u B K (fun j=> Q j i)): Salary L u B K (fun i=>∑ j∈S,Q i j):=by intro i; simp_rw [map_sum]; exact Wage.sum h _ _ (fun j w=> v j w i)
lemma sufficient (h:Maxer L u) (N:Module.Basis σ K E)(p:∀ i,Wage L u B (fun j=> N.repr (P j) i)): Salary L u B K P:=by
   refine (Salary.many h (fun i j=> N.repr (P i) j • N j) Finset.univ (fun i _=> Salary.tilt (p i) (Salary.born (N i)))).via (Eventually.of_forall fun i=> N.sum_repr _) (?_); simp
lemma reading (h:Maxer L u) (N:Module.Basis σ K E)(p:∀ i,Wage L u B (fun j=> N.repr (P j) i)): Wage L u B (fun j=> N.equivFun (P j)):=by
    apply Wage.rel (Wage.sum h (fun i j=> ‖N.repr (P i) j‖) Finset.univ (fun i _=> Wage.norm (p i))) (IsBigO.of_bound' (Eventually.of_forall (fun j=>?_)))
    let D:= fun i=> ‖N.repr (P j) i‖; have hx:= Finset.sum_nonneg (s:=Finset.univ) (f:=D) fun i _=>norm_nonneg _; rw [Real.norm_of_nonneg hx]; exact (pi_norm_le_iff_of_nonneg hx).mpr (fun i=> Finset.single_le_sum (s:=Finset.univ) (f:=D) (fun i _=> norm_nonneg _) (Finset.mem_univ i))
lemma matrix (h:Maxer L u) (N:Module.Basis σ K E)(Q:ι→ E→ₗ[K] F) (v: Salary L u B K P) (w: ∀ i:σ, Salary L u Y K (fun j=>Q j (N i))) : Salary L u (B*Y) K (fun i=> Q i (P i)):=by
    conv => arg 5; ext i; rw [← N.sum_repr (P i),map_sum]
    simp_rw [map_smul]; exact Salary.many h _ _ (fun i _=> Salary.tilt (v (N.coord i)) (w i))
lemma matrix_full (h:Maxer L u) [FiniteDimensional K E] (Q:ι→ E→ₗ[K] F) (v: Salary L u B K P) (w: Salary L u Y K Q): Salary L u (B*Y) K (fun i=> Q i (P i)):= matrix h (Module.finBasis K E) Q v (fun i=> w.pass (LinearMap.applyₗ _))
lemma matrix_enough (h:Maxer L u) (N:Module.Basis σ K E)(Q:ι→ E→ₗ[K] F) (v:∀ i, Salary L u B K (fun j=>Q j (N i))): Salary L u B K Q:=by
    let f(i:σ)(z:F): E→ₗ[K]F:= (N.coord i).smulRight z; let X(i): F→ₗ[K] (E→ₗ[K]F):= { toFun:=f i,map_add':= fun x y=>LinearMap.ext (fun z=>smul_add ..), map_smul':= fun c x=>LinearMap.ext fun z=>smul_comm .. }
    refine (Salary.many h (fun i j=> f j (Q i (N j))) Finset.univ (fun j _=> (v j).pass (X j))).via (Eventually.of_forall fun i=>?_) (.refl ..); apply N.ext; intro j; rw [LinearMap.sum_apply,Finset.sum_eq_single j]; simp [f]; intro i _ p; simp [f,p, Ne.symm p]; simp
end Salary
variable [NormedAddCommGroup R]
lemma as_salary1 {Q:ι→ R} (p:Wage L 1 B Q): Q=O[L] B:=by obtain ⟨n,v⟩:= p; simpa using v
lemma Salary.tendsto (N:Module.Basis σ K E) {x:ι→E} (h:Salary L u B K x)(p:∀ n:ℕ,Tendsto (fun i=>u i^n*B i) L (𝓝 0)): Tendsto (fun i=> N.equivFun (x i)) L (𝓝 0):= tendsto_pi_nhds.mpr (fun i=> (h (N.coord i)).next_zero p)
end YM.SignedWilsonExpansion.Commission
