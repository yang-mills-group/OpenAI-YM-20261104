import YM.FVA2.Generator.Qgau
/-!
# Introduce check/MS field infinitesimal generators for the same conversion

Differentiate on any log scale at the kernel-family level, all formal orders.
Use all linear endomorphism evaluations; also state ODE in formal g variable with
this precise sign (scale generator from smaller separated distances), and `Walk`
throttle. No regularity assumption on nondiagonal unshifted position $B_t$ required.
This is for the mass-independent scheme.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Generator.Der
open Function Filter Set MeasureTheory Maxwell Maxwell.Free
open MS MS.Local.Physical MS.High MS.Wind MS.Land MS.Native MS.Tide MS.Fleet
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus Position Position.Axes Arrival
open MS.Menus MS.Book MS.Book.Convolve MS.Book.Program MS.Puff MS.Puff.Actors PowerSeries
open scoped Topology ContDiff BigOperators Classical
open Dframe Reg.Point Reg.Token Reg.Choice _root_.YM.FVA2.Scale
open YM.FVA2.Scale.Facets Scale.Level Scale.Equator Scale.Measure Scale.Jury
open Scale.Meter Scale.GroupS Scale.Beta
variable {G:Gauge}{d n k:ℕ}{A: Arenas G}{Β: Guard G d}
def Instant (A:ℝ→ Guard G d)(B:Guard G d)(t:ℝ): Prop:= ∀ i:ℕ,∀ v:Module.Dual ℂ (FieldEnd G d),HasDerivAt (fun t=> v (coeff i ( A t ))) (v (coeff i B)) t
namespace Instant
variable {A:ℝ→Guard G d}{B:Guard G d}{t:ℝ}
private lemma uniqueF {f g: FieldEnd G d}(h:∀ v:Module.Dual ℂ (FieldEnd G d), v f=v g): f=g:=by let b:=Module.finBasis ℂ (FieldEnd G d); apply b.equivFun.injective; exact funext (fun i=> h (b.coord i))
lemma once (h: Instant A B t)(h':Instant A Β t): B=Β:= PowerSeries.ext fun i=> uniqueF fun v=> (h i v).unique (h' i v)
lemma zero_col {i:ℕ} (h:Instant A B t)(g:FieldEnd G d)(hh:∀ t,coeff i (A t)=g): coeff i B=0:=by
    apply uniqueF; intro v; obtain H:=h i v; simp_rw [hh] at H; rw [map_zero]; exact H.unique (hasDerivAt_const ..)
lemma preserve (h:Instant A B t)(hu:∀ t, Native (A t)): Native B:= by intro i; apply uniqueF; intro v; obtain H:= h i (v ∘ₗ Level.diag); simp only [ LinearMap.comp_apply, hu ] at H; exact H.unique (h i v)
lemma shift (h:Instant A B t)(q:Cn): Instant (fun t=> stepV q (A t)) (stepV q B) t:= by
    intro i v; simp_rw [stepV,coeff_mk,rules,map_sum, _root_.map_smul,smul_eq_mul]; apply HasDerivAt.fun_sum; intro j _; exact (h j v).const_mul _
lemma stamp (h:Instant A B t)(C:Guard G d): Instant (fun t=> C*A t) (C*B) t:=by
    intro i v; simp_rw [ coeff_mul,map_sum ]; apply HasDerivAt.fun_sum; intro j _; exact h j.2 (v ∘ₗ LinearMap.mulLeft ℂ (coeff j.1 C))
-- no new topology on Sec modules
lemma horizon {e:ℕ}{C:ℝ→Guard G e}{D:Guard G e}(h:Instant A B t)(he: Instant C D t)(i:d≤e)(hC:∀ t,Walk i (A t) (C t)): Walk i B D:= by
    intro j p; let b:=Module.finBasis ℂ (Sec G e); apply b.equivFun.injective; funext k; obtain hp:= he j ( (b.coord k) ∘ₗ (LinearMap.applyₗ (R:=ℂ) ( up i p )) ); change HasDerivAt (fun t=> b.coord k (coeff j (C t) (up i p))) _ _ at hp; simp_rw [hC] at hp; exact hp.unique (h j (( b.coord k ) ∘ₗ (up i) ∘ₗ (LinearMap.applyₗ (R:=ℂ) p) ) ) -- coord types
end Instant

-- construct gamma from real subspace.Currency for every row. At n≥1 in Change; use rational-basis across all; enough for unit/reality.
private abbrev Price (G:Gauge)(d:ℕ):= Sec G d × Module.Dual ℂ (Sec G d) × (ℂ →ₗ[ℝ] ℝ)
private def cost (i:Price G d): Module.Dual ℝ (Normalize.Change G d):= i.2.2 ∘ₗ ( ( i.2.1 ∘ₗ (LinearMap.applyₗ (R:=ℂ) (M₂:=Sec G d) i.1) ).restrictScalars ℝ ) ∘ₗ ( Normalize.Change G d ).subtype
variable {p:ℝ→Cn}{B:ℝ→Frames G}
variable (X:Law A p B)
include X
private lemma present (k d:ℕ) : ∃ x: ↥( Change G d ),∀ v:Module.Dual ℂ (FieldEnd G d), HasDerivAt (fun t=> v (coeff k (B t d))) (v x.val) (0:ℝ):= by
    by_cases hx:k=0; · subst k; refine ⟨ 0, fun v=>?_ ⟩; simp_rw [Base.zero ( X.paid .. )]; change HasDerivAt _ (v 0) _; rw [map_zero]; exact hasDerivAt_const ..
    obtain ⟨s,u,hs⟩:= Future.bought (cost (G:=G) (d:=d)) (fun x hx=> by
       apply Subtype.ext; ext1 p; let b:=Module.finBasis ℂ (Sec G d); apply b.equivFun.injective; change b.equivFun (x.val p)=b.equivFun 0; rw [map_zero]; funext i; apply Complex.ext; exact hx (p, b.coord i, Complex.reLm); exact hx (p,b.coord i,Complex.imLm))
    let T (t:ℝ): Change G d:= ⟨coeff k (B t d), ( X.paid t d ).high _ hx ⟩
    let f(i:s)(t:ℝ):= cost i.val (T t); let Z:ℝ:=0; have hp(i:s): HasDerivAt (f i) (deriv (f i) Z) Z:= by
       apply DifferentiableAt.hasDerivAt; let g:= fun t:ℝ=> i.val.2.1 (coeff k (B t d) i.val.1); obtain ⟨p,h⟩:= Rhythm.from_poly.mp ( X.proper d k i.val.1 i.val.2.1 ); change g=_ at h; have hg : DifferentiableAt ℝ g Z:=by rw [h]; apply ( p.differentiable.restrictScalars ℝ ).differentiableAt.comp _ (Complex.ofRealCLM.differentiableAt)
       exact (i.val.2.2.toContinuousLinearMap.differentiableAt.comp _ hg)
    let x:= ∑ i:s,deriv (f i) Z • u i; refine ⟨ x, fun v=>?_ ⟩; let C:= (v.restrictScalars ℝ) ∘ₗ ( Change G d ).subtype; have he(t): v (coeff k (B t d))=∑ i:s,f i t • v (u i).val:=by change C (T t)=∑ i:s,_; rw [hs (T t),map_sum C]; refine Finset.sum_congr rfl (fun i _=> map_smul C _ _)
    change HasDerivAt _ (C x) _; unfold x; simp_rw [ he, map_sum,map_smul C ]; exact HasDerivAt.fun_sum (fun i _=> (hp i).smul_const (C (u i)))
lemma available (d:ℕ): ∃ q:Guard G d,(∀ i,coeff i q∈ Change G d) ∧ Instant (fun t=>B t d) q 0:= by
    choose y h using fun i=>present X i d; refine ⟨ mk (fun i=>(y i).val),fun i=>?_, fun i v=>?_ ⟩; rw [coeff_mk]; exact (y i).property; rw [coeff_mk]; exact h i v
omit X
def engine (p:ℝ→Guard G d): Guard G d:= if H:∃ q, Instant p q 0 then H.choose else 0
include X
lemma walks (d:ℕ): Instant (fun t=>B t d) (engine (fun t=>B t d)) 0:= by obtain ⟨q,hp,H⟩:= available X d; unfold engine; rw [dif_pos ( show ∃ q, Instant (fun t=> B t d) q 0 from ⟨q,H⟩ ) ]; exact Classical.choose_spec (p:=fun q=>Instant (fun t=>B t d) q 0) (⟨_,H⟩)
lemma stays (d:ℕ) : Native (engine (fun t=>B t d)) ∧ ∀ i, coeff i (engine (fun t=>B t d))∈Normalize.Change G d:= by
    let H:= walks X d; refine ⟨ H.preserve (fun t=> X.ready t d),?_ ⟩; obtain ⟨q,Hq,h⟩:= available X d; rw [H.once h]; exact Hq
lemma step (d:ℕ)(t:ℝ): Instant (fun t=> B t d) ( B t d * stepV (p t) (engine (fun t=>B t d)) ) t:= by
    let Γ:= engine (fun t=>B t d); let F(s:ℝ):= B t d * stepV (p t) (B s d); obtain H:= (( walks X d ).shift ( p t ) ).stamp (B t d); have he(s): F (s-t)=B s d:= by unfold F; rw [← old_g (s-t) (B t d) (X.ready t d), ← (X.toTouched.additive t (s-t)).2 d, add_sub_cancel .. ]
    intro i v; let q : ℂ:= v (coeff i ( B t d * stepV (p t) Γ )); obtain hh:= H i v; change HasDerivAt (fun t=> v (coeff i ( F t ))) q 0 at hh; rw [← sub_self t] at hh; obtain ht:= hh.scomp (h:=fun x:ℝ=> x-t) t ((hasDerivAt_id' t).sub_const t); simp_rw [Function.comp_def,he,one_smul] at ht; exact ht
lemma grace {d k:ℕ}(h:d≤k): Walk h ( engine (fun t=>B t d) ) (engine (fun t=>B t k)):= (walks X d).horizon (walks X k) h fun t=> X.continues t h
lemma heel (d:ℕ): PowerSeries.coeff 0 (engine (fun t=>B t d))=0:= (walks X d).zero_col _ (fun t=> ( X.paid t d ).zero )
end YM.FVA2.Generator.Der
