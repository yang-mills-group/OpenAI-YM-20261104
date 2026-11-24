import YM.QuadraticLocal.Hearth
/-!
Transport field-independent, INCLUDING global marks (unit mark can use the same
canvas). Do not charge a *total test* at every root; preserves per-site bill Cannibal. Reserve at
Σ of p.In req explicit; exact bless via carrier roots and ratio-parent fibers. Use ζ=old exponent
and pay post-L cost of fiber volume and rebasing, not volume. No big stencils or topology lost.
Push carries polynomial scalars exactly even off all masks. Can't infer a price from a prior
unnormalized density estimate behind flags. Final display will retain these as unmasked Captions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Spire
open Function Filter Finset Lattice Wilson RG Ac Marker Push.Corrected Push.AbsoluteSums MeasureTheory
open RG3 Progress.DirectedRecipe PhysicalNext PhysicalNext.Repeat Lotus Merge Palette Trigger
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Muse RemainderComparison.Mosaic RemainderComparison.Serif RemainderComparison.Typeface
open Push.Local GridRenewal.Rain
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}{n c:Side}{P : Rep G n}{V:Type}[DecidableEq V]{R:Census V}{o:V→Site n}
    {x a r p y Δ y₀ C t₀ θ c0:ℝ}
variable {T:Type*}{I:Type}{b:BudgetPoint} (A: Lamps T I G b o R) (S:StepData c n)
-- b : BudgetPoint
set_option quotPrecheck false
variable {P' : BudgetPoint}
variable (w:V→ℝ)(hw:∀ i,0<w i)
local notation "τ"=> Poly.toll w
abbrev Waves := { i:I // A.clear i }
def post (L:StepData c n) (X:Support n) := X.image L.ratio.parent
private def charge (r:Lattice.Ratio c n)(x:RegularAddress n) : RegularAddress c:=
    ⟨r.parent x.site, x.support.image r.parent,mem_image_of_mem _ x.anchor⟩
local notation "J"=> Waves A
local notation "κ"=> S.ratio.parent ∘ o

def convertGlobal (p':BudgetPoint) : Lamps T (Waves A) G p' (S.ratio.parent ∘ o) R where
  mode := A.mode ∘ Subtype.val
  live _:= A.live _
  address i:= charge S.ratio (A.address i.val)
  roots i v hv:= mem_image_of_mem _ (A.roots i.val v hv)
  nominal t i _:= A.nominal t i.val 1
  legal _ _:= regular_const _
  clear _:= True
  pure := fun _ _ _ _=> rfl
local notation "A'"=> convertGlobal A S P'
lemma frame (t:T)(U:Config G c)(i:J) : (A').frame i t U= A.frame i.val t 1:=by
    unfold convertGlobal Lamps.frame Lamps.light; rw [if_pos i.prop]; simp only; rw [if_pos (show True from True.intro)]; rfl
-- receipt α positive.B any. No summability/rate growth assumption about moving stage, require actual versus repr.
variable (hs : b.B ≤ 2*P'.B) (ha:0≤θ) (hy:0≤y) (hA:A.Paid w b.B y t₀)
open Extra.Multi
-- Extra projection sketch reserve v=0. Costs from book.H
set_option quotPrecheck false
def fees (L:Side)(θ:ℝ) := (Fintype.card (Site L):ℝ)* Real.exp (θ*Extra.Multi.tilePrice 0)
include hw hs ha hy hA
lemma pays (hK:20*θ*tilePrice 0 ≤ (S.ratio.count.val:ℝ)*y) : (A').Paid w P'.B θ (fees S.ratio.count θ*t₀):=by
    obtain ⟨f,hf,h,hH⟩:=hA.budget; have hg i:0≤ τ (A.mode i)*f i:=mul_nonneg (Poly.worth hw _).le (hf _); refine ⟨fun i=>f i.val,fun i=>hf i.val,fun i t x hx=>?_ ,fun x=>?_⟩
    · apply bound_weaken (bound_const _); apply (h i.val t (A.address i.val).site (A.address i.val).anchor).2 1 (Next.Foundations.one_healthy _ _ b.threshold_pos.le) [] (Nat.zero_le _) (by simp)
    let α:=S.ratio.parent; let u:= univ.filter (fun i => α i=x)
    let a0 := θ* (tilePrice 0:ℝ); let q:= Real.exp a0
    let g (x:Site n)(i:J):= if x∈A.ground i.val then q*(τ (A.mode i.val)*f i.val* Real.exp (y*(coverNumber b.B (A.ground i.val):ℝ))) else 0
    have hN(x:Site n): SumBudget (g x) (q*t₀):=by
       let f' i := q*(if x∈ A.ground i then τ (A.mode i)*f i* Real.exp (y*(coverNumber b.B (A.ground i):ℝ)) else 0)
       convert budget_pull Subtype.val (Subtype.val_injective («p»:=A.clear)) (show SumBudget f' (q*t₀) from budget_scale (Real.exp_pos a0).le (hH x)) using 1; ext i; unfold f' g; split <;> simp [*]
    have hV i: (A').ground i = (A.ground i.val).image S.ratio.parent:= rfl
    have hv:=parentCost S x; change u.card ≤ _ at hv
    have hZ: ((q*t₀)*(u.card:ℝ))≤ _:=(mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr hv) (budget_nonneg (hN 0))) -- `ℝ Int?`
    have he:= budget_over u g (fun _=>q*t₀) (fun i _=>hN i); have ht: ∑ j∈u,q*t₀ ≤ fees S.ratio.count θ*t₀:= by simp only [sum_const,nsmul_eq_mul]; unfold fees; linarith
    refine budget_loosen (budget_mono he ?_ fun i=>?_) ht
    · intro i; split; exact mul_nonneg (hg _) (Real.exp_nonneg _); exact le_rfl
    split
    next hv=>
       have hGx:= Extra.Multi.projection_reserve S.ratio P'.B_pos hs ha hK (A.ground i.val) ((A').ground i) (hV i|>.symm ▸ halo_subset ..)
       obtain ⟨j,hj,rfl⟩:= mem_image.mp ((hV i) ▸ hv)
       have hu': g j i= _:= if_pos (c:= j∈ A.ground i.val) hj
       refine le_trans (b:=g j i) ?_ (Finset.single_le_sum (fun j (_:j∈u)=> (hN j).1 i) (show j∈u from Finset.mem_filter.mpr ⟨mem_univ _,rfl⟩))
       rw [hu']; rw [mul_left_comm q, ← Real.exp_add]; apply mul_le_mul_of_nonneg_left _ (hg _); refine Real.exp_monotone (hGx.trans (?_)); exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    next=> exact he.1 i
omit hw hs ha hy hA
-- step.Exact.Global yes. no k.
variable (L:Gallery T I o P R)
lemma log (P':BudgetPoint)(t:T)(U) : (convertGlobal L.E S P').log t U= globes L t:=tsum_congr (fun i=>frame L.E S t U i)
lemma no_spark (ha:0≤a)(hw:∀ i,0<w i)(d:ℝ)(hP:L.E.Paid w P.p.B a d) (t:T): (globes L t).part R.quiet=0:=by unfold globes; rw [Poly.share (f:=fun i:{ i // L.E.clear i }=> L.E.frame i.val t 1) ((hP.sums ha hw t 1).comp_injective (i:=Subtype.val) (Subtype.val_injective («p»:=L.E.clear)))]; simp_rw [Lamps.frame_quiet]; exact tsum_zero -- edit
section shift
variable (F:T → Config G c→ Poly R)(K:T→ Config G n→ Poly R)(P':BudgetPoint)
variable {O:Activities G c}{H:Hard T P' O.forced O.K (S.ratio.parent ∘ o) R}{log:T→ Config G c→ Poly R}
variable [Fintype V]
variable (hQ:ReadZone T P' O H (fun t=>S.push P.beta (K t)) log)
-- to include G;
include hQ
lemma postGlobal (d:ℝ)(ha:0≤a)(hw:∀ i,0<w i)(hP:L.E.Paid w P.p.B a d)
    (hk:S.IsKernel P.beta G)(hi:∀ t, Integrable (K t) (prior G _))(he:∀ t U,L.density t U= cyclone (globes L t)* K t U)(hL:∀ t U,(log t U).part R.quiet=0) :
    ReadZone T P' O H (fun t=> S.push P.beta (L.density t)) (fun t U=> globes L t+log t U):=by
    intro i U; obtain ⟨hs,v,hv⟩:=hQ i U
    let g : Marker.Poly R →ₗ[ℂ] Marker.Poly R := Algebra.lmul ℂ (Marker.Poly R) (cyclone (globes L i))
    let f := g.toContinuousLinearMap.restrictScalars ℝ
    have hA: S.push P.beta (L.density i) U= cyclone (globes L i)* S.push P.beta (K i) U:=by unfold StepData.push; have ht:= f.integral_comp_comm (StepData.push_slice hk U _ (hi i)); simp_rw [he]; simp_rw [f.map_smul] at ht; exact ht
    refine ⟨hs,v,?_⟩; dsimp only at hv ⊢; rw [hA,hv,mul_smul_comm,←mul_assoc]; congr 2; -- one goal
    rw [← passes (globes L i+log i U) (show _=0 by simp_rw [Poly.part_plus, no_spark w L ha hw d hP i, hL, add_zero]),← GridRenewal.Rain.passes _ (hL ..),GridRenewal.Rain.plus]
end shift
end YM.QuadraticLocal.Spire
