import YM.FVAAlt2.Normalizations

/-! Actual finite analytic projection compared through coupling-parameter
shifts (native polynomial `θ` costs not assumed bounded in cutoff), and a
consumer with a full finite family of (as yet only formal) insertions.
Quantifiers are all lists / all sector even allowed through those applications.
The kernel from the same period-dependent torus height is kept. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2
open MS MS.Koszul MS.Native MS.Native.Wilsonian MS.Book MS.Cylinder MS.Puff MS.Puff.Actors MS.Swirl MS.Puff.Mom Swirl.Near MS.Fleet
open MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog Convolve Program
open Function Finset Filter Topology MeasureTheory Lattice SchemeRG11.Sway SchemeRG11.Sway.Lam Pert.Orb
open scoped PowerSeries ContDiff
section shift
variable {A V B:Type}[AddCommGroup A][Module ℂ A]
variable (a:A)(c: Program.Cn)
lemma shift_const : substitute c (useN.refineV a)=useN.refineV a:= by
  funext i; rw [rules,sum_eq_single_of_mem 0 (by simp)]; · change PowerSeries.coeff i (c^0) • (useN.refineV a 0) = _; rw [pow_zero,PowerSeries.coeff_one]; unfold SplitP.refineV; rw [if_pos (show 0=useN.origin from rfl)]; by_cases h:i=useN.origin; rw [if_pos h,if_pos (show i=0 from h),one_smul]; rw [if_neg h,if_neg (show i≠0 from h),zero_smul] -- nested rw order
  intro j _ h; unfold SplitP.refineV; rw [if_neg (show j≠ useN.origin from h),smul_zero]
variable {c} (hc: Rooted c)(M:Actors A)
include hc
lemma laws_subst : Tether (substitute c) (M.stack useN) (M.stack useN):= by refine ⟨shift_const M.unit _,fun _ _=> ?_⟩; exact Eq.symm (substitute_pair hc _ _ M.core)
lemma subst_cheer (x:T A)(h:x 0 =0): M.Cheer useN (substitute c x)=substitute c (M.Cheer useN x):= by
  funext i; let Z:= M.stack useN; change Z.cheers (substitute c x) i i=_; rw [← (laws_subst hc M).cheersV]; rw [rules,rules]; exact sum_congr rfl fun k hk=> congrArg (cut c k i • ·) (overbook M useN x h (show k ≤ i from mem_Iic.mp hk))

variable {p:Sector B}{K:Matrix B B ℂ}[Fintype B]
lemma denominator_sub (U:SpecB B) (h:U 0=0): ℶV K (exp0 p (substitute c U))= substitute c (ℶV K (exp0 p U)):= by unfold exp0; rw [subst_cheer hc (actor p) U h]; exact comm c _ (View K)
lemma numerator_sub (U F: SpecB B)(h: U 0=0): ℶV K ((PermV p).core (exp0 p (substitute c U)) (substitute c F))= substitute c (ℶV K ((PermV p).core (exp0 p U) F)):= by unfold exp0; rw [subst_cheer hc _ U h, ← (laws_subst hc (actor p)).craft]; exact comm c _ (View K) -- defeq pattern?
lemma cost_sub {U F:SpecB B}{Z:T ℂ}(h:U 0=0)(hv: Endμ K p U F Z): Endμ K p (substitute c U) (substitute c F) (substitute c Z):= by unfold Endμ; rw [numerator_sub hc U F h,denominator_sub hc U h]; exact Eq.trans (congrArg _ hv) ((laws_subst hc Toy).craft _ _)
end shift

section moments
variable {A W:Type} {p:Sector A} [Fintype A] [LinearOrder W] (w:Finset W)
omit [Fintype A] in
lemma stencilL {X: Mate A W}(U: W→PowerSeries (Com p))
    (h:∀ i:W,X {i}=Com.forget p (U i))(he:∀ s:Finset W,s.card≠1→ X s=0): Font p X w= Com.forget p (∏ i∈w,U i):= by
  have hm(u:Finset W): X u∈ (PermV p).guard:= by
    by_cases ht:u.card=1; · obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp ht; rw [h]; exact Com.kept _
    rw [he u ht]; exact Submodule.zero_mem _
  induction w using Finset.induction with
  | empty=> rw [prod_empty,Com.forget_one]; exact MS.Puff.Stencil.simple_E (PermV p) X (SplitP.marked W) (show X ∅=0 from he _ (by simp))
  | insert i s hs H=> unfold Font at H; rw [Font,Stencil.cheers _ hm he _ _ hs, h,H, prod_insert hs, Com.forget_mul]
end moments

section shifted
open Ends Bos MS.Cylinder.Lab Puff.Stencil
variable {G:Gauge}{n:Side}{ι κ:Type}[Fintype ι][DecidableEq ι][Fintype κ][DecidableEq κ]
variable (A:Module.Basis ι ℝ (Land G n))(b:Module.Basis κ ℝ (ScalarGhost G n))
variable {W:Type}[LinearOrder W] (t:Team) (z:ℝ)(c:W→Cover)(o:Cover)(V: W→Actor G) (s:Finset W)
local notation "u"=>Program.shift t z
local notation "p"=> isOdd (ι:=ι) (κ:=κ)
local notation "L"=> embeddingM A b
local notation "X₀"=>posEnergy (Wilsonian.core G) n true
local notation "K"=>propagator (κ:=κ) A
local notation "X1"=> posEnergy (style G (Stripped t) z) n true
local notation "cₓ"=> fun i=>wrap n (o+c i)
-- scale_shift of zero-removed bulk
lemma shift_start : substitute u X₀=X1 := by
 unfold style; rw [strip_wobble]; -- cannot use wobble?
 funext i; by_cases h:i=0; · rw [h,Program.pay0,posEnergy,if_pos rfl]; rfl
 rw [posEnergy,if_neg h,rules,rules,map_sum,Finset.smul_sum]; apply sum_congr rfl; intro j _; rw [map_smul]; by_cases he:j=0
 · subst j; simp [cut,PowerSeries.coeff_one,h]
 rw [posEnergy,if_neg he]; exact smul_comm .. 

variable (Y: W→PowerSeries (Bos ι)) (Xr:W→ℕ→Dot G Cover)

variable (χ: ∀ i, V i z=substitute (Program.shift t z) (Xr i))
variable (η:∀ i, promote (pull (embeddingM A b)) (promote (posMark n (wrap n (o+c i))) (Xr i))=Com.forget (isOdd (κ:=κ)) (Bos.upS (Y i)))

-- ONLY η is a stencil hypothesis; V(t) establishes its projections later. Treat on Xr moment.smooth with κ attached.
include χ η
lemma shift_mark (F:Finset W) : pullSeries L (MS.Puff.Mom.Font Draft.DotFlip (stencil (fun w=> V w z) cₓ) F) = substitute u (Com.forget p (Bos.upS (∏ i∈F,Y i))) := by
 let S:=stencil Xr cₓ
 have hab(w:Finset W):pullSeries L (stencil (fun w=>V w z) cₓ w)= substitute u (pullSeries L (S w)):= by
   by_cases hm : w.card=1
   · obtain ⟨v,rfl⟩:= Finset.card_eq_one.mp hm; unfold S stencil; simp only [Finset.singleton_nonempty,dif_pos,Finset.card_singleton,if_true,Finset.min'_singleton]; rw [χ]; exact Eq.trans (congrArg (pullSeries L) (comm u (Xr v) _)) (comm u _ (pull L))
   unfold S stencil; split; · simp only [map_zero]
   simp only [map_zero] 
 rw [← pull_font (embTie A b),funext hab]; have he:= (laws_subst (share t z) (actor p)).figure (SplitP.marked W) (fun w=>pullSeries L (S w)) F -- wrong use theorem on Marked uses actor?? stacked law already
 change (PermV p).Cheer (SplitP.marked W) ((substitute u) ∘ (fun w=>pullSeries L (S w))) F = _
 refine he.symm.trans (congrArg (substitute u) ?_); change Font p (fun w=> pullSeries L (S w)) F=_
 rw [map_prod (Bos.upS), stencilL F (fun i=>Bos.upS (Y i)) ?_ ?_]; · intro i; unfold S stencil; simp only [Finset.singleton_nonempty,dif_pos,Finset.card_singleton,if_true,Finset.min'_singleton]; exact η i
 intro w hx; unfold S stencil; split; · simp only [map_zero]
 simp only [map_zero]
variable (hn : Admissible n) (hs:∀ i j,Symm Draft.DotFlip (V i z j).val)(hr:∀ i j,∃ k:ℤ, Limit (V i z j).val k)
include hn hs hr

theorem shifted_points : PhysicalSum G t z n true s c o V (substitute u (unpack (Lentry (ray A (∏ i∈s,Y i))))) := by
  rw [slice_end A b t z c o V hs hr s,← shift_start]
  rw [shift_mark A b t z c o V Y Xr χ η s]; -- ordering
  rw [show pullSeries L (substitute u X₀)=substitute u (pullSeries L X₀) from comm u X₀ _ ]; exact cost_sub (share t z) (by change pull L (if (0:ℕ)=0 then (0: Raw (Mode G n) ℂ) else _) = _; rw [if_pos rfl, map_zero]) (bare_points A b hn _) -- base none
end shifted
end YM.FVAAlt2
