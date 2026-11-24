import YM.Comparison.RG02.Adjacent.Curve
/-!
# Invariance under signal composition

Fusing two clock/nil markers in all the accounts, specializing to the orbital curve
for sign/frame transport. Do not truncate inside a measured density.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Adjacent
open Function Filter Finset MeasureTheory
open PertExtension.Series PertExtension.Series.Tested YM.Tensor
open Order Assembly Moving Moving.Path Moving.Shift Laplace
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

local notation "φ"=> 𝓝 (0:ℝ)
local notation "λ₀"=> (ω:WithTop ℕ∞)
structure Shadow (r:ℕ)(f g:ℝ→ℂ) : Prop where
 left : ContDiffAt ℝ ω f 0
 right : ContDiffAt ℝ ω g 0
 aligns i : i≤r → motion f i=motion g i
lemma instant (f : ℝ→ℂ) (r:ℕ) : ContDiff ℝ ω (peval (motion f) r) := ContDiff.sum (fun _ _=> (contDiff_id.pow _).smul contDiff_const)
lemma polary (F : ℕ→ℂ) (i k:ℕ) : motion (peval F k) i= if i≤k then F i else 0 := congrFun ((ordinary (f:=peval F k) ((ContDiffAt.sum fun _ _=> ((contDiffAt_id (x:=(0:ℝ))).pow _).smul contDiffAt_const))).unique (Aspiration.polynomial F k)) i
namespace Shadow
variable {f g f' g' h:ℝ→ℂ} {i k r:ℕ}
lemma refl (h : ContDiffAt ℝ ω f 0) : Shadow r f f := ⟨h,h,fun _ _=>rfl⟩
lemma same (h : f=ᶠ[φ] g)(hv : ContDiffAt ℝ ω f 0) : Shadow r f g := ⟨hv,hv.congr_of_eventuallyEq h.symm,fun _ _=> mgerm h⟩
lemma symm (h : Shadow r f g):Shadow r g f:= ⟨h.right,h.left, fun _ w=> (h.aligns _ w).symm⟩
lemma trans (hx:Shadow r f h)(hp:Shadow r h g): Shadow r f g:=⟨hx.left,hp.right,fun _ w=> (hx.aligns _ w).trans (hp.aligns _ w)⟩
lemma pairing (u: Shadow r f g)(v: Shadow r f' g'): Shadow r (fun x=>f x+f' x) (fun x=>g x+g' x) := ⟨u.left.add v.left,u.right.add v.right,fun i w=>by rw [madd u.left v.left,madd u.right v.right, u.aligns _ w,v.aligns _ w]⟩
lemma product (u: Shadow r f g)(v: Shadow r f' g'): Shadow r (fun x=>f x*f' x) (fun x=>g x*g' x) := by
   refine ⟨u.left.mul v.left,u.right.mul v.right,fun i hi=>?_⟩
   rw [mprod u.left v.left,mprod u.right v.right]; apply sum_congr rfl; intro j hj; have hh:= mem_antidiagonal.mp hj; rw [u.aligns _ (by omega),v.aligns _ (by omega)]
lemma sum {T:Type*} (t:Finset T) {f g:T→ℝ→ℂ} (h:∀i∈t,Shadow r (f i) (g i)): Shadow r (fun x=>∑ i∈t,f i x) (fun x=>∑ i∈t,g i x):= by
    induction t using Finset.induction with
    | empty=>simp_rw [sum_empty]; exact Shadow.refl contDiffAt_const
    | insert v t he ih=> simp_rw [sum_insert he]; exact (h v (mem_insert_self ..)).pairing (ih (fun i hi=> h i (mem_insert_of_mem hi)))
lemma respite (u : Shadow r f g)(K:UnitCost): Shadow r (f ∘ K.enter) (g ∘ K.enter) := by
   have hl:ContDiffAt ℝ ω f (K.enter 0):= K.borne.symm ▸ u.left
   have hr:ContDiffAt ℝ ω g (K.enter 0):= K.borne.symm ▸ u.right
   refine ⟨hl.comp _ K.here,hr.comp _ K.here, fun i hi=> ?_⟩
   have hi' (i:ℕ) (hi:i≤r) : iteratedFDeriv ℝ i f 0=iteratedFDeriv ℝ i g 0:=by
      ext; -- ∀ direction
      refine (smul_right_inj (show ( (i.factorial:ℝ)⁻¹)≠0 from by positivity)).mp (u.aligns i hi)
   unfold motion Assembly.jet
   rw [iteratedFDeriv_comp hl K.here le_top,iteratedFDeriv_comp hr K.here le_top,K.borne]
   apply congrArg (fun p : ContinuousMultilinearMap ℝ (fun _ : Fin i => ℝ) ℂ => (i.factorial:ℝ)⁻¹ • p (fun _=>1))
   unfold FormalMultilinearSeries.taylorComp
   refine sum_congr rfl fun c hc=> ContinuousMultilinearMap.ext fun v=>?_
   simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, OrderedFinpartition.applyOrderedFinpartition_apply, ftaylorSeries]; rw [hi' _ (c.length_le.trans hi)]
lemma truncate (r:ℕ)(h : ContDiffAt ℝ ω f 0) : Shadow r f (peval (motion f) r):= ⟨h,(instant ..).contDiffAt,fun i hi=> ((polary _ i r).trans (if_pos hi)).symm⟩
end Shadow
-- align need Product r smooth compute powers not volume
end YM.Comparison.RG02.Adjacent
