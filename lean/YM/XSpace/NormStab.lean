import YM.XSpace.Roar
/-!
# Infinitesimal free normalization nondegeneracy

The nondegeneracy test uses **all point** configurations at every horizon.
Filtration and H enforced (no manifest full O(4)-equivariance assumed on finite-condition
candidates). On the complex field space with real involution; this is the Lie algebra of
permitted changes on the arrays. Even from silent equality on the complexified test family
one needs the commutation with the real involution in this proof! (The orbit lemma uses
real polynomial moments.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.XSpace.Normalize
open Function Set Filter Maxwell Maxwell.Free Maxwell.Wick Sample
open scoped BigOperators Topology Classical ContDiff
variable {G : Gauge} {d n :ℕ} (g:G.Simple)

include g
lemma roar_stopped (T:Change G d) (H:silence G d (spill T.val)) (hd:4≤d) (x:Sec G d) (he : reel d x=x): T.val x=0:=by
  have hi : realForm x.val=x.val:=congr_arg Subtype.val he
  let y (t : ℝ) (Z:TaylorTower G):= probe Z (forward T.val t x).val
  have hh (Z:TaylorTower G) : HasDerivAt (fun t=>y t Z) (probe Z (T.val x).val) 0:=by
    let L := LinearMap.toContinuousLinearMap (((probe Z).toLinearMap ∘ₗ coeS (G:=G) d).restrictScalars ℝ |>.comp (tableD G d).symm.toLinearMap)
    have he (p) : L (tableD G d p) = probe Z p.val:=by unfold L; simp; rfl
    have hk : (fun t=> y t Z)= L ∘ (fun t => tableD G d (forward T.val t x)):= funext fun t=> (he _).symm; rw [hk]; convert! L.hasFDerivAt.comp_hasDerivAt (0:ℝ) (forwards T.val x 0) using 1; rw [forward0, he]
  have hv := local_sing g x.property y (fun t=> sings (p:=(forward T.val t x).val) (forward T.val t x).property) (fun t=> ?_) (fun Z=> ?_)
  · apply Subtype.ext; apply equalPol; intro Z
    have hl : HasDerivAt (fun t=>y t Z) 0 0:=(hasDerivAt_const _ (probe Z x.val)).congr_of_eventuallyEq (hv.mono fun t h=> congr_fun h Z)
    rw [show probe Z (T.val x).val=0 from (hh Z).unique hl,Submodule.coe_zero,map_zero]
  · obtain ⟨M,hm,h⟩:= exists_wrench (coreColor g) (points_moves T H g hd t) (realizes_real T t) hd
    refine ⟨M,h,funext fun Z=>?_⟩; unfold y; rw [← painted x]; exact (hm Z x.val x.property hi).symm
  simpa only [y,forward0] using (hh Z).continuousAt.tendsto

lemma normstab (T:Change G d) (H:silence G d (spill T.val)) : T=0:=by
  have he : ∀ x: Sec G d,reel d x=x → T.val x=0:=by
    intro x h; by_cases hl:4≤d; exact roar_stopped g _ H hl x h
    apply Subtype.ext; rw [← swept]; exact kills_low (d:=d) g (lt_of_not_ge hl) (Change_unit T) x.val x.property
  have hh : coeS d ∘ₗ T.val=0:= real_tests fun x h=>by rw [LinearMap.comp_apply,he x h,map_zero]; rfl
  apply Subtype.ext; ext1 x; apply Subtype.ext; exact DFunLike.congr_fun hh x
end YM.XSpace.Normalize
