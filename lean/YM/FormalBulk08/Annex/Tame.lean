import YM.FormalBulk08.Annex.Seam
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Annex
open Function Filter Lattice Dawn Set
open scoped BigOperators Topology ENNReal Classical ContDiff Matrix
variable {D k:ℕ}
lemma basic4(x:E4): (∑ i:Axis, x i • basis i)=x:=by simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,basis] using (EuclideanSpace.basisFun Axis ℝ).sum_repr x
lemma views (f g:ContinuousMultilinearMap ℝ (fun _:Fin k=> E4) ℝ)(he:∀ b: Fin k→ Axis,f (basis ∘ b)=g (basis ∘ b)): f=g:= by
    ext1 u; have hy:u= fun i=>∑ a:Axis,u i a • basis a:=funext fun i=>(basic4 _).symm
    rw [hy,f.map_sum (fun i a=> u i a •basis a),g.map_sum (fun i a=>u i a •basis a)]; simp_rw [ContinuousMultilinearMap.map_smul_univ]; exact Finset.sum_congr rfl (fun i _=> congr_arg (_ • ·) (he i))
-- sign +1 means reflect above +1/2. sign -1 reflect below -1/2

def ε (b:Bool):ℝ:= if b then 1 else -1
def border (b:Bool):ℝ:= ε b/2
variable (a : Axis)(b: Bool)(r:ℝ)
def shadeP (a:Axis):E4→L[ℝ]ℝ:=EuclideanSpace.proj a
def slideD : E4→L[ℝ]E4:= ContinuousLinearMap.id ℝ E4 + (r-1) • (shadeP a).smulRight (basis a)
-- offset

def jostle (x:E4):E4:=(border b*(1-r)) • basis a + slideD a r x
lemma slide_read (x:E4): slideD a r x=x+(r-1) • (x a • basis a):=rfl
lemma jostle_one (x:E4): jostle a b r x a=border b+r*(x a-border b):= by
   simp only [jostle,slide_read, PiLp.add_apply, PiLp.smul_apply, basis_eq,if_true,smul_eq_mul];ring
lemma jostle_else (x:E4) {i: Axis}(h:i≠a): jostle a b r x i=x i:=by simp [jostle,slide_read,h]
lemma jostle_border (x:E4)(h:x a=border b) : jostle a b r x=x:=by
   apply PiLp.ext; intro i; by_cases hv:i=a
   · subst i; rw [jostle_one,h];ring
   exact jostle_else a b r x hv

def useBasis (f: Garden D): Garden D:= ⟨f.val∘jostle a b r,(show ContDiff ℝ D f.val from f.property).comp (show ContDiff ℝ D (jostle a b r) from contDiff_const.add (slideD a r).contDiff)⟩
lemma whisper (i:Axis):slideD a r (basis i) = (if a=i then r else (1:ℝ)) • basis i:= by
    rw [slide_read]; by_cases h:a=i
    · subst i; rw [basis_eq,if_pos rfl,if_pos rfl,one_smul,sub_smul,one_smul];abel
    simp [basis_eq, h]
-- punctual derivative word
lemma folded (f:Garden D)(x:E4)(u:Brush D): halo (useBasis a b r f) u x = (r^((Finset.univ.filter (fun i=> a=u.2 i)).card)) * halo f u (jostle a b r x) := by
    let y:=(border b*(1-r)) • basis a; let g (x:E4):= f.val (y+x)
    change iteratedFDeriv ℝ u.1.val (g ∘ slideD a r) x (basis ∘ u.2)=_; rw [(slideD a r).iteratedFDeriv_comp_right (show ContDiff ℝ u.1.val g from (tends f u.1).comp (contDiff_const.add contDiff_id)) _ le_rfl,ContinuousMultilinearMap.compContinuousLinearMap_apply]; simp_rw [Function.comp_apply,whisper,ContinuousMultilinearMap.map_smul_univ]; unfold g; rw [iteratedFDeriv_comp_add_left]; rw [show (∏ i: Fin u.1.val, if a=u.2 i then r else 1) = _ from (show _= r^((Finset.univ.filter (fun i:Fin u.1.val=> a=u.2 i)).card) from (by rw [←Finset.prod_filter,Finset.prod_const]))]; rfl
end YM.FormalBulk08.Annex
