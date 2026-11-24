import YM.Integration.WilsonThermometerWeakCornerRows
import YM.Integration.WilsonThermometerWeakCoordinateNorm
import YM.MSbar.Aqua.Quartz

/-! At separated true positions, the protected derivative letters from the
original Ward hierarchy evaluate the full real near-position differential. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerWeakCornerJets
open Finset Filter Set Function Spec Extraction Table GapsContact GapsContact.Seams
open Frontier6 Frontier6.Tale Frontier6.Road MergeProof.Acme
open PhysicalNext.Repeat.Legato
open scoped Topology Classical ContDiff BigOperators
open WilsonThermometerWeakCoordinateNorm WilsonThermometerWeakCornerRows
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book} (F:Final R.family f S)
variable {n:ℕ} {J:Type} [Fintype J]

def sites (a:ℝ)(x:Points n)(y:J→E4):Fin n⊕J→E4:= Sum.elim (fun i=>a • x i) y

def panel (q:StateIndex F)(v:Fin n→S.Tag)(w:J→S.Tag)(y:J→E4)(a:ℝ)(x:Points n):ℂ:=
  peal F q (assembly S (fun i=>a • x i) v*assembly S y w)

private lemma wider {a:ℝ}{x:Points n}{y:J→E4}(h:Injective (sites a x y)):
    ∀ᶠ z in 𝓝 x,Injective (sites a z y):=by
  apply Tale.larger (X:=Points n) _ h
  apply continuousAt_pi.mpr
  intro i
  cases i with
  | inl i=>exact (PiLp.continuous_apply 2 _ i).continuousAt.const_smul a
  | inr i=>exact continuousAt_const

theorem smooth (q:StateIndex F)(v:Fin n→S.Tag)(w:J→S.Tag)(y:J→E4)(a:ℝ)
    {x:Points n}(clear:Injective (sites a x y)):
    ContDiffAt ℝ ∞ (panel F q v w y a) x:=by
  let V:=Fin n⊕J
  let E:Fin (Fintype.card V)≃V:=(Fintype.equivFin V).symm
  let positions:=fun z:Points n=>points (sites a z y ∘ E)
  have good:positions x∈conf (Fintype.card V):=clear.comp E.injective
  have placed:ContDiff ℝ ∞ positions:=by
    change ContDiff ℝ ∞ ((PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin (Fintype.card V)=>E4)).symm ∘ _)
    apply ContDiff.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _:Fin (Fintype.card V)=>E4)).symm.contDiff
    apply contDiff_pi.mpr
    intro i
    change ContDiff ℝ ∞ (fun z:Points n=>sites a z y (E i))
    cases E i with
    | inl i=>exact (PiLp.proj (𝕜:=ℝ) 2 (fun _:Fin n=>E4) i).contDiff.const_smul a
    | inr j=>exact contDiff_const
  let tags:=Sum.elim v w
  have sampled:=((S.class_smooth (state F q) (hierarchy F q).smooth (tags ∘ E)).contDiffAt
    ((conf_open _).mem_nhds good)).comp x placed.contDiffAt
  apply sampled.congr_of_eventuallyEq
  filter_upwards [wider clear] with z hz
  change peal F q (assembly S (fun i=>a • z i) v*assembly S y w)=_
  unfold sites at hz
  rw [←Tale.concatenates, Tale.acast F q,if_pos hz]
  rfl

private lemma move (a t:ℝ)(p:Fin n×Axis)(x:Points n):
    (fun i=>a • (x+t • WilsonThermometerWeakCoordinateNorm.letter p) i)=wag (fun i=>a • x i) a p t:=by
  ext1 i
  by_cases h:i=p.1
  · subst i
    simp [wag_eq,chord,Ward.inc,WilsonThermometerWeakCoordinateNorm.letter,smul_add,smul_smul,mul_comm]
  · rw [wag_untouched _ _ _ _ _ h]
    simp [WilsonThermometerWeakCoordinateNorm.letter,h]

private lemma first (q:StateIndex F)(v:Fin n→S.Tag)(w:J→S.Tag)(y:J→E4){a:ℝ}
    {x:Points n}(p:Fin n×Axis)(clear:Injective (sites a x y)):
    HasDerivAt (fun t:ℝ=>panel F q v w y a (x+t • WilsonThermometerWeakCoordinateNorm.letter p))
      (a • panel F q (route F v p 1) w y a x) 0:=by
  have good:Injective (Sum.elim (wag (fun i=>a • x i) a p 0) y):=by
    simpa only [wag_zero,sites] using clear
  have row:=route_joint F v w good q 0
  simpa only [panel,move,trailWord,route_zero,pow_zero,one_smul,zero_add,pow_one,wag_zero] using row

private theorem line {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (x v:E):
    HasDerivAt (fun t:ℝ=>x+t • v) v 0:=by
  have h:HasDerivAt (fun t:ℝ=>t • v) ((1:ℝ) • v) 0:=(hasDerivAt_id (0:ℝ)).smul_const v
  simpa only [one_smul] using h.const_add x

/-- One common set of fields is held fixed throughout the ordered test. -/
theorem literal (q:StateIndex F)(v:Fin n→S.Tag)(w:J→S.Tag)(y:J→E4)(a:ℝ)
    (smooth:∀x,Injective (sites a x y) → ContDiffAt ℝ ∞ (panel F q v w y a) x)
    (l:List (Fin n×Axis)){x:Points n}(clear:Injective (sites a x y)):
    MSbar.Lis.roc (panel F q v w y a) (l.map WilsonThermometerWeakCoordinateNorm.letter) x =
      a^l.length • panel F q (rows F l v) w y a x:=by
  induction l generalizing x with
  | nil=>simp [MSbar.Lis.roc,rows]
  | cons p l ih=>
    let V:=MSbar.Lis.roc (panel F q v w y a) (l.map WilsonThermometerWeakCoordinateNorm.letter)
    let path:=fun t:ℝ=>x+t • WilsonThermometerWeakCoordinateNorm.letter p
    have at0:path 0=x:=by simp [path]
    have d0:=line x (WilsonThermometerWeakCoordinateNorm.letter p)
    have dV:ContDiffAt ℝ 1 V x:=by
      apply MSbar.Lis.smooth (l.length+1) 1
      · exact (smooth x clear).of_le (by exact_mod_cast le_top (a:=(l.length+1:ℕ∞)))
      · simp [Nat.add_comm]
    have same: (fun t:ℝ=>V (path t)) =ᶠ[𝓝 0] fun t=>a^l.length • panel F q (rows F l v) w y a (path t):=by
      have fits:=wider clear
      have reach:Tendsto path (𝓝 0) (𝓝 x):=at0 ▸ d0.continuousAt
      exact (reach.eventually fits).mono (fun t ht=>ih ht)
    have other:=((first F q (rows F l v) w y p clear).const_smul (a^l.length)).congr_of_eventuallyEq same
    have dx:DifferentiableAt ℝ V (path 0):=by
      rw [at0]
      exact dV.differentiableAt one_ne_zero
    have equal:=((dx.hasFDerivAt.comp_hasDerivAt 0 d0).unique other)
    simpa only [at0,MSbar.Lis.roc,List.map_cons,List.length_cons,rows,pow_succ,mul_smul] using equal

end YM.Integration.WilsonThermometerWeakCornerJets
end
