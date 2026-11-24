import YM.PertExtension.CoefficientLimit
import YM.PertExtension.PositionBranch

/-!
# Removing the leading cutoff offset, formal continuity of finite X solves

The finite leading raw arrays have not yet exactly imposed the free-position
entries. The solution here first rebases the `TestSystem` at the leading
cutoff by an exact orbital transformation; formal correction at every positive
degree then uses the same free numerical target.
-/
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
namespace YM.PertExtension.Position
open Set Filter Function PowerSeries Triangle
open scoped Topology BigOperators Classical ContDiff

variable {J P:Type*}[Fintype J]{shape:P→ℕ}

namespace AlignSeries
theorem array {α}{l:Filter α} {A : α→Mark J shape→fps}{B : Mark J shape→fps}{K:α→FrameAt J fps}{H:FrameAt J fps}(h:∀ i,AlignSeries l (fun v=>A v i) (B i))
    (hk:∀ i j,AlignSeries l (fun v=>K v i j) (H i j))(u:Mark J shape): AlignSeries l (fun v=> insert J shape (A v) (K v) u) (insert J shape B H u) :=
  AlignSeries.sum _ _ fun _=> (h _).mul (AlignSeries.prod _ _ _ fun _ _ => hk _ _)
end AlignSeries

namespace TestSystem
variable (D:TestSystem J P shape)
def leadingAdjust (a₀ b : Mark J shape→ℝ) : TestSystem J P shape :=
    {D with baseline:=D.baseline+(D.branch a₀ (b ∘ markIn D.tests)).val}

def positioned (D:TestSystem J P shape)(a: Mark J shape → fps) :=
    insert J shape a (D.position a)

lemma shifted_deriv (a : Mark J shape→ℝ){b : D.Z}(A : TestSystem J P shape) (v:D.Z) (hZ:A.Z=D.Z)
    (hv : A.baseline=D.baseline+b.val) (hA : ∀ (x:D.Z)(q:Mark J shape→ℝ), (D.lieResult (q ∘ markIn _) (x+b)).val = (A.lieResult (q ∘ markIn _) (hZ ▸ x)).val) :
    fderiv ℝ D.solver (a ∘ markIn D.tests,b) (0,v)=(0,hZ ▸ A.inspect a (hZ ▸ v)) := by
  cases D with | mk Z p sel baseline target=>
   cases A with | mk Y r get B goal=>
    change Y=Z at hZ; subst Y
    let D : TestSystem J P shape := ⟨Z,p,sel,baseline,target⟩
    let A : TestSystem J P shape := ⟨Z,r,get,B,goal⟩
    let f := fderiv ℝ D.solver (a ∘ markIn D.tests,b)
    let L := ContinuousLinearMap.inr ℝ D.Parameter D.Z
    have h : HasFDerivAt (fun u=>D.solver ((a ∘ markIn D.tests, b) + L u)) (f.comp L) 0 := by
      have he := (D.smooth_solve.differentiable (by simp)) (a ∘ markIn D.tests,b) |>.hasFDerivAt
      have hl : HasFDerivAt (fun u=>(a ∘ markIn D.tests, b) + L u) L 0 := by convert L.hasFDerivAt.const_add _
      exact ((by simpa using he) : HasFDerivAt D.solver f ((a ∘ markIn D.tests,b)+L 0)).comp (g':=f) (0:D.Z) hl
    let g : ↥Z →L[ℝ] Z := LinearMap.toContinuousLinearMap (A.inspect a)
    have hZA (u:Z): D.lieResult (a ∘ markIn p) (u+b) = A.lieResult (a ∘ markIn r) u := Subtype.ext (hA u a)
    have hz : HasFDerivAt (fun u=> (a ∘ markIn p,D.lieResult (a ∘ markIn p) (u+b))) ((0:(↥Z) →L[ℝ] D.Parameter).prod g) 0 := by
      simp_rw [hZA]
      convert! (hasFDerivAt_const (a ∘ markIn p) (0:Z)).prodMk (((A.lieResult_contDiff (a ∘ markIn r)).differentiable (by simp) (0:Z)).hasFDerivAt)
    rw [show (fun u:Z=>D.solver ((a ∘ markIn D.tests,b)+L u))=(fun u=> (a ∘ markIn p,D.lieResult (a ∘ markIn p) (u+b))) by funext u; simp [solver,L,add_comm,D]] at h
    have hh := DFunLike.congr_fun (h.unique hz) v
    exact hh

variable {α : Type*}(b : Mark J shape→fps)(A:α→Mark J shape→fps){l : Filter α}(hb : D.Regular (fun i=>constantCoeff (b i)))
variable (hA : ∀ i,AlignSeries l (fun v=>A v i) (b i))

private abbrev free := fun i=>constantCoeff (b i)
private abbrev qData (v:α): D.Parameter:=fun i=>constantCoeff (A v (markIn _ i))
abbrev systemAt (v:α):=D.leadingAdjust (free b) (fun i=>constantCoeff (A v i))

include hb hA
lemma pair_tends : Tendsto (fun t=> (qData D A t,D.branch (free b) (qData D A t))) l (𝓝 (free b ∘ markIn D.tests, (0:D.Z))) :=
  (D.tends (free b) hb).comp (tendsto_pi_nhds.mpr (fun i=>by unfold qData; simpa using hA (markIn D.tests i) 0))

theorem leading_achieved : ∀ᶠ i : α in l, (D.systemAt b A i).Regular (fun j=>constantCoeff (A i j)) := by
  filter_upwards [(D.pair_tends b A hb hA).fst_nhds.eventually (D.solves (free b) hb),
    (D.pair_tends b A hb hA).eventually (D.eventually_fullrank (free b) hb)] with u hv' hu
  constructor
  · exact hv'
  obtain ⟨u₁,u₂⟩:=hu
  let L :=fderiv ℝ D.solver (qData D A u,D.branch (free b) (qData D A u))
  change Injective L at u₁
  let J := D.systemAt b A u
  have he (z:D.Z): L (0,z) = (0,(J.inspect (fun j=>constantCoeff (A u j))) z):= by
    have := D.shifted_deriv (b:=D.branch (free b) (qData D A u)) (fun j=>constantCoeff (A u j)) J z rfl rfl (fun x p=>by
       change ((D.result (p ∘ markIn D.tests) (D.baseline+(x+ _).val)):FrameAt _ ℝ)=(D.result _ _).val
       simp only [Submodule.coe_add,J,systemAt,leadingAdjust]
       congr 2; abel)
    exact this
  have hj : Injective (J.inspect (fun i=>constantCoeff (A u i))) := fun x y h=> congr_arg Prod.snd (u₁ (show L (0,x)=L (0,y) by rw [he,he,h]))
  exact ⟨hj,LinearMap.injective_iff_surjective.mp hj⟩

-- Continuity needed for inversion of the test derivative in the recursion.
lemma converges_tests : Tendsto (fun i=> LinearMap.toContinuousLinearMap ((systemAt D b A i).inspect (fun j=>constantCoeff (A i j)))) l (𝓝 (LinearMap.toContinuousLinearMap (D.inspect (free b)))) := by
   let S (p:Mark J shape→ℝ)(y:D.Z): D.Z →L[ℝ] D.Z :=
     (ContinuousLinearMap.snd ℝ D.Parameter D.Z).comp ((fderiv ℝ D.solver (p ∘ markIn D.tests,y)).comp (ContinuousLinearMap.inr ℝ D.Parameter D.Z))
   let R i := S (fun j=>constantCoeff (A i j)) (D.branch (free b) (qData D A i))
   have h : Tendsto R l (𝓝 (S (free b) 0)) := by
      exact continuous_const.clm_comp ((D.smooth_solve.continuous_fderiv (by simp)).clm_comp continuous_const) |>.tendsto _ |>.comp (D.pair_tends b A hb hA)
   have ht : S (free b) 0 = LinearMap.toContinuousLinearMap (D.inspect (free b)) :=
      ContinuousLinearMap.ext fun v=>congr_arg Prod.snd (D.solve_fderiv (free b) v)
   rw [ht] at h
   refine h.congr fun v=>ContinuousLinearMap.ext fun z=> congr_arg Prod.snd
      (D.shifted_deriv (b:=D.branch (free b) (qData D A v)) _ (systemAt D b A v) z rfl rfl (fun x q=>?_) )
   change ((D.result (q ∘ markIn D.tests) (D.baseline+(x+ _).val)):FrameAt J ℝ)=(D.result _ _).val
   simp only [Submodule.coe_add,systemAt,leadingAdjust]
   congr 2; abel

private theorem inverse_cont {t:α→D.Z}(t₀:D.Z)(ht:Tendsto t l (𝓝 t₀)) :
    Tendsto (fun i=> (D.systemAt b A i).repair (A i) (t i)) l (𝓝 (D.repair b t₀)) := by
  let L : D.Z →L[ℝ] D.Z := LinearMap.toContinuousLinearMap (D.inspect (free b))
  let P (i:α): D.Z →L[ℝ] D.Z:= LinearMap.toContinuousLinearMap ((D.systemAt b A i).inspect (fun j=>constantCoeff (A i j)))
  have hL : IsUnit L:= ContinuousLinearMap.isUnit_iff_bijective.mpr (by apply hb.rank)
  have hp : Tendsto P l (𝓝 L):=D.converges_tests b A hb hA
  obtain ⟨v,hv⟩:=hL; have hx := NormedRing.inverse_continuousAt (R:=D.Z →L[ℝ] D.Z) v
  have hu := D.leading_achieved b A hb hA
  rw [← hv] at hp
  have hc:=((continuousAt_fst.clm_apply continuousAt_snd).tendsto).comp ((hx.tendsto.comp hp).prodMk_nhds ht)
  have he : Ring.inverse v.val t₀ = D.repair b t₀ := by
     refine hb.rank.injective (show L _=L _ from ?_)
     have hH : v.1 (Ring.inverse v.val t₀)=t₀ := DFunLike.congr_fun (Ring.mul_inverse_cancel _ v.isUnit) t₀
     rw [hv,repair,dif_pos hb.rank];exact (show _ from (hv ▸ hH).trans ((LinearEquiv.ofBijective _ hb.rank).apply_symm_apply ..).symm)
  change Tendsto (fun t' : α=> Ring.inverse (P t') (t t')) _ _ at hc
  rw [he] at hc -- adjust
  refine Tendsto.congr' (f₁:=fun t'=>Ring.inverse (P t') (t t')) (hu.mono fun i hi=>?_) hc
  change (Ring.inverse (P i)) (t i)=(D.systemAt b A i).repair (A i) (t i)
  refine hi.rank.injective (show P i _=P i _ from ?_)
  have hP := ContinuousLinearMap.isUnit_iff_bijective.mpr (show Bijective (P i) from hi.rank)
  have ht : P i ((Ring.inverse (P i)) (t i))=t i:= DFunLike.congr_fun (Ring.mul_inverse_cancel _ hP) (t i)
  rw [repair,dif_pos hi.rank,ht]
  exact ((LinearEquiv.ofBijective _ hi.rank).apply_symm_apply ..).symm

theorem stack_align (n) : ∀ i j,AlignSeries l (fun v=>(D.systemAt b A v).stack (A v) n i j) (D.stack b n i j) := by
  induction n with
  | zero=>
    intro i j
    have ht := D.pair_tends b A hb hA |>.snd_nhds
    have hv : Tendsto (fun v=>D.Z.subtypeL (D.branch (free b) (qData D A v))) l (𝓝 (0:FrameAt J ℝ)):= D.Z.subtypeL.continuous.continuousAt.tendsto.comp ht
    exact AlignSeries.scalar_C _ _ (by convert! tendsto_pi_nhds.mp (tendsto_pi_nhds.mp ((tendsto_const_nhds (x:=D.baseline)).add hv |>.mono_right (le_of_eq (congr_arg 𝓝 (add_zero _)))) i) j)
  | succ n ih=>
    intro i j
    simp_rw [stack,patch]
    apply AlignSeries.add (h:=ih i j)
    apply AlignSeries.mul _ (AlignSeries.const _)
    apply AlignSeries.scalar_C
    let J v : D.Z:= (D.systemAt b A v).response (A v) ((D.systemAt b A v).stack (A v) n) (n+1)
    have hv : Tendsto J l (𝓝 (D.response b (D.stack b n) (n+1))) :=
       D.select.toContinuousLinearMap.continuous.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr fun j=> AlignSeries.array hA ih (markIn D.tests j) (n+1))
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (D.Z.subtypeL.continuous.continuousAt.tendsto.comp (D.inverse_cont _ _ hb hA _ hv.neg)) i) j

theorem positions_align : ∀ j,AlignSeries l (fun v=>(D.systemAt b A v).positioned (A v) j) (D.positioned b j) :=
  AlignSeries.array hA (fun i j k=>by simpa only [position,coeff_mk] using! D.stack_align b A hb hA k i j k)

end TestSystem
end YM.PertExtension.Position
