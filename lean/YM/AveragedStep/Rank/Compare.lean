import YM.Next.FOUNDATIONS.LinkBounds
import YM.AveragedStep.Orders.Grant
import YM.Progress.STATIONARY_SCENES.SliceGap
/-! # Symbolic gap for the paired SD solve
Must compare on exactly the `F.Free` sector (coarse pinned), else no gap even
at the cutoff. Reconcile both the Taylor normalization and the link lifting
(no pull on the pins) with Wilson supplies.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AveragedStep
open Filter Function Lattice RG Loops Tree Wilson Precision Metric Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical InnerProductSpace
open Matrix Push.Uniform
open PertExtension.Series.Radial
variable {c f:Side}{G:Gauge}{S:StepData c f}

-- linear cost for representing fields on drape with zero pins
-- call our directions `Hand` == Rim c f -> G.Color
-- `AxisChart` of Precision counts ℓ² on each free edge and uses Pi norm across edges

def bridge (p:Parcel c f):Hand G c f→L[ℝ] Vectors S.patch G:= LinearMap.toContinuousLinearMap
    ({toFun:=pick (S:=S) p
      map_add':=by intro x y; funext i; unfold pick; cases he:hook S p i <;> simp [Option.elim,he]
      map_smul':=by intro t X; exact pick_smul p X t} : Hand G c f→ₗ[ℝ] Vectors S.patch G)

def back (F:Forest S.ratio):AxisChart G F→L[ℝ] Hand G c f:= LinearMap.toContinuousLinearMap
   ({toFun:=fun X=>Sum.elim (fun i:Edge (Site f)=>if h:i∈F.trunks then 0 else X ⟨i,h⟩) (fun _=>0)
     map_add':=by intro x y; funext i; rcases i with i|i; dsimp only [Sum.elim_inl,Pi.add_apply]; split <;> simp; simp
     map_smul':=by intro t x; funext i; rcases i with i|i; dsimp only [Sum.elim_inl,Pi.smul_apply]; split <;> simp; simp} : AxisChart G F→ₗ[ℝ] Hand G c f)

lemma back_take (F:Forest S.ratio)(j:Key F G):
    back F (Precision.frame F j)= Pi.single (Sum.inl j.1.val:Rim c f) (fingers G j.2):=by
 funext i; rcases i with i|i
 · change (if h:i∈F.trunks then 0 else Precision.frame F j ⟨i,h⟩)=_
   by_cases he:i=j.1.val
   · subst i; rw [dif_neg j.1.property,Pi.single_eq_same]; unfold Precision.frame; rw [Pi.single_eq_same]
   split
   · rw [Pi.single_eq_of_ne (by simpa using he)]
   next h=> unfold Precision.frame; rw [Pi.single_eq_of_ne (show (⟨i,h⟩:F.Free)≠j.1 by rintro hx; exact he (congrArg Subtype.val hx)),Pi.single_eq_of_ne (by simpa using he)]
 change 0= _; simp

lemma tooths {P:Patch}{K:KernelChoices}(h:P.Branches K G)(p:Mold)(i j: Vectors P G) :tooth P (K:=K) p i 1 j=fderiv ℝ (fderiv ℝ (chip P K p (canon P))) 0 j i:=by
 let L:=fderiv ℝ (chip P K p (canon P) (G:=G))
 have hf:ContDiffAt ℝ ω L 0 := ((smooth_chip P K h p (canon P)).1.fderiv_right (m:=ω) (by simp))
 unfold tooth jet
 rw [iteratedFDeriv_one_apply]
 have he : fderiv ℝ (fun y:Vectors P G=>L y i) 0 j=fderiv ℝ L 0 j i := by
    rw [((hf.differentiableAt (by simp)).hasFDerivAt.clm_apply (u:=fun y:Vectors P G=>i) (hasFDerivAt_const ..)).fderiv]
    simp
 change (↑(Nat.factorial 1):ℝ)⁻¹* fderiv ℝ (fun y=>L y i) 0 j=fderiv ℝ L 0 j i; rw [he]; norm_num [Nat.factorial]

lemma pick_zero {e:Rim c f}(p:Parcel c f)(h:p∉ owners S e)(v:G.Color): pick (S:=S) p (Pi.single e v)=0:=by
 funext i; unfold pick; cases he:hook S p i; rfl
 next j=> exact Pi.single_eq_of_ne (show j≠e by rintro rfl; exact h (own_member S (land_mem S he))) _

def tabulate (S:StepData c f) : Hand G c f→ℝ:= fun Y=>∑ p:Parcel c f,chip S.patch S.kernel (sort p) (canon S.patch) (pick (S:=S) p Y)
def tagulate (S:StepData c f)(k:S.Choices): Hand G c f→ℝ:= fun Y=>∑ p:Parcel c f,chip S.patch S.kernel (sort p) (leads S k p) (pick (S:=S) p Y)
lemma germ_tabulate (h:S.patch.Branches S.kernel G)(k:S.Choices):
    tabulate S (G:=G)=ᶠ[𝓝 0] tagulate S (G:=G) k := by
 have he(p:Parcel c f):∀ᶠ Y:Hand G c f in 𝓝 0,chip S.patch S.kernel (sort p) (canon S.patch) (pick (S:=S) p Y)=chip S.patch S.kernel (sort p) (leads S k p) (pick (S:=S) p Y):=by
   have hn: Tendsto (bridge (S:=S) (G:=G) p) (𝓝 0) (𝓝 0):=by simpa only [map_zero] using (bridge (S:=S) (G:=G) p).continuous.tendsto 0
   exact hn.eventually (common_chip S.patch S.kernel h _ _ _)
 filter_upwards [eventually_all.mpr he] with i he
 unfold tabulate tagulate; simp_rw [he]

-- scalar assembly in full V+W coordinates, includes anchored owners
lemma tab_price (h:S.patch.Branches S.kernel G)(A:ChartRatio G)(z:Ink G c f)(Y:Hand G c f):
    tier S A z.1 (fingers G z.2) 0 Y=iteratedFDeriv ℝ 2 (tabulate S (G:=G)) 0 ![Y,Pi.single z.1 (fingers G z.2)]:=by
 let D(p:Parcel c f):=chip S.patch S.kernel (sort p) (canon S.patch) (G:=G)
 let L(p:Parcel c f):=bridge (G:=G) (S:=S) p
 have hl (p:Parcel c f) : ContDiffAt ℝ 2 (D p) (L p (0:Hand G c f)):=by rw [map_zero]; exact (smooth_chip S.patch S.kernel h _ _).1.of_le le_top
 have hv(p:Parcel c f):ContDiffAt ℝ 2 (D p ∘ L p) 0:= (hl _).comp 0 (L p).contDiff.contDiffAt
 rw [tier,backbone]; rw [if_pos rfl,sub_zero]
 let i:Hand G c f:=Pi.single z.1 (fingers G z.2)
 rw [show tabulate (G:=G) S=(fun Y=>∑ p:Parcel c f,(D p∘ L p) Y) from rfl,
     iteratedFDeriv_fun_sum_apply (n:=2) (fun p _=>hv p)] -- name?
 -- rotate goals etc
 have he(p):iteratedFDeriv ℝ 2 (D p ∘ L p) 0 ![Y,i] = fderiv ℝ (fderiv ℝ (D p)) 0 (pick (S:=S) p Y) (pick (S:=S) p i):=by
   rw [Next.Foundations.jets_linear (L p) (show ContDiffAt ℝ 2 (D p) 0 from by simpa only [map_zero] using hl p), ContinuousMultilinearMap.compContinuousLinearMap_apply, iteratedFDeriv_two_apply]; rfl
 change _ = (∑ p,iteratedFDeriv ℝ 2 (D p ∘ L p) 0) ![Y,i]
 simp_rw [_root_.sum_apply,he]
 refine (Finset.sum_subset (Finset.subset_univ _) (f:=fun p=>tooth S.patch (K:=S.kernel) (sort p) (pick (S:=S) p i) 1 (pick (S:=S) p Y)) ?_).trans ?_
 · intro p _ hp; rw [tooths h, pick_zero p hp, map_zero]
 exact Finset.sum_congr rfl (fun p _=>tooths h ..)

def display (F:Forest S.ratio)(X:AxisChart G F):Board G c f:=(lifting F (represent 0) X,1)
lemma display_link (F:Forest S.ratio)(X:AxisChart G F):Sum.elim (display F X).1 (display F X).2=(fun i=>G.lieExp (back F X i)):=by
 funext i; rcases i with i|i
 · change lifting F (represent 0) X i=_; rw [Precision.link_one]; by_cases h:i∈F.trunks
   · rw [lifting, show F.drape _ i=1 from F.on_tree _ ⟨i,h⟩]; change _= G.lieExp (if h:i∈F.trunks then 0 else X ⟨i,h⟩); rw [dif_pos h,G.mat_lieExp_zero]
   change _=G.lieExp (if h:i∈F.trunks then 0 else X ⟨i,h⟩); rw [dif_neg h,lifting,F.off_tree (i:=⟨i,h⟩),Precision.replica_one,Pi.one_apply,mul_one]
 exact G.mat_lieExp_zero.symm
lemma coded (F:Forest S.ratio)(k:S.Choices)(X:AxisChart G F)(p:Parcel c f):temperature S k p (display F X)=chip S.patch S.kernel (sort p) (leads S k p) (pick (S:=S) p (back F X)):=by
 unfold temperature chip; apply congr_arg; rw [display_link]
 funext i; change aim (fun i=> G.lieExp (back F X i)) (hook S p i)=G.lieExp (pick (S:=S) p (back F X) i); unfold aim pick; cases hook S p i; · exact G.mat_lieExp_zero.symm
 rfl
lemma polymerize (h:S.patch.Branches S.kernel G)(k:S.Choices)(F:Forest S.ratio) : (tested (S:=S) F k firstClip (wil G) 0)= tagulate S k ∘ (back F):=by
 funext X; simp only [Function.comp_apply,tagulate]; simp_rw [← coded F k X]
 rw [tested, initial_main (he:=rfl),Fintype.sum_sum_type]; apply congrArg₂ (·+·)
 · simp_rw [(terrace_face S h ..).1]; rfl
 unfold noiseTaylor; change _ * (∑ e:Site c×Axis,_) = ∑ a:Site c × Option Axis,_
 simp_rw [Fintype.sum_prod_type,Fintype.sum_option,(terrace_station S h ..).1]; have hE(x:Site c)(i:Axis):=(terrace_bond S h k (x,i) (display F X)).1
 simp_rw [zero_add,Finset.mul_sum,(fun x i=>hE x i)]
 rw [Precision.link_one]; unfold display; rw [Precision.link_one]

/-- Exact identification of the non-tree score matrix (the inversion direction,
NOT the full field Hessian in U,V). NB ordering of indices follows calculus
library's `iteratedFDeriv` convention; symmetry used before operator bounds. -/
def body (A:ChartRatio G)(F:Forest S.ratio): Matrix (Key F G) (Key F G) ℝ:= Matrix.of fun i j=>tier S A (.inl i.1.val) (fingers G i.2) 0 (back F (Precision.frame F j))
lemma identified (h:S.patch.Branches S.kernel G)(k:S.Choices)(F:Forest S.ratio)(A:ChartRatio G):
    body A F=(hessian F k firstClip (wil G) 0 0)ᵀ :=by
 ext i j
 change tier _ _ _ _ _ _=_
 let z:Ink G c f:= (Sum.inl i.1.val, i.2)
 change tier S A z.1 (fingers G z.2) 0 _ = _
 rw [tab_price h A z]
 have ht: ContDiffAt ℝ (2:ℕ) (tabulate S (G:=G)) 0 := ContDiffAt.sum (fun p _=>ContDiffAt.comp (g:=chip S.patch S.kernel (sort p) (canon S.patch)) (f:=(bridge (S:=S) (G:=G) p:Hand G c f→ _)) 0
    (by rw [map_zero]; exact (smooth_chip S.patch S.kernel h (sort p) (canon S.patch)).1.of_le le_top) ((bridge p).contDiff.contDiffAt))
 rw [(germ_tabulate (G:=G) h k).iteratedFDeriv ℝ 2|>.eq_of_nhds]
 change _=iteratedFDeriv ℝ 2 (tested (S:=S) F k firstClip (wil G) 0) 0 ![Precision.frame F j,Precision.frame F i]
 have hh: ContDiffAt ℝ 2 (tagulate S (G:=G) k) 0 := ht.congr_of_eventuallyEq (germ_tabulate h k).symm
 rw [polymerize h, Next.Foundations.jets_linear (back F (G:=G)) hh,ContinuousMultilinearMap.compContinuousLinearMap_apply]
 congr 1; funext p; fin_cases p; rfl
 exact (back_take F i).symm
end YM.AveragedStep
