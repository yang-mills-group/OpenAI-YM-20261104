import YM.FVA2.Volumes
import YM.MSbar.Pact.HaarLink
import YangMills.WilsonProof.NativeSupport.YM.MS.Bare.Shadows
import YM.FormalOPE.RG10.Inherit.Atelier

/-!
# Suppliers for full local Landau ⇔ tree gauge bridge on the *orbit log links*

There is a single leftover global gauge. Use ordinary calculus only on the charts
near the flat orbit. The determinant proof uses left/right translated link Haar
forms locally and the equivariant splitting of the based (`Nonroot`) gauge degrees.
It is sensitive to replacing a canonical transformation with one freezing the FP
determinant, or to evaluating at an unreduced cover chart.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.TreeBasis
open FormalOPE.RG10 FormalOPE.RG10.BlockGauge
open PertExtension PertExtension.Chart MS MS.Bare MS.Bare.Maurer Function Finset
open Push.Loops Inherit Filter Set Metric Precision Volumes
open scoped Classical Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {V E : Type} {G : Gauge} {D : Loom V E} {T : D.Truss}
variable [Fintype V][Fintype E]

/-- Tree section chart, no determinants built in. -/
def treeLog (G : Gauge) (T : D.Truss) : Links E G → Free T G := Inherit.down ∘ T.bulk ∘ expLinks G E
omit [Fintype E] [Fintype V] in
lemma treeLog_zero (G : Gauge) (T : D.Truss) : treeLog G T 0=0:= by unfold treeLog; rw [Function.comp_apply,Function.comp_apply,identity_zero,Loom.Truss.bulk_one,down_one]
omit [Fintype V] in
lemma priceHot (G : Gauge) (T : D.Truss) : ContDiffAt ℝ ω (treeLog G T) 0 := down_chart (T.bulk_diff neighborhood_exp) (by rw [Function.comp_apply,identity_zero,Loom.Truss.bulk_one])
omit [Fintype V] in
lemma board_near (G : Gauge) (T : D.Truss) : ∀ᶠ u: Free T G in 𝓝 0, treeLog G T (enter G T u)=u:= by filter_upwards [down_left (G:=G) (I:=T.Bulk)] with u h; unfold treeLog; rw [Function.comp_apply,Function.comp_apply,entry_exp,Loom.Truss.bulk_board]; exact h
omit [Fintype V] in
lemma fixed_eventual (G : Gauge) (T : D.Truss) : ∀ᶠ A:Links E G in 𝓝 0, D.spin (T.frame (expLinks G E A)) (expLinks G E A)=expLinks G E (enter G T (treeLog G T A)):= by
    have he : Tendsto (T.bulk ∘ expLinks G E) (𝓝 (0:Links E G)) (𝓝 1):= by
        convert! (T.bulk_diff neighborhood_exp).continuousAt.tendsto using 2; rw [Function.comp_apply,identity_zero,Loom.Truss.bulk_one]
    filter_upwards [he.eventually (down_right (G:=G) (I:=T.Bulk))] with A h
    rw [entry_exp,show expLinks G T.Bulk (treeLog G T A)=T.bulk (expLinks G E A) from h,Loom.Truss.board_bulk]; rfl

-- finite root action near slice

def θLink (G : Gauge) (x : G.El) (y : G.El) (a : G.Color) := LocalH.snap G (x*G.lieExp a*y⁻¹)
def θFull (g : V→G.El) (A : Links E G) := Inherit.down (D.spin g (expLinks G E A))  -- D not explicit; expose for notation

omit [Fintype E] [Fintype V] in
lemma turns_here (g : V→G.El) (A : Links E G) (i:E) : θFull (D:=D) g A i= θLink G (g (D.fromEdge i)) (g (D.toEdge i)) (A i) := rfl

omit [Fintype V] [Fintype E] in
lemma θ_hot (P : Set G.El) (s : Set G.Color) (H:LocalH.Geom G P s) (u v : G.El) {a:G.Color}(h:u*G.lieExp a*v⁻¹∈P):
    ContDiffAt ℝ ω (θLink G u v) a:= by
    unfold θLink LocalH.snap; exact (H.2.2.2.2.2.2 _ h).comp (f:=fun a=> G.mat (u*G.lieExp a*v⁻¹)) _ ((contDiffAt_const.mul G.exp_jet.contDiffAt).mul contDiffAt_const) -- definal maybe
omit [Fintype V] in
lemma differential (g : V→G.El) (A : Links E G) (he : ∀ i, ContDiffAt ℝ ω (θLink G (g (D.fromEdge i)) (g (D.toEdge i))) (A i)) :
    HasFDerivAt (θFull (D:=D) g) (ContinuousLinearMap.pi (fun i=> (fderiv ℝ (θLink G (g (D.fromEdge i)) (g (D.toEdge i))) (A i)) ∘L ContinuousLinearMap.proj i)) A := hasFDerivAt_pi.mpr (fun i=> (HasFDerivAt.comp (g:=θLink G (g (D.fromEdge i)) (g (D.toEdge i))) (f:= (ContinuousLinearMap.proj i : Links E G →L[ℝ] G.Color)) A (((he i).differentiableAt (by simp)).hasFDerivAt) ( (ContinuousLinearMap.proj i : Links E G →L[ℝ] G.Color).hasFDerivAt ))) -- definal

omit [Fintype V] in
lemma root_flow (g : V→G.El) (A : Links E G) (T : D.Truss) (P : Set G.El) (s : Set G.Color) (H:LocalH.Geom G P s) (hr:g D.origin=1) (hs:∀ i,D.spin g (expLinks G E A) i∈ P):
    treeLog G T ∘ (θFull (D:=D) g)=ᶠ[𝓝 A] treeLog G T:= by
    have hp (i:E): Continuous (fun v:Links E G=> D.spin g (expLinks G E v) i):= by unfold Loom.spin expLinks; fun_prop
    filter_upwards [Filter.eventually_all.mpr (fun i=> (hp i|>.tendsto A).eventually (H.1.mem_nhds (hs i)))] with x hx
    unfold treeLog; simp only [Function.comp_apply]; rw [show expLinks G E (θFull (D:=D) g x)=D.spin g (expLinks G E x) from funext fun i=> H.2.2.2.1 (hx i)]
    apply congr_arg Inherit.down; exact funext fun i=> congr_fun (T.identify _ g hr) i.val

omit [Fintype E] [Fintype V] in
lemma right_spin (g : V→G.El) (A : Links E G) (P : Set G.El) (s : Set G.Color) (H:LocalH.Geom G P s) (hs:∀ i,D.spin g (expLinks G E A) i∈ P):
    expLinks G E (θFull (D:=D) g A)=D.spin g (expLinks G E A):= funext fun i=> H.2.2.2.1 (hs i)

omit [Fintype V] in
lemma det_hFlow (g : V→G.El) (A : Links E G) (P : Set G.El) (s : Set G.Color) (H:LocalH.Geom G P s) (U:ChartRatio G) (hu:LocalRatio U)
    (ha:∀ i,A i∈ball 0 U.radius) (hs:∀ i,D.spin g (expLinks G E A) i∈ P)
    (hw:∀ i, θFull (D:=D) g A i∈ball 0 U.radius) :
    ∏ i,U.J (A i)=(∏ i,U.J (θFull (D:=D) g A i))* |(fderiv ℝ (θFull (D:=D) g) A).det|:= by
    let C (i:E) := θLink G (g (D.fromEdge i)) (g (D.toEdge i))
    let F (i:E):= fderiv ℝ (C i) (A i)
    have he i: ContDiffAt ℝ ω (C i) (A i):= θ_hot _ _ H _ _ (hs i)
    rw [ (differential g A (D:=D) he).fderiv, show (ContinuousLinearMap.pi (fun i:E => F i ∘L ContinuousLinearMap.proj i)).det=_ from LinearMap.det_pi (fun i=> (F i).toLinearMap), Finset.abs_prod, ← Finset.prod_mul_distrib] -- scalar?
    refine Finset.prod_congr rfl fun i _=> Eq.symm (MSBar.Pact.aperture (T:=C i) hu (ha i) (hw i) ((he i).differentiableAt (by simp)) (g (D.fromEdge i)) (g (D.toEdge i))⁻¹ ?_)
    exact ((((continuous_const.mul G.lieExp_cont).mul continuous_const).continuousAt (x:=A i)).eventually (H.1.mem_nhds (hs i))).mono (fun _ h=> H.2.2.2.1 h) -- shape

end YM.FVA2.TreeBasis
