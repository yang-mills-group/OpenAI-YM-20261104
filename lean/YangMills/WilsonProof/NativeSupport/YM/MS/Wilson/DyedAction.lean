import YM.MS.Wilson.DyedAction
import YM.MS.Wilson.Painter
import YM.MS.Wilson.PortLin
/-!
# G color symmetry before H rotation

As operator fields on both ends. Matrix ∆ remains basis-independent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Paint
open Function Set Filter Finset Plane Koszul Cylinder Lab Taylor Bare Focus Landau Sew Chart Draft
open Lattice Color
open scoped Topology ContDiff
variable {G:Gauge} {P I:Type} (u:G.El)
local notation "T"=> weight u
local notation "C"=> CI G
-- conductor coset sums reusable
lemma transposed (i j:C): ∑ a, wc u i a * wc u j a= if i=j then 1 else 0:= by simp_rw [wc_conjugate u j,← wc_group]; simp
lemma shuffle4 (F:C→C→C→C→Dot G P) : ∑ i,∑ j,∑ k,∑ l,F i j k l = ∑ k,∑ l,∑ i,∑ j,F i j k l := by
   -- perm: lift pair product
   have he : ∑ k:C×C,∑ j:C×C, F k.1 k.2 j.1 j.2=∑ j:C×C,∑ k:C×C,F k.1 k.2 j.1 j.2:= Finset.sum_comm
   simpa only [Fintype.sum_prod_type] using he

def Circ (F:CI G → Dot G P): Prop:= ∀ u:G.El, ∀ k,dye u (F k)=∑ j:C,wc u j k • F j
lemma cog_c (x:P): Circ (G:=G) (cog x):= by
   intro u i; simp only [cog,map_sum,map_smul,pigment,GH_dye, LinearMap.sum_apply,LinearMap.smul_apply, Finset.smul_sum];
   rw [shuffle4]; conv_rhs => rw [Finset.sum_comm] -- need trace to see order inner
   simp_rw [smul_smul]
   rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro a _; conv_rhs =>rw [Finset.sum_comm]
   apply Finset.sum_congr rfl; intro b _; simp_rw [← Finset.sum_smul]; congr 1
   have hu j k : -(letterLie j k i:ℂ)/2*(wc u b k * wc u a j)= - (1/2:ℂ)* (weight u a j*weight u b k *letterLie j k i:ℝ) := by push_cast [wc]; ring
   have hv j : wc u j i * (-(letterLie a b j:ℂ)/2)=-(1/2:ℂ) * (letterLie a b j*weight u j i:ℝ) := by push_cast [wc]; ring
   simp_rw [hu,hv,← Finset.mul_sum, ← Complex.ofReal_sum,tensorT]  -- T notation refers u? shadow issue

lemma stems (a b:C)(J:C→Maurer.Ends G)(hJ:∀ i:C, ∑ j:C,T i j • J j=Prod.map (G.adjoint u) (G.adjoint u) (J i)): (∑ j:C,T a j • (vel (J j) b ∘ G.adjoint u))=ᶠ[𝓝 0]∑ j:C,T j b • vel (J a) j:= by
    obtain ⟨r,hr,h⟩:=LocalH.geom_patch G;
    filter_upwards [Metric.ball_mem_nhds (0:G.Color) hr] with v hv; have he := Maurer.runvolt (J a) (h r (le_refl r)) hv u -- order?
    rw [← hJ] at he; replace he:=congr_arg (fun x:G.Color=> x b) he; unfold Maurer.volts at he; simp only [map_sum,map_smul,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,acts_all] at he
    rw [Finset.sum_apply,Finset.sum_apply]; exact he
lemma turn_steer (x:P) (i:C)(q: Edge P)(J:C→ Maurer.Ends G)(hJ:∀ i:C, ∑ j:C,T i j • J j=Prod.map (G.adjoint u) (G.adjoint u) (J i)) : dye u (steerA x i q J)=∑ j:C,wc u j i • steerA x j q J:= by
    let T' := (G.adjoint u).toContinuousLinearMap; have he (b:CI G) : germ (vel (J b) i∘G.adjoint u):= ContDiffAt.comp (g:=vel (J b) i) (f:=⇑T') 0 (by rw [map_zero]; exact vel_germ ..) T'.contDiff.contDiffAt
    simp only [steerA,map_sum,pigment,GH_dye,byedge u q _ (vel_germ _ i), map_smul,LinearMap.sum_apply,LinearMap.smul_apply, Finset.smul_sum]
    rw [Finset.sum_comm]; conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _=>?_); have hL : ∑ j:C, wc u k j • onedge q (vel (J j) i ∘ G.adjoint u) = ∑ j:C, wc u j i • onedge q (vel (J k) j):= by
       have hv := edge_swap q (stems u k i J hJ)
       rw [edge_sum q _ (fun j _=> show germ (T k j • (vel (J j) i ∘ G.adjoint u)) from (he j).const_smul (T k j)),edge_sum q _ (fun j _=> show germ (T j i • vel (J k) j) from (vel_germ _ j).const_smul (T j i))] at hv; simp_rw [edge_scale q _ (he _),edge_scale q _ (vel_germ _ _)] at hv; exact hv
    have ht:= congr_arg (couple DotFlip (GH k x)) hL; simpa only [map_sum,map_smul] using ht
lemma breathC [AddCommGroup P](d:Chart.Rail P)(x:Edge P): Circ (G:=G) (throat d x):= by
    intro u i
    unfold throat; simp_rw [map_add,smul_add,Finset.sum_add_distrib]
    congr 1
    all_goals apply turn_steer _; intro w
    all_goals apply Prod.ext <;> first | solve | simp [leftStem,rightStem,Prod.fst_sum,Prod.snd_sum]| simpa [leftStem,rightStem,Prod.fst_sum,Prod.snd_sum] using paletteC u w -- placeholder

-- Color tensor H sum contraction, for arbitrary ops commutation later
section
variable {E E' V :Type}[AddCommMonoid E][Module ℂ E][AddCommMonoid E'][Module ℂ E'][AddCommMonoid V][Module ℂ V]
lemma bilateral (L:E→ₗ[ℂ] E'→ₗ[ℂ] V)(f:C→E)(H:C→E') : ∑ i:C,L (∑ j,wc u j i • f j) (∑ j,wc u j i • H j)=∑ i,L (f i) (H i):= by
    -- order of sums after simp
    simp only [map_sum,map_smul,LinearMap.smul_apply,LinearMap.sum_apply,Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]; simp_rw [← Finset.sum_smul,transposed]; simp [ite_smul]
end
lemma combine (u:G.El)(F H:C→ Dot G P)(hf:Circ F)(hh:Circ H): dye u (∑ i:C,couple DotFlip (F i) (H i))=∑ i:C,couple DotFlip (F i) (H i) := by simp_rw [map_sum,pigment,hf u,hh u]; exact bilateral u _ _ _
lemma centerB [AddCommGroup P](d:Chart.Rail P)(x:P): Colorless (bosons G d x):= by
    intro u; unfold bosons; rw [map_add,originW d x u]; unfold ropes; rw [map_sub];
    have he b : dye u (∑ i:C,couple DotFlip (AHplus i (x,b)) (throat d (x,b) i)) = _:= combine u _ _ (fun j i=> AHP_dye j i (x,b)) (breathC d (x,b))
    have hg := combine u _ _ (fun j i=> GHP_dye j i x) (cog_c x)
    rw [map_sum]; simp_rw [he,hg]

end YM.MS.Native.Paint
