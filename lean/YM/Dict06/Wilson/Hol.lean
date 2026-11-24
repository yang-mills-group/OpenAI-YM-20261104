import YM.Dict06.Wilson.Section
import YM.Dict06.Series.Tower
import YM.Work.G02

/-! The log holonomy of a radial test is a genuine smooth Color/link germ on
the finite chart. Only the linear part is Drops.access;
use the full germ at positive orders. This also gives higher coefficient data by
Taylor of a specified ODE at the common Hol (independent of the physical
Family's dynamics: Hol.solves uniquely). -/
set_option autoImplicit false
noncomputable section
namespace YM.Dict06.Wil
open Series Lattice Wilson Labels Source Source.Drops Topology Function Set Filter
open scoped ContDiff Matrix.Norms.Frobenius BigOperators Classical Topology
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {d:ℕ}

def logTest (H : Hol G) (d:ℕ) (Y : Finset Cover) (J : Snap G d) : Panel Y G :=
  fun i=> G.plog (G.mat (H.links d (expand d J) 1 i.val))
lemma chart_of_links (H:Hol G) (d) (Y): ContDiffAt ℝ ω (logTest H d Y) 0 ∧ logTest H d Y 0=0 := by
  have a (i:UsedEdges Y) := YM.Work.G02.linkGerm H d i.val
  refine ⟨contDiffAt_pi.mpr (fun i=>?_),funext fun i=>?_⟩
  · let f(J:Snap G d):=G.mat (H.links d (expand d J) 1 i.val)
    change ContDiffAt ℝ ω (G.plog ∘ f) 0
    have he:f 0=1:=by unfold f; rw [(a i).2.1,G.mat_one]
    have h:=G.plog_diff
    rw [← he] at h; exact h.comp _ ((a i).1.contDiffAt)
  change G.plog (G.mat (H.links d (expand d 0) 1 i.val))=0
  rw [(a i).2.1,G.mat_one,G.plog_one]
lemma back (H:Hol G) (d:ℕ) (Y:Finset Cover) (i:UsedEdges Y):
    ∀ᶠ J:Snap G d in 𝓝 0, G.lieExp (logTest H d Y J i) = H.links d (expand d J) 1 i.val := by
  let f (J:Snap G d) := H.links d (expand d J) 1 i.val
  obtain ⟨ha,hz,h⟩:=YM.Work.G02.linkGerm H d i.val
  have hm : AnalyticAt ℝ (G.mat ∘ f) 0:=ha
  have hz : G.mat (f 0)=1 := by unfold f; rw [hz,G.mat_one]
  have he:=hm.continuousAt.tendsto
  change Tendsto (G.mat ∘ f) _ (𝓝 (G.mat (f 0))) at he
  rw [hz] at he
  have hf:Tendsto f (𝓝 0) (𝓝 1):=(G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr he
  exact hf.eventually G.plog_right

/-- Identify the linearized log input with the *actual native* positive
link integral of the radial potential. -/
lemma log_first (H:Hol G) (d:ℕ) (Y:Finset Cover) (J:Snap G d) (i:UsedEdges Y):
    term (logTest H d Y) 1 J i = access J i.val := by
  let L:Panel Y G →L[ℝ] G.Color:= (LinearMap.proj (R:=ℝ) (φ:=fun _ : UsedEdges Y=>G.Color) i).toContinuousLinearMap
  let f (t:ℝ):= logTest H d Y (t • J)
  have hf : ContDiffAt ℝ ω f 0 := (by
    have hc: ContDiffAt ℝ ω (logTest H d Y) ((0:ℝ) • J):=by rw [zero_smul]; exact (chart_of_links H d Y).1
    exact hc.comp (f:=fun t:ℝ=>t • J) 0 (contDiffAt_id.smul contDiffAt_const))
  have hf0 : f 0=0:=by simp [f,(chart_of_links H d Y).2]
  let D (t:ℝ):=L (f t)
  have hD: D 0=0:=by rw [show D 0=L (f 0) from rfl,hf0,map_zero]
  have hd:HasDerivAt D (deriv D 0) 0:= ((L.contDiff.contDiffAt.comp (𝕜:=ℝ) (f:=f) (0:ℝ) hf).differentiableAt (by simp)).hasDerivAt
  obtain ⟨_,_,he⟩:=YM.Work.G02.linkGerm H d i.val
  apply G.colorMat_injective
  have hroy : HasDerivAt (fun t:ℝ=>G.mat (G.lieExp (D t))) (G.colorMat (deriv D 0)) 0:=by
    have h := G.expDiff_zero; rw [← hD] at h
    exact h.comp_hasDerivAt (0:ℝ) hd
  have ht : Tendsto (fun t:ℝ=>t • J) (𝓝 0) (𝓝 0):=by simpa using! (show Continuous (fun t:ℝ=>t • J) from continuous_id.smul continuous_const).tendsto 0
  have he': (fun t:ℝ=>G.mat (H.links d (expand d (t • J)) 1 i.val)) =ᶠ[𝓝 0]
      (fun t=>G.mat (G.lieExp (D t))) := by
    filter_upwards [ht.eventually (back H d Y i)] with t ht; rw [← ht]; rfl
  have h := (hroy.congr_of_eventuallyEq he').unique (he J)
  have hf1 := (chart_of_links H d Y).1.of_le (m:=(1:ℕ)) le_top
  calc
    _ = G.colorMat (L (term (logTest H d Y) 1 J)) := rfl
    _ = G.colorMat (ordinary 1 (L ∘ f)) := by
      unfold term
      rw [←radial_eq 1 hf1,ordinary_map _ _ (hf.of_le le_top)]
    _ = G.colorMat (deriv D 0) := by simp [ordinary,D, Function.comp_def, iteratedDeriv_one]
    _ = _ := h

lemma links_independent (H T:Hol G) (J:Jet G) (t:ℝ) : H.links d J t=T.links d J t:=by
  funext i; exact congrFun ((H.solves d J t i).unique (T.solves d J t i)) 1
lemma log_independent (H T:Hol G) (Y:Finset Cover): logTest H d Y= logTest T d Y:=by
  funext q i; unfold logTest; rw [links_independent H T]

variable {F:Frame G d} (S:SectionData F)
lemma section_links (H:Hol G) (p:F.Coeff) :
   echo S p ∘ logTest H d S.stencil =ᶠ[𝓝 0]
     (fun J:Snap G d=> S.evaluate p (H.links d (expand d J) 1)) := by
  filter_upwards [show ∀ᶠ J:Snap G d in 𝓝 0, ∀ i:UsedEdges S.stencil,
      G.lieExp (logTest H d S.stencil J i) = H.links d (expand d J) 1 i.val from
        eventually_all.mpr (fun i=>back H d S.stencil i)] with J hJ
  have he : Source.entry (S:=S.stencil) (H.links d (expand d J) 1)=lit (logTest H d S.stencil J):=by
    funext i; unfold Source.entry lit; rw [flag_eval,hJ]
  unfold echo SectionData.evaluate Function.comp; rw [he]; rfl
end YM.Dict06.Wil
