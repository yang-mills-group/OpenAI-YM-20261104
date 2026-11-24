import YM.MS.Wilson.Bare
/-! A-linear growth of `art` on expressions, used from color control etc.
 also ties chart replacements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Native.Sew
open Function Set Filter Finset Plane Koszul Cylinder Lab Taylor Chart Bare Draft Lattice
open scoped Topology ContDiff
variable {A B I P : Type} {G : Gauge}
section
variable [Fintype A][DecidableEq A] (W:A→ Edge P)
lemma art_sum (s:Finset I) {F:I→ Lot G A → ℝ}(hF:∀ i∈s,germ (F i)): art W (∑ i∈s,F i)=∑ i∈s,art W (F i):=by simp_rw [art,ink_sum priv s hF,map_sum]
lemma art_scale (c:ℝ){F:Lot G A → ℝ}(h:germ F): art W (c • F) = (c:ℂ) • art W F:= by unfold art; rw [ink_smul _ h,map_smul,map_smul]
lemma art_swap {F H: Lot G A→ℝ}(h:F=ᶠ[𝓝 0] H) : art W F= art W H:= by simp_rw [art,inkit _ h]
end
section
variable (x:Edge P) {g:G.Color→ℝ}
lemma tiny (h:germ g): germ (g ∘ fun f:Lot G Unit=>f ()):= h.comp (f:=fun f:Lot G Unit=> f ()) 0 (contDiff_apply ..|>.contDiffAt)
lemma edge_sum (s:Finset I) {F:I→ G.Color →ℝ}(h:∀ i∈s,germ (F i)): onedge x (∑ i∈s,F i)=∑ i∈s,onedge x (F i):= by
    unfold onedge; rw [show (fun b : Lot G Unit=>(∑ i∈s,F i) (b ()))=∑ i∈s, (F i ∘ (fun b:Lot G Unit=> b ())) from funext fun b=> by rw [Finset.sum_apply,Finset.sum_apply]; rfl, art_sum _ s (fun i hi=> tiny (h i hi))]; rfl
lemma edge_scale (c:ℝ)(h:germ g): onedge x (c • g) = (c:ℂ) • onedge x g:= art_scale _ c (tiny h)
lemma edge_swap {f:G.Color→ℝ}(h:f=ᶠ[𝓝 0] g): onedge x f=onedge x g:= art_swap _ ((continuous_apply ()|>.tendsto (0:Lot G Unit)).eventually h)
end
end YM.MS.Native.Sew
