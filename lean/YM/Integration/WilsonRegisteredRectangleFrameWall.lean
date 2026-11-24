import YM.Integration.WilsonRegisteredRectangleFrameNeighborhood
import YM.Integration.WilsonRegisteredRectangleFrameSwap
import YM.Integration.WilsonRegisteredRectangleLaw

/-! Exchange on the actual two-field Haar chart. The true minimizing tests on the intervening shell depend only on the saved exterior. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonRegisteredRectangleFrameWall
open Lattice RG Wilson Finset WilsonRegisteredRectangleFrameData WilsonRegisteredRectangleFrameSwap
open WilsonRegisteredRectangleFrameNeighborhood WilsonRegisteredRectangleLaw
open scoped Classical
variable {G:Gauge}{c f:Side}(S:StepData c f)

def inner (o:Site f)(r:ℕ):Finset (Site c):=univ.filter fun x=>separation o (S.ratio.embed x)≤r

def wall (o:Site f)(r:ℕ):Finset (Site c):=univ.filter fun x=>
  r ≤ separation o (S.ratio.embed x)+S.patch.L.val ∧ separation o (S.ratio.embed x)≤r+S.patch.L.val

theorem boundary (o:Site f)(r:ℕ)(e:Edge (Site c))(cross:crosses (inner S o r) e):e.1+step e.2∈wall S o r:=by
  have near:=jump S e.1 e.2
  have ab:=separation_triangle o (S.ratio.embed e.1) (S.ratio.embed (e.1+step e.2))
  have ba:=separation_triangle o (S.ratio.embed (e.1+step e.2)) (S.ratio.embed e.1)
  rw [separation_comm (S.ratio.embed (e.1+step e.2))] at ba
  simp only [crosses,inner,mem_filter,mem_univ,true_and] at cross
  simp only [wall,mem_filter,mem_univ,true_and];omega

private theorem same_quiet {P:Patch}{K:KernelChoices}{U V:CoverConfig G}(h:Chart P U V):P.usesMin K U ↔ P.usesMin K V:=by
  have ax (j:P.FrameTag):P.axial U j=P.axial V j:=funext fun y=>h.path j.1 y j.2
  have paths (a:P.Frame G):P.via a U=P.via a V:=by funext x y k;simp only [Patch.via,h.path]
  simp only [Patch.usesMin,ax,paths]

theorem earned {o b:Site f}{s t r:ℕ}{A B:Support f}
    (left:∀y∈A,separation o y ≤ s)(right:∀y∈B,separation b y ≤ t)
    (sl:s+bondRoom S < r)(far:r+bondRoom S+t<separation o b)(ext:Config G f)
    (healthy:∀x∈wall S o r,quiet S ext x)(a a' b₀ b':Config G f):
    Separated S (inner S o r) (chart A B ext (a,b₀)) (chart A B ext (a',b')) (chart A B ext (a,b')) (chart A B ext (a',b₀)):=by
  let u (a b:Config G f):=chart A B ext (a,b)
  have left_view (x:Site c)(hx:x∈inner S o r)(a z z':Config G f):
      agrees (S.ratio.embed x) (bondRoom S) (u a z) (u a z'):=by
    intro e he
    have near:= (mem_filter.mp hx).2
    have off:e.1∉B:=by
      intro present;have hb:=right e.1 present
      have ab:=separation_triangle o (S.ratio.embed x) e.1;have bc:=separation_triangle o e.1 b
      rw [separation_comm e.1 b] at bc;omega
    simp only [u,chart,OriginalMarkedConditionalAction.patch,if_neg off]
  have right_view (x:Site c)(hx:x∉inner S o r)(z z' b₀:Config G f):
      agrees (S.ratio.embed x) (bondRoom S) (u z b₀) (u z' b₀):=by
    intro e he
    have near:¬separation o (S.ratio.embed x)≤r:=fun h=>hx (mem_filter.mpr ⟨mem_univ _,h⟩)
    have off:e.1∉A:=by
      intro present;have ha:=left e.1 present
      have ab:=separation_triangle o e.1 (S.ratio.embed x)
      rw [separation_comm e.1 (S.ratio.embed x)] at ab;omega
    simp only [u,chart,OriginalMarkedConditionalAction.patch,if_neg off]
  have siteView {x:Site c}{U V:Config G f}(h:agrees (S.ratio.embed x) (bondRoom S) U V):SiteData S U V x:=by
    apply WilsonRegisteredRectangleFrameNeighborhood.site;intro e he;exact h e (he.trans (Nat.le_add_left ..))
  have saved (x:Site c)(hx:x∈wall S o r)(z v:Config G f):quiet S (u z v) x:=by
    have bounds:= (mem_filter.mp hx).2
    apply (same_quiet (K:=S.kernel) (P:=S.patch) (U:=expandAt (S.ratio.embed x) (u z v)) (V:=expandAt (S.ratio.embed x) ext) ?_).mpr (healthy x hx)
    apply WilsonRegisteredRectangleFrameNeighborhood.site;intro e he
    have offA:e.1∉A:=by
      intro p;have y:=left e.1 p;have atx:=separation_triangle o e.1 (S.ratio.embed x)
      rw [separation_comm e.1 (S.ratio.embed x)] at atx;unfold bondRoom at sl;omega
    have offB:e.1∉B:=by
      intro p;have y:=right e.1 p;have ob:=separation_triangle o e.1 b;rw [separation_comm e.1 b] at ob
      have atx:=separation_triangle o (S.ratio.embed x) e.1;unfold bondRoom at far;omega
    simp only [u,chart,OriginalMarkedConditionalAction.patch,if_neg offA,if_neg offB]
  exact ⟨fun x hx=>⟨siteView (left_view x hx a b₀ b'),siteView (left_view x hx a' b' b₀)⟩,
    fun x hx=>⟨siteView (right_view x hx a a' b₀),siteView (right_view x hx a' a b')⟩,
    fun e hx=>⟨all_bond S e (left_view e.1 hx a b₀ b'),all_bond S e (left_view e.1 hx a' b' b₀)⟩,
    fun e hx=>⟨all_bond S e (right_view e.1 hx a a' b₀),all_bond S e (right_view e.1 hx a' a b')⟩,
    fun e cross=>⟨saved _ (boundary S o r e cross) a b₀,saved _ (boundary S o r e cross) a' b'⟩⟩

theorem original (legal:S.patch.Branches S.kernel G)(β:ℝ)(W:Config G c){o b:Site f}{s t r:ℕ}{A B:Support f}
    (left:∀y∈A,separation o y ≤ s)(right:∀y∈B,separation b y ≤ t)
    (sl:s+bondRoom S < r)(far:r+bondRoom S+t<separation o b)(ext:Config G f)
    (healthy:∀x∈wall S o r,quiet S ext x)(a a' b₀ b':Config G f):
    let k:=fun x=>S.density β (chart A B ext x) W
    k (a,b₀)*k (a',b')=k (a,b')*k (a',b₀):=
  WilsonRegisteredRectangleFrameSwap.original S legal β W _ (earned S left right sl far ext healthy a a' b₀ b')

end YM.Integration.WilsonRegisteredRectangleFrameWall
