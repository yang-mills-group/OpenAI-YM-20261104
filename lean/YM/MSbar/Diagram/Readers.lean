import YM.MSbar.Diagram.Linearity
/-! Static-fiber versions of the operations. Here s denotes the common true-pairs regulator variable,
not the auxiliary integer for transfers. `Live` doesn't require transfer bounds (input independent
of s so constant in this regime). -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Diagram
open Super Domain Domain.DR Loops Dim Symbol Function Set Filter MeasureTheory Arrow
open scoped Topology BigOperators Classical ContDiff ENNReal
abbrev Vertex (C:Type) := ∀m,Words C m→ℂ
abbrev Sites (C:Type):= ∀m, Loops.Line (Token C m) (Mom m)
variable {C:Type} {W:Edition C} {R T : ℝ} {m n j:ℕ} {d e l:Bit}
    (z:ℂ) {f g:Vertex C}{X Y: Sites C}
abbrev liftV (f:Vertex C) : Functionals C:=fun _=>f
abbrev liftS (L:Sites C):Links C:=fun _=>L
abbrev Live (W:Edition C) (d:Bit) (f:Vertex C) := Full univ 0 W d (liftV f)
structure Window (W:Edition C) (d:Bit) (T:ℝ) (P:Sites C):Prop where
   fit : Pilot univ 0 W d (liftS P)
   bounded : Band univ (liftS P) T
   space : 0≤T

def traceP (W:Edition C) (z:ℂ) (P:Sites C) (f:Vertex C): Vertex C:= Lap W (liftS P) (liftV f) z
def traceT (W:Edition C) (d:Bit) (z:ℂ) (P:Sites C) (f g:Vertex C): Vertex C:=splice W d (liftS P) (liftV f) (liftV g) z
def traceR (W:Edition C) (z:ℂ) (P:Sites C) (f:Vertex C): Vertex C:= tick W (liftS P) (liftV f) z
-- defeq constraints assembled in SOME operations read with same z. Provide canon lemmas
lemma atP (P:Links C) (F:Functionals C): Lap W P F z=traceP W z (P z) (F z):= lap_at W rfl rfl -- infer?
lemma atT (P:Links C) (F G:Functionals C): splice W d P F G z=traceT W d z (P z) (F z) (G z):= splice_at W d rfl rfl rfl
lemma atR (P:Links C) (F:Functionals C): tick W P F z=traceR W z (P z) (F z):= point z rfl rfl

variable (hf: Live W d f) (hx: Window W e T X)
namespace Window
lemma add (hp:Window W d T X) (hq:Window W d T Y): Window W d T (X+Y):=⟨hp.fit.add hq.fit,hp.bounded.add hq.bounded,hp.space⟩
lemma scale (hp:Window W d T X) (c:ℂ): Window W d T (c•X) := ⟨hp.fit.scale c,hp.bounded.scale c,hp.space⟩
lemma grow (hp: Window W d T X) (hb:T≤R): Window W d R X:= ⟨hp.fit,hp.bounded.mon hb,hp.space.trans hb⟩ -- name
end Window

namespace Live
lemma add (hf:Live W d f) (hg:Live W d g):Live W d (f+g):= Full.add hf hg
lemma scale (c:ℂ) (hf:Live W d f): Live W d (c•f):= Full.scale hf c
lemma zero : Live W d 0:= Full.zero ..
lemma neg (hf: Live W d f):Live W d (-f) :=Full.neg hf
lemma sub (hf: Live W d f) (hg:Live W d g): Live W d (f-g):=Full.sub hf hg
lemma sum {ι:Type*} {F:ι→Vertex C}(s:Finset ι) (h:∀ i∈s, Live W d (F i)): Live W d (∑ i∈s,F i):=by induction s using Finset.induction_on with | empty=> rw [Finset.sum_empty]; exact zero | insert i s hi ih=> rw [Finset.sum_insert hi]; exact Live.add (h i (Finset.mem_insert_self ..)) (ih fun j hj=> h _ (Finset.mem_insert_of_mem hj))
lemma arc {i} (hp:Live W d f): Arc (f i):= fares hp.licensed (mem_univ 0)
include hf
lemma hits (h: Pilot univ 0 W e (liftS X)): Live W (e+d) (traceR W z X f):= Full.freeze (Arrow.full hf h) (mem_univ z)
include hx
lemma gets : Live W (e+d) (traceP W z X f):= Full.freeze (payload hf hx.fit hx.bounded hx.space isOpen_univ) (mem_univ z)
lemma wins (hg:Live W l g): Live W (e+d+l) (traceT W d z X f g):= Full.freeze (spin_splice hf hg hx.fit hx.bounded) (mem_univ z)

lemma line_sum (hg:Live W d g): traceP W z X (f+g)=traceP W z X f+traceP W z X g:=
    congr_fun (Clear.add_lap hx.fit hx.bounded hx.space hf hg) z -- defeq? Pi
lemma mass (c:ℂ):traceP W z X (c•f)=c•traceP W z X f:=congr_fun (Clear.scale_lap hx.fit hx.bounded hx.space hf c) z
lemma line_scale (c:ℂ): traceP W z (c•X) f=c•traceP W z X f:= congr_fun (Clear.kernel_lap hx.fit hx.bounded hx.space hf c) z
lemma kernel_add (hy:Window W e R Y):traceP W z (X+Y) f=traceP W z X f+traceP W z Y f:=by
    let K:=max T R; have hA:= Band.mon hx.bounded (show T≤K from le_max_left ..);exact congr_fun (Clear.line_lap hx.fit hA (hx.space.trans (le_max_left ..)) hf hy.fit (hy.bounded.mon (le_max_right ..))) z
end Live

namespace Static
variable {K:Sites C} {h:Vertex C}
lemma plus_R : traceR W z X (f+g)=traceR W z X f+traceR W z X g:= congr_fun (Clear.add_tick (K:=liftS X) (W:=W) (F:=liftV f) (G:=liftV g)) z
lemma scale_R (c:ℂ): traceR W z X (c•f)=c•traceR W z X f:= congr_fun (Clear.scale_tick (K:=liftS X) (W:=W) (F:=liftV f) c) z
lemma plus_T : traceT W d z X (f+g) h=traceT W d z X f h+traceT W d z X g h:= congr_fun (Clear.add_tree_1 (d:=d) (K:=liftS X) (F:=liftV f) (G:=liftV g) (H:=liftV h)) z
lemma scale_T (c:ℂ): traceT W d z X (c•f) h=c•traceT W d z X f h:= congr_fun (Clear.scale_tree_1 (d:=d) (K:=liftS X) (F:=liftV f) (H:=liftV h) c) z
lemma plus_T' : traceT W d z X h (f+g)=traceT W d z X h f+traceT W d z X h g:= congr_fun (Clear.add_tree_2 (d:=d) (K:=liftS X) (F:=liftV f) (G:=liftV g) (H:=liftV h)) z
lemma scale_T' (c:ℂ): traceT W d z X h (c•f)=c•traceT W d z X h f:= congr_fun (Clear.scale_tree_2 (d:=d) (K:=liftS X) (F:=liftV f) (H:=liftV h) c) z
end Static
end YM.MSbar.Diagram
