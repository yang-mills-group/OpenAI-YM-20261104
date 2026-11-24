import YM.X.Jet.Pale
/-!
Smooth jet relay under Banach multiline operations; products with Pi components, finance etc. local analytic. For Bank composition prolong.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Jet
open Function Filter Set
open scoped ContDiff Topology BigOperators Classical
variable {A V: Type*}[NormedAddCommGroup A][NormedSpace ℝ A][NormedAddCommGroup V][NormedSpace ℝ V]
namespace Act
variable {a b:Word V}{u v:ℝ→V}{n k : ℕ}
lemma trans_at (ha:Act n u a)(hb:Act n u b)(h:k≤n):a k=b k:= (ha.writes k h).symm.trans (hb.writes _ h) -- notation
lemma emits (ha:Act n u a)(h: Fits n u b) : Act n u b:=⟨ha.nice,h⟩
lemma repairs (ha:Act n u a)(h: ∀ i≤n,a i=b i) : Act n u b:= ha.emits (fun i hi=>(ha.writes i hi).trans (h i hi))
lemma add (ha:Act n u a)(hb:Act n v b): Act n (u+v) (a+b):= (ha.zipper hb).linear (L:=ContinuousLinearMap.fst ℝ V V + ContinuousLinearMap.snd ℝ V V)
lemma smul (ha:Act n u a) (r:ℝ):Act n (r • u) (r • a):= ha.linear (L:=r • ContinuousLinearMap.id ℝ V)
variable {I: Type*}[Fintype I] {T:I→ Type*}[∀ i, NormedAddCommGroup (T i)][∀ i,NormedSpace ℝ (T i)]
variable {f:ℝ→ (i:I)→T i}{s:Word ((i:I)→ T i)}
lemma all_picks (h:∀ i, Act n (fun t=>f t i) (fun k=> s k i)) : Act n f s:= by
   have he : ContDiffAt ℝ ω f 0:= contDiffAt_pi.mpr fun i=> (h i).nice
   refine ⟨he,fun j k=>?_⟩; funext i
   have hh : Act n f (someJ f):= ⟨he,fun i hi=>rfl⟩
   exact ((hh.linear (L:=(ContinuousLinearMap.proj i))).writes j k).symm.trans ((h i).writes j k)
lemma proj (h:Act n f s)(i:I): Act n (fun t=> f t i) (fun k=>s k i) := h.linear (L:=ContinuousLinearMap.proj i)
end Act
end YM.PositionX.Jet
