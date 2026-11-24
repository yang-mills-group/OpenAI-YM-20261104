import YM.SchemeRG11.Wisp.Village
/-! Qualitative limits sufficient for W nontrivial-order. Cut shifts and
interleavings. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.World
open Function Filter Asymptotics Topology MeasureTheory Set Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch
open scoped Classical
variable {T:Align.Itinerary}
def Finishes {E:Type*}[TopologicalSpace E](Q:ℕ→E):Prop:=∃ c,Tendsto Q atTop (𝓝 c)
namespace Finishes
variable {E F I:Type*}
section
variable [TopologicalSpace E]{f g:ℕ→E}(h:Finishes f)
lemma of {y:E}(ht:Tendsto f atTop (𝓝 y)):Finishes f:=⟨_,ht⟩
include h in
lemma same (e:f=ᶠ[atTop] g):Finishes g:=⟨_,h.choose_spec.congr' e⟩
include h in
lemma continuousMap [TopologicalSpace F]{g:E→F}(he:Continuous g):Finishes (fun i=>g (f i)):=⟨_,(he.continuousAt (x:=h.choose)).tendsto.comp h.choose_spec⟩ -- check
lemma const(f:E): Finishes (fun _:ℕ=>f) := ⟨f,tendsto_const_nhds⟩
end
section
variable [NormedAddCommGroup E][NormedSpace ℝ E]{f g:ℕ→E}{u:ℕ→ℝ}
omit [NormedSpace ℝ E] in
lemma add (h:Finishes f)(k:Finishes g): Finishes (fun i=>f i+g i) := ⟨_, h.choose_spec.add k.choose_spec⟩
omit [NormedSpace ℝ E] in
lemma sub (h:Finishes f)(k:Finishes g): Finishes (fun i=>f i-g i) := ⟨_, h.choose_spec.sub k.choose_spec⟩
omit [NormedSpace ℝ E] in
lemma neg (h:Finishes f):Finishes (fun i=>-f i):= ⟨_,h.choose_spec.neg⟩
lemma stretch(h:Finishes u)(k:Finishes f):Finishes (fun i=>u i • f i):=⟨_,h.choose_spec.smul k.choose_spec⟩
omit [NormedSpace ℝ E] in
lemma sum (s:Finset I)(f:I→ℕ→E)(h:∀i∈s,Finishes (f i)):Finishes (fun j=>∑i∈s,f i j):=by
 induction s using Finset.induction with
 | empty=>simp only [Finset.sum_empty]; exact const _
 | insert i s hi ih=>simp_rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih (fun i hi=>h i (by simp [hi])))
end
section
variable {u v:ℕ→ℝ}
lemma mul(h:Finishes u)(k:Finishes v):Finishes (fun i=>u i*v i):=h.stretch k
lemma prod(s:Finset I)(f:I→ℕ→ℝ)(h:∀i∈s,Finishes (f i)):Finishes (fun j=>∏i∈s,f i j):=by
 induction s using Finset.induction with
 | empty=>simp only [Finset.prod_empty]; exact const _
 | insert i s hi ih=>simp_rw [Finset.prod_insert hi]; exact (h i (by simp)).mul (ih (fun i hi=>h i (by simp [hi])))
end
end Finishes
lemma Along.shift {T: Itinerary}{u:ℕ → Cover}{p:E4}(h:Along T u p)(z:Cover): Along T (fun i=> u i+z) p:=by
 have he:= (show Tendsto _ _ _ from h).add (inc_const T z); rw [add_zero] at he; apply he.congr; intro i; ext k; simp [Full.incVec,mul_add]
lemma Along.sub {T: Itinerary}{u v:ℕ → Cover}{p q:E4}(h:Along T u p)(b:Along T v q): Along T (fun i=>u i-v i) (p-q):=by
 apply (Tendsto.sub h b).congr; intro i; ext k; simp [Full.incVec,mul_sub]
lemma Along.base(z:Cover):Along T (fun _=>z) 0:=Align.inc_const _ _

-- integrated corner for near tags. use cut support derived from step.
variable (T)
def d(z:Cover):ℝ:=Catch.diam z+1
lemma d_pos (z:Cover):0<d z:=by unfold d; positivity
lemma d_le (z:Cover):1≤ d z:=by unfold d; simp
abbrev baseU (i:ℕ)(z:Cover):= T.gap i*d z
variable {T}
def Surround (s:ℕ→Finset Cover)(A:ℝ): Prop:= ∀ᶠ i in atTop,∀z∈s i, baseU T i z ≤ A
lemma camp_p {C R:ℝ}{f:ℕ → Cover→ℝ}{s:ℕ→Finset Cover}(h:∀ᶠ i in atTop,∀z∉s i,f i z=0)(hC:C≥0)(hv:Surround (T:=T) s R)(hk:∀ᶠ i in atTop,∀ z∈s i, |f i z| *(baseU T i z)^3≤C): ∀ᶠ i in atTop, ∀ᵐ y:E4, ‖pot (T.gap i) (f i) y‖ ≤ (closedBall (0:E4) (4*R)).indicator (fun y=>4^3*C/‖y‖^3) y:=by
 filter_upwards [h,hv,hk] with i hi hv hk; filter_upwards [volume.ae_ne (0:E4)] with y hy
 let p := stake (T.gap i) y
 by_cases he:p∈s i
 · have e: ‖y‖≤ 4*baseU T i p:= by simp only [baseU,d,←mul_assoc]; exact rock (T.positive i) y
   have b:=hk p he
   rw [indicator_of_mem (mem_closedBall.mpr (by rw [dist_zero_right]; linarith [hv p he]))]
   change ‖f i p‖ ≤ _; rw [Real.norm_eq_abs]; apply (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hy) _)).2; calc
      _ ≤ |f i p| * (4*baseU T i p)^3 := by gcongr
      _ = 4^3*(|f i p| * baseU T i p ^ 3):=by ring
      _ ≤ _ := by gcongr
 change ‖f i p‖ ≤ _; rw [hi p he,norm_zero]; exact indicator_nonneg (fun _ _=>by positivity) _
lemma climbers {f:ℕ → Cover→ℝ}{s:ℕ→Finset Cover}{C R:ℝ}{g:E4→ℝ}
 (h:∀ᶠ i in atTop,∀z∉s i,f i z=0)(hC:C≥0)(hv:Surround (T:=T) s R)(hk:∀ᶠ i in atTop,∀ z∈s i, |f i z| *(baseU T i z)^3≤C)(hx:∀ y:E4,y≠0→ Tendsto (fun i:ℕ=> f i (stake (T.gap i) y)) atTop (𝓝 (g y))) : Tendsto (fun i=> (T.gap i)^4 * (∑ z∈s i,f i z)) atTop (𝓝 (∫y,g y)):=by
 apply Tendsto.congr' _ (tendsto_integral_filter_of_dominated_convergence (F:=fun i=>pot (T.gap i) (f i)) _ (h.mono (fun i hi=> (gridP (T.positive i) (f i) hi).1.aestronglyMeasurable)) (camp_p h hC hv hk) (inv_cube ..) ((volume.ae_ne (0:E4)).mono fun y a=> hx _ a)) -- order?
 exact h.mono fun i hi=> (gridP (T.positive i) (f i) hi).2
lemma travellers {f:ℕ → Cover→ℝ}{s:ℕ→Finset Cover}{C R:ℝ}
 (h:∀ᶠ i in atTop,∀z∉s i,f i z=0)(hC:C≥0)(hv:Surround (T:=T) s R)(hk:∀ᶠ i in atTop,∀ z∈s i, |f i z| *(baseU T i z)^3≤C)(hx:∀ y:E4,y≠0→ Finishes (fun i:ℕ=> f i (stake (T.gap i) y))) : Finishes (fun i=> (T.gap i)^4 * (∑ z∈s i,f i z)):=by
 have htop (y:E4): ∃ v:ℝ,y≠0→ Tendsto (fun i:ℕ=> f i (stake (T.gap i) y)) atTop (𝓝 v):= by
   by_cases H:y=0
   · exact ⟨0,fun a=> absurd H a⟩
   exact ⟨_,fun _=>(hx y H).choose_spec⟩
 choose g hg using htop
 exact ⟨_,climbers h hC hv hk hg⟩
end YM.SchemeRG11.World
