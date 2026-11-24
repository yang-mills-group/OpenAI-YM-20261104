import YM.MS.ScaleForest.Meridian
/-!
# s/z bookkeeping of the multi-piece forest sum

Distribute linear operations in meromorphic convention. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.ScaleForest
open Set Filter MeasureTheory Real Function
open Plane Koszul Heat Flux Landau Arts Arc Spin Pilot Wire Rock Path Oceans Plum Alps Garment Color Book Convolve Signal Shine Hem Mell Pearl Train Dock Garment.Wick Garment.Wave GraphSum
open Detect Tone Momentum Osc Fiddle Metric
open scoped Topology ContDiff
variable {G : Gauge} {I : Type} {X Y F H : Curtain G I} {n : ℕ}

private theorem weave_plus (X Y H: Mob G) : weave (X+Y) H=weave X H+weave Y H:= funext fun _=> map_add ((product (field parity)).flip (H _)) ..
private theorem weave_more (X Y H: Mob G) : weave H (X+Y)= weave H X+weave H Y:=funext fun _=> map_add (product (field parity) (H _)) ..
section
variable (K:LineRule G) {X Y H:Mob G} {z:ℂ} (hz:z∈Town) (hx:Form0 false X)(hy:Form0 false Y) (hH:Form0 false H) (A:QP)(μ:ℝ)
include hz hx hy hH
lemma pinPlus1 : pinned K.half z μ A (X+Y) H = pinned K.half z μ A X H+pinned K.half z μ A Y H := by
   obtain ht:= K.ok; obtain h:= ht.forms false; rw [placedEq h ht.even ht.rev (hx.add hy) hH hz, placedEq h ht.even ht.rev hx hH hz,
     placedEq h ht.even ht.rev hy hH hz,map_add];
   obtain hx:= form_rephase hx A; obtain hy:=form_rephase hy A; unfold sweptRef; rw [weave_plus,oceanR h (form_weave hx hH) (form_weave hy hH) hz,oceanR h hx hy hz,weave_plus,weave_plus]; simp_rw [smul_sub, smul_add]; abel
lemma pinPlus2 : pinned K.half z μ A H (X+Y) = pinned K.half z μ A H X+pinned K.half z μ A H Y := by
   obtain ht:= K.ok; obtain h:= ht.forms false; rw [placedEq h ht.even ht.rev hH (hx.add hy) hz, placedEq h ht.even ht.rev hH hx hz,
     placedEq h ht.even ht.rev hH hy hz];
   obtain hH:= form_rephase hH A; unfold sweptRef; rw [weave_more,oceanR h (form_weave hH hx) (form_weave hH hy) hz, weave_more,oceanR h hx hy hz,weave_more]; simp_rw [smul_sub, smul_add]; abel
omit hH in
lemma loopPlus : closeG K.half z μ (X+Y)=closeG K.half z μ X+closeG K.half z μ Y:= by simp_rw [closeG_eq]; rw [oceanR (K.ok.forms _) hx hy hz,smul_add]
end

lemma expenses_one (u:Curtain G I→Curtain G I) (p:Curtain G I→Prop) (he:p 0)
    (ht:Iris (u 0) 0)(hl:∀ X Y,p X→p Y→ p (X+Y) ∧ Iris (u (X+Y)) (u X+u Y))
    (l: List (Curtain G I)) (hx:∀ i∈l,p i) : p l.sum ∧ Iris (u l.sum) (l.map u).sum:= by
   induction l with
   | nil=> exact ⟨ he,ht⟩
   | cons i l ih=> obtain ⟨hp,hH⟩:= ih (fun j hj=> hx j (List.mem_cons_of_mem _ hj)); obtain ⟨hp,hu⟩:=hl i l.sum (hx i (by simp)) hp; exact ⟨ hp,EventuallyEq.trans hu (EventuallyEq.add (EventuallyEq.rfl) hH)⟩

def expandsTwo {A B C:Type}(u:A→B→C)(l:List A)(r:List B):List C:= l.flatMap (fun i=> r.map (u i))
lemma expenses_two (u:Curtain G I→ Curtain G I→Curtain G I)
    (hz:∀ X, Visits (I:=I) X→ Iris (u 0 X) 0 ∧ Iris (u X 0) 0)
    (hr:∀ X Y F: Curtain G I, Visits X→Visits Y→Visits F→ Iris (u (X+Y) F) (u X F+u Y F) ∧ Iris (u F (X+Y)) (u F X+u F Y))
    (l r: List (Curtain G I)) (hl:∀ i∈l,Visits i)(ht:∀ i∈r, Visits i) : Iris (u l.sum r.sum) (expandsTwo u l r).sum:= by
   obtain H:= visitSum ht
   induction l with
   | nil=> exact (hz _ H).1
   | cons i l ih=>
      obtain he:= hl i (by simp); obtain hp : ∀ i∈l,Visits i:= fun i hi=> hl _ (List.mem_cons_of_mem _ hi); obtain hx:= (hr i l.sum r.sum he (visitSum hp) H).1; rw [expandsTwo,List.flatMap_cons,List.sum_append];
      exact EventuallyEq.trans hx ( EventuallyEq.add (expenses_one (u i) Visits visit_zero (hz i he).2 (fun a b hK hk=> ⟨visit_plus hK hk,(hr a b i hK hk he).2⟩ ) r ht ).2 ( ih hp ) )

lemma smoke_promise (L:LineRule G)(A:I→QP)(μ:ℝ)(hX:Visits X)(hY:Visits Y)(hF:Visits F) :
    Iris (Pfor L μ (X+Y) F A) (Pfor L μ X F A+Pfor L μ Y F A) ∧ Iris (Pfor L μ F (X+Y) A) (Pfor L μ F X A+Pfor L μ F Y A) := by
   constructor <;> (filter_upwards [hX,hY,hF,Shine.high0] with z h1 h2 h3 hz; funext s t)
   · exact pinPlus1 L hz (h1 s t) (h2 s t) (h3 s t) (exp (-s) • A t) _
   exact pinPlus2 L hz (h1 s t) (h2 s t) (h3 s t) (exp (-s) • A t) _

lemma spends_u (K:LineRule G)(μ:ℝ) (l:List (Curtain G I))(he:∀ i∈l,Visits i) : Iris (Ufor K μ l.sum) (l.map (Ufor K μ)).sum := by
   refine (expenses_one (Ufor K μ) Visits visit_zero ?_ (fun X Y hX hY=> ⟨ visit_plus hX hY,?_⟩) l he).2
   · refine Eventually.of_forall fun x=>?_ ; funext s t; exact closeG_zero K.half x _
   filter_upwards [hX,hY,Shine.high0] with x hx hy hv; funext s t; exact loopPlus K hv (hx s t) (hy s t) _

lemma spends_b (K : LineRule G) (l r: List (Curtain G I))(he:∀ i∈l, Visits i)(hr:∀ i∈r,Visits i): Iris (Bfor K l.sum r.sum) (expandsTwo (Bfor K) l r).sum:= by
   apply expenses_two (Bfor K) _ _ _ _ he hr
   · intro X _; constructor <;> (refine Eventually.of_forall (fun x=>?_); funext s t; simp only [Bfor, Pi.zero_apply,bridgeG_eq K.ok.rev,← schedule,map_zero,LinearMap.zero_apply])
   intro X Y F _ _ _; constructor <;> (refine Eventually.of_forall fun z=>?_ ; funext s t; simp only [Pi.add_apply, Bfor,bridgeG_eq K.ok.rev,← schedule,map_add, LinearMap.add_apply])
lemma spends_p (K : LineRule G) (μ:ℝ)(A:I→QP)(l r: List (Curtain G I))(he:∀ i∈l, Visits i)(hr:∀ i∈r,Visits i): Iris (Pfor K μ l.sum r.sum A) (expandsTwo (fun X Y=>Pfor K μ X Y A) l r).sum:= by
   apply expenses_two (fun X Y=> Pfor K μ X Y A) ?_ (fun _ _ _=> smoke_promise K A μ) _ _ he hr
   intro X _; constructor <;> (refine Eventually.of_forall fun z=>?_; funext s t)
   · exact emptyPin_l (F:=(0:Mob G)) (show Goods 0 _ from (good ..).zero_mem) z _ _
   exact emptyPin_r (F:=(0:Mob G)) (show Goods 0 _ from (good ..).zero_mem) z _ _
lemma spends_v (l:List (Curtain G I))(he:∀ i∈l,Fluxible i) : Iris (vertical l.sum) (l.map vertical).sum := by
   refine (expenses_one vertical Fluxible fluxible_zero ?_ (fun X Y hX hY=> ⟨ fluxible_plus hX hY,?_⟩) l he).2
   · refine Eventually.of_forall fun x=>?_ ; funext s y m w; simp [vertical,mend,velocity,← cert,map_zero]
   filter_upwards [hX,hY] with z hx hy; funext s t m w; simp_rw [Pi.add_apply, vertical,mend,velocity, Pi.add_apply, ← cert,map_add, Pi.add_apply]; exact integral_add (hx s t m w) (hy s t m w)
end YM.MS.ScaleForest
