import YM.RegulatorIR.Profiles.Chance

/-!
# Measurability and sector integrability of profile charges

Measurable proofs do not need the operator bounds (use countable and total
tsum here). But integrability and meaning as graphs still need the absolute
estimates. Half-open is explicit. -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Profiles
open Function Budget Spatial Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory Cluster Diagram Quadratic Prim PowerSeries Gradient Laplace Lattice Gauge Geometry Geometry.Field Chart Orb Wilson RG Tree Tree.Forest Bark Taping Ledger Ledger.Sky Step Matrix StopB Ward Uniform Finset Halo Halo.Sight Gain Labels Source Centered
open scoped Topology ENNReal NNReal BigOperators Classical PowerSeries ContDiff Matrix.Norms.Frobenius Matrix
variable {G:Gauge}{W I X Y U V:Type}{q u b p a i j e k d m:ℕ}{M: W→ℕ}{n:Page M→Side}{L:Meter W}{J D:Choice M}
def Malm (T:Room→Packet X p):Prop:=∀ x, Measurable (fun y:Room=>T y x)
section Tensors
variable {T B:Room→Packet X p} {K:Layer X X}
lemma Malm.const (T:Packet X p): Malm (fun _=>T):=fun _=> measurable_const
lemma Malm.scaled (h:Malm T) (c:ℝ): Malm (fun i=>c • T i):=fun x=> measurable_const.mul (h x)
lemma Malm.plus (h:Malm T)(H:Malm B): Malm (fun i=>T i+B i):= fun x=>(h x).add (H x)
lemma Malm.symmetric (h:Malm T): Malm fun i=> Packet.symmetry (T i):=by intro i; simp_rw [symmetry_at]; exact measurable_const.mul (Finset.measurable_sum _ fun a _=> h _)
lemma Malm.par {T:I→Room→Packet X p}(s:Finset I)(h:∀ i∈s,Malm (T i)): Malm fun w=>∑ i∈s,T i w:=by intro j; simp_rw [Finset.sum_apply]; exact Finset.measurable_sum _ (fun i hi=> h i hi j)
lemma Malm.product {V U:Room→Orders X}(h:∀ i j,Malm fun w=>V w i j)(H:∀ i j,Malm fun w=>U w i j): Malm fun w=>accord (V w) (U w) i j:=by
 apply Malm.par _; intro p hp; apply Malm.par _; intro i hi; have hh:= mem_antidiagonal.mp hi;subst j; simp only [pie];exact Malm.symmetric (fun x=> (h _ _ (cutLeft x)).mul (H _ _ (cutRight x)))
variable [Countable X]
lemma Malm.visit (h:Malm T)(j:Fin p): Malm (fun i=> Packet.ray j (T i) K):=fun x=> Measurable.tsum fun u=> measurable_const.mul (h (update x j u))
lemma Malm.through (h:Malm T): Malm (fun i=> draft K (T i)):=by
 apply Malm.symmetric; generalize List.finRange p =l; induction l with
 | nil=>exact h
 | cons a l ih=> exact Malm.visit ih a
lemma Malm.heat {T:Room→Ranked X}(h:Malm fun w=>T w (p+2)): Malm (fun w=> heating K (T w) p):= Malm.scaled (Malm.symmetric (fun z=> Measurable.tsum (fun i=>measurable_const.mul (h (Tuple.linked z i))))) _
lemma Malm.match_v {T B:Room→Ranked X}(h:Malm fun i=> T i (p+1))(H:Malm fun i=> B i (a+1)): Malm (fun w=> matchTwo K (T w) (B w) (p+a) (p,a)):=by
 unfold matchTwo; simp only
 refine Malm.scaled (Malm.symmetric ?_) _; intro x; exact Measurable.tsum (fun z=> (h (Fin.cons z (cutLeft x))).mul (Malm.visit (K:=K) H 0 (Fin.cons z (cutRight x))))
lemma Malm.rise (P:ℕ→Orders X){F:Room→Orders X}(h:∀ i j,Malm (fun w=>F w i j)):∀ r e k,Malm (fun w=> markHeat K P (F w) r e k):=by
 intro r; induction r using Nat.strong_induction_on with
 | _ r ih=>
    intro i j; cases r
    · simp_rw [markHeat_first];exact h i j
    next r=>
      simp_rw [markHeat_next]; apply Malm.scaled; apply Malm.plus (Malm.heat (ih r (by omega) _ _))
      apply Malm.par _; intro p hp; apply Malm.par _; intro m _; apply Malm.par _; rintro ⟨l,v⟩ hv; rw [← Finset.mem_antidiagonal.mp hv]; exact Malm.match_v (ih p.1 (by have hh:= mem_antidiagonal.mp hp;omega) m.1 _) (Malm.const (P p.2 m.2 _))
lemma Malm.end_v (P:ℕ→Orders X){F:Room→Orders X}(h:∀ i j,Malm fun w=>F w i j) : Malm (fun w=>endHeat k K P (F w) i j):= by unfold endHeat heated; apply Malm.par _; exact fun _ _=> Malm.rise P h _ _ _
lemma Malm.off (h:Malm T)(f:X↪Y): Malm (fun w=> offer f (T w)):=by intro x; apply Measurable.tsum; intro i; exact h _
variable [Countable Y] {P:ℝ}{A: Deck P X U}{F:Deck P Y V}
lemma sheen (S:GridStep A F) (V: Orders X){W:Room→Orders X}(h:∀ i j,Malm fun w=> W w i j): Malm (fun w=> S.each m V (W w) i j):=by
 intro x; exact Malm.through (K:=S.driftL) (Malm.end_v (logHeat S.line (S.jVac V) false) (F:=fun w i j=>offer (firstChannel A F).native (W w i j)) (k:=m) (i:=i) (j:=j) (fun i j=> Malm.off (h i j) (firstChannel A F).native)) (acrossT (lastChannel A F).native x)
omit [Countable X] [Countable Y] in
lemma Sheen [Countable U][Countable V] (S:GridStep A F)(B:Orders U){W:Room→Orders U}(h:∀ i j,Malm fun w=>W w i j): Malm (fun w=> S.island m B (W w) i j):=by
 intro x; exact Malm.through (K:=S.mean) (Malm.end_v (logHeat S.layer (S.jOrb B) true) (F:=fun w i j=>offer (firstChannel A F).tile (W w i j)) (k:=m) (i:=i) (j:=j) (fun i j=> Malm.off (h i j) (firstChannel A F).tile)) (acrossT (lastChannel A F).tile x)
lemma Malm.scrolled (h:Malm T): Malm (fun w=> A.scroll (T w)):=by intro x; apply Measurable.tsum;intro i; apply (h i.val).mul_const
end Tensors

variable {S:Heir n G} {R: Reel S}{T:S.Accounts} (H:(portraitR T).Report m)
def Leading :Prop:=∀ w:W,∀ i r,Malm (fun x=> H.main (Page.opening (signM M) (w,x)) i r)
variable (HH:Leading H)
include HH
lemma raw_measurable :∀ v i j,Malm (fun w=> H.main (leafX v w) i j):= by
 refine Page.proves HH ?_; intro w h i j; change Malm (fun x=> H.main (turnX w x).next i j); simp_rw [← H.step_m]; exact sheen (S.frames w) (T.bulk w.prev) (m:=m) (W:=fun x=> H.main (leafX w.prev x)) h
lemma medium_measurable (w:W) j e : Measurable (medium S T H j e w):= raw_measurable H HH (j.choose w) e 0 Fin.elim0
lemma orbit_measurable :∀ v i j,Malm (X:=Book G (n v)) (p:=j) (fun w=> H.point (leafX v w) i j):=by
 refine Page.proves (fun w i j=> ?_) ?_
 · change Malm (X:=Book G (n (Page.opening M w))) (fun x=> H.point (Page.opening (signM M) (w,x)) i j); simp_rw [H.same]; exact Malm.scrolled (A:= S.maps (Page.opening M w)) (HH w i j)
 intro w h i j; change Malm (X:=Book G (n w.next)) (fun x=> H.point (turnX w x).next i j); simp_rw [← H.step_p]; exact Sheen (S.frames w) (T.orb w.prev) (m:=m) (W:=fun (x:Room)=> H.point (leafX w.prev x)) h
lemma end_measurable (w: W)(Q: Margins (fun w:Page M=> Book G (n w)))(e:ℕ): Measurable (fun x=> outlook S T H Q (w,x) e):=by
 let k:=Page.finallyW M w
 let K:= Q.endK w
 exact Malm.end_v (K:=K) (k:=m) (i:=e) (j:=0) (logHeat K (S.stump T Q w) true) (F:=fun x=> H.point (leafX k x)) (orbit_measurable H HH k) Fin.elim0
variable {c: Flap M→ℝ≥0∞} {γ:ℝ}{Q:Margins (fun w:Page M=> Book G (n w))}
variable (A: Seated S T H Q L u b 6 p a 1 γ c D) (hv:e ≤ p)(hh:D.age ≤ J.age)
include A hv hh
omit HH A hv hh in
private lemma on_cube (f:Room→ℝ)(h:Measurable f) {x:Room}{t:ℝ}(ht:0≤t)(hh:∃ c:ℝ,∀ i∈cube x t,‖f i‖ ≤ c): IntegrableOn f (cube x t):=by
 obtain ⟨c,hc⟩:= hh; let μ:=volume.restrict (cube x t);have he:IsFiniteMeasure μ:= ⟨by unfold μ; simp only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter];rw [cubic x ht];finiteness⟩
 letI : IsFiniteMeasure μ:=he
 exact Integrable.of_bound (μ:=μ) h.aestronglyMeasurable c ((ae_restrict_mem (seen ..)).mono fun y=>hc y)
lemma medium_int (w: W)(t:Room)(l:ℝ)(ht:0≤l): IntegrableOn (medium S T H J e w) (cube t l):=by
 obtain ⟨c,b,hc,h⟩:= Centered.allC S T H Q A hv hh; exact on_cube _ (medium_measurable H HH w J e) ht ⟨_,fun x _=>h w x⟩
lemma outlook_int (w:W): IntegrableOn (fun x=>outlook S T H Q (w,x) e) (Centered.court (S.P w)) :=by
 obtain ⟨c,b',hc,h⟩:= Centered.allC S T H Q A hv hh; obtain ⟨K,t,Hk,hx⟩:= Centered.window_gap S T H Q A hv hh
 exact on_cube _ (end_measurable H HH w Q e) (div_nonneg (S.hp w).le (by norm_num)) ⟨_,fun i hi=>by
    let p:=outlook S T H Q (w,i) e; let g:=medium S T H J e w i
    exact le_trans ((show ‖p‖≤ ‖p-g‖+‖g‖ from (le_of_eq (congr_arg norm (sub_add_cancel p g).symm)).trans (norm_add_le (p-g) g))) (add_le_add (hx w i hi) (h w i))⟩
end YM.RegulatorIR.Profiles
