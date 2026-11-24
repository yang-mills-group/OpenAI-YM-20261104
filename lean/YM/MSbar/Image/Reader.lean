import YM.MSbar.Ward.Master
/-! Minimal subtraction surviving section. Region-independent reader, used on certified functions
only, projection to smooth full evanescent symbol for external data. -/
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Image
open Dim Symbol Domain Diagram Function Set Filter Play Play.Deck Category Counter Counter.Price Super Scale
open scoped Classical Topology BigOperators
variable {C:Type} (V U:Set ℂ) (W:Edition C) (d j c:Bit) {X Y:Functionals C} {z:ℂ}
def clear (U:Set ℂ)(W:Edition C)(d:Bit)(F:Functionals C): Functionals C:= if h:Regular U W d F then (Price.rem h).choose else 0
def reader (U:Set ℂ)(W:Edition C)(d:Bit)(F:Functionals C): Vertex C:= clear U W d F 0
namespace Reader
variable {W U V d j c} (h:Regular U W d X) (hh:Regular U W d Y) 
-- don't need actual h for val.live but restrict statements
include h
lemma star : Bright U W d (clear U W d X):= by rw [clear,dif_pos h]; exact (Price.rem h).choose_spec.1
lemma core : EqOn X (clear U W d X) (rim U):=by rw [clear,dif_pos h]; exact (Price.rem h).choose_spec.2
variable [p:Profit U]
include p
lemma whole (m:ℕ)(t:Words C m): Tendsto (fun z=> X z m t) (𝓝[≠] (0:ℂ)) (𝓝 (reader U W d X m t)):=by
    refine (((Bright.hol (star h) t 0 p.around).differentiableAt (p.pub.mem_nhds p.around)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (p.pub.mem_nhds p.around), self_mem_nhdsWithin] with z hz hx; exact (congr_fun (congr_fun (core h ⟨hz,hx⟩) m) t).symm
lemma live : Live W d (reader U W d X):=(star h).freeze p.around
lemma line {Z:Functionals C}(H:EqOn X Z (rim U))(hZ: Bright U W d Z): reader U W d X=Z 0:= Bright.keep (star h) ((core h).symm.trans H) hZ p.around
lemma equal (he:EqOn Y X (rim U)): reader U W d Y=reader U W d X := line (h.recognize he) (he.trans (core h)) (star h)
lemma region [Profit V] (he: V⊆U): reader V W d X=reader U W d X :=by funext m x; apply tendsto_nhds_unique (whole (h.slim he) m x) (whole h m x)
omit h in
lemma empty : reader U W d 0=0:= line (X:=0) Price.zero (fun _ _=>rfl) (Full.zero U 0 W d)
lemma times (a:ℂ) : reader U W d (a • X)=a•reader U W d X:= line (h.scale a) (fun z hz=>congr_arg (a • ·) (core h hz)) ((star h).scale a)
lemma holm {w:ℂ→ℂ}(hw:DifferentiableOn ℂ w U): reader U W d (Counter.times w X)=w 0 • reader U W d X:= line (h.unit hw) (fun z hz=> congr_arg ((w z) • ·) (core h hz)) (Bright.temp (star h) hw)
include hh
lemma plus : reader U W d (X+Y)=reader U W d X + reader U W d Y := line (h.add hh) (fun z hz=> congr_arg₂ (·+·) (core h hz) (core hh hz)) ((star h).add (star hh))
lemma sub : reader U W d (X-Y)=reader U W d X - reader U W d Y := line (h.sub hh) (fun z hz=> congr_arg₂ (·-·) (core h hz) (core hh hz)) ((star h).sub (star hh))
omit hh
omit h in
lemma sum {α:Type*}(I:Finset α){A:α→Functionals C}(hu:∀ i ∈ I, Regular U W d (A i)): reader U W d (∑ i∈I,A i)=∑ i∈I, reader U W d (A i):=by induction I using Finset.induction_on with | empty=>simp [empty] | insert i s he ih=> rw [Finset.sum_insert he,Finset.sum_insert he,plus (hu _ (Finset.mem_insert_self ..)) (Price.sum s fun j hj=> hu _ (Finset.mem_insert_of_mem hj)),ih (fun j hj=>hu _ (Finset.mem_insert_of_mem hj))]
lemma post {A:Mono W d j}(hA: Play.Linear A) : reader U W j (Play.post A X)=(A 0 (plug W d (reader U W d X))).val := line (bound_linear hA h) (fun z hz => show (A z (plug _ _ _)).val=(A z (plug _ _ _)).val from (by rw [core h hz] )) (hA _ (star h))
lemma twin (H: Regular U W j Y){A:Poly W d j c}(hA:Polarized A): reader U W c (Play.twin A X Y)=(A 0 (plug W d (reader U W d X)) (plug W j (reader U W j Y))).val:= line (bound_poly hA h H) (fun z hz=> show (A z (plug _ _ _) (plug _ _ _)).val=(A z (plug _ _ _) (plug _ _ _)).val from (by rw [core h hz,core H hz])) (hA _ (star h) (star H))
end Reader
end YM.MSbar.Image
