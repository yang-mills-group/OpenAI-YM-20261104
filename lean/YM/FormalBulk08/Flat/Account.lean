import YM.FormalBulk08.Flat.Ray
import YM.FormalBulk08.Flat.Strip

/-!
# A quantitative strip account for pulse/vault and A0/T

Independent calculation. Real formulae were used on the puncture. There is
no uniform in-L puncture interpolation being assumed; instead line
prices use interpolation on the prepaid widths. Numerous other designs of
the same receipts are possible.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Flat
open Filter Set Function Lattice Laurent Bloch Exterior Precision RG Next.Free UVExtension.Free Work.F08
open scoped Topology BigOperators
variable {G : Gauge} {ι α β : Type*} {t j : ℕ}

abbrev Detail (ι : Type*) := ι × { p : Momentum // p∈baseCube ∧ p≠0 }
namespace Detail
def city (x : Detail ι) : ι := x.1
def ray (x : Detail ι) : Momentum:=x.2.val
def toll (x : Detail ι) : ℝ := domainRadius/‖x.ray‖
lemma uses : Range (ι:=Detail ι) ray toll := Range.restrict_weight _ (fun x=>x.2.property.1) (fun x=>x.2.property.2)
end Detail

theorem interior [Fintype α] [Fintype β] (P Q : ι→ Row α β) (E σ : ℝ) (he : 0<E) (hσ : 0<σ)
    (ht : ∀ i,(P i).strip σ E ∧ (Q i).strip σ E) (X : ι→ℝ) (hp : ∀ i,0<X i)
    (hx : ∀ i,X i ≤ 1) (k : ℕ)
    (h : Boards (Detail.toll (ι:=ι)) (fun j=>X j.city^(k+1)) k
      (fun x=> (P x.city).read x.ray) (fun x=> (Q x.city).read x.ray)) :
    ∃ C : ℝ,0<C ∧ ∀ i,(minusRows (P i) (Q i)).strip (σ/4) (C*Real.sqrt (X i)) := by
  have hh (x : α×β) : ∃ C : ℝ,0<C ∧ ∀ i,Laurent.Width (σ/4) (C*Real.sqrt (X i)) ((minusRows (P i) (Q i)) x.1 x.2) := by
    obtain ⟨M,hM,h⟩:=h x.1 x.2
    obtain ⟨C,hC,H⟩:=strip_from_real σ E M hσ he hM k
    exact ⟨C,hC,fun i=> H _ _ ((ht i).1 x.1 x.2) ((ht i).2 x.1 x.2) _ (hp i) (hx i) (fun p hp hx=> (h (⟨i,p,hp,hx⟩:Detail ι)).2.2)⟩
  -- maximum over entry types (post-block when dependent)
  classical
  choose K hK H using hh
  let C := 1+∑ a,K a
  have hC : 0 ≤ ∑ a, K a := Finset.sum_nonneg (fun a _=>(hK a).le)
  refine ⟨C,by unfold C; linarith,fun i a b=>?_⟩
  apply (H (a,b) i).mono le_rfl
  gcongr; exact (Finset.single_le_sum (f:=K) (fun i _=>(hK i).le) (Finset.mem_univ (a,b))).trans (le_add_of_nonneg_left (by norm_num))

lemma pulsePay (k : ℝ) (hk : 0<k) (hj : 4≤j) :
    ∃ σ C : ℝ,0<σ ∧ 0<C ∧ ∀ V : Train j, (pink k V).strip σ C ∧ (blue k V).strip σ C := by
  obtain ⟨ha,hb⟩:=heart_budget k hk hj (fun i:Train j=>i)
  obtain ⟨σ,C,hσ,hC,H⟩:= matrix_cover ha zone_pos (fun i p hp x hx=> (overlap_heart _ hk _ hp x hx).1)
  obtain ⟨η,K,hη,hK,h⟩:= matrix_cover hb zone_pos (fun i p hp x hx=> (overlap_heart _ hk _ hp x hx).2)
  refine ⟨min σ η,max C K,lt_min hσ hη,lt_max_of_lt_left hC,fun v=>?_⟩
  exact ⟨strip_mono (H v) (min_le_left ..) (by rw [mul_one]; exact le_max_left ..),strip_mono (h v) (min_le_right ..) (by rw [mul_one]; exact le_max_right ..)⟩

lemma probe_more (f : α→ι) {V W : ι → Train j} {A : ι→Levels G} {i N N' : ι→ℕ} (h : Probe V W A i N N') : Probe (V ∘ f) (W ∘ f) (A ∘ f) (i ∘ f) (N ∘ f) (N' ∘ f) :=
  ⟨fun x=> h.sizes (f x),fun x=> h.lengths (f x),fun x=>h.which (f x),fun x=> h.from_V (f x),fun x=> h.from_W (f x)⟩

theorem bed_money {V W : ι→Train j} {A : ι→Levels G} {i N N' : ι→ℕ} (h : Probe V W A i N N') (hj : 4≤j) (k : ℝ) (hk : 0<k)
    (X : ι→ℝ) (hp : ∀ x,0<X x) (hx : ∀ x,X x≤1) (hr : ∀ x,fineR (A x) (N x) (i x)≤X x^(28+1))
    (E σ : ℝ) (he : 0<E) (hσ : 0<σ) (hg : ∀ V : Train j, (pink k V).strip σ E ∧ (blue k V).strip σ E) :
    ∃ C : ℝ,0<C ∧ ∀ l, (minusRows (pink k (V l)) (pink k (W l))).strip (σ/4) (C*Real.sqrt (X l)) ∧
                         (minusRows (blue k (V l)) (blue k (W l))).strip (σ/4) (C*Real.sqrt (X l)) := by
  have H:=probe_more Detail.city h
  have R : Range (Detail.ray (ι:=ι)) Detail.toll := Detail.uses
  let r (x:Detail ι) := X x.city^(28+1)
  have hR x := (show fineR ((A ∘ Detail.city) x) ((N ∘ Detail.city) x) ((i ∘ Detail.city) x)≤r x from hr x.city)
  have hX (x:Detail ι):= (show 0≤r x from pow_nonneg (hp x.city).le _)
  obtain ⟨C,hC,hc⟩:=interior (fun x=>pink k (V x)) (fun x=>pink k (W x)) E σ he hσ (fun x=>⟨(hg _).1,(hg _).1⟩) X hp hx 28
    (((Probe.pink_tabs H hj R hR k hk).extra R.atLeast hX (show 14≤28 by decide)).plugs (fun x=> ((heart_true k hk hj (V x.city)).1.echo _ (R.cube x)).symm) (fun x=> ((heart_true k hk hj (W x.city)).1.echo _ (R.cube x)).symm))
  obtain ⟨D,hD,hd⟩:=interior (fun x=>blue k (V x)) (fun x=>blue k (W x)) E σ he hσ (fun x=>⟨(hg _).2,(hg _).2⟩) X hp hx 28
    (((Probe.blue_tabs H hj R hR k hk).extra R.atLeast hX (show 6≤28 by decide)).plugs (fun x=>((heart_true k hk hj (V x.city)).2.echo _ (R.cube x)).symm) (fun x=>((heart_true k hk hj (W x.city)).2.echo _ (R.cube x)).symm))
  exact ⟨max C D,lt_max_of_lt_left hC,fun l=>⟨strip_mono (hc l) le_rfl (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.sqrt_nonneg _)),strip_mono (hd l) le_rfl (mul_le_mul_of_nonneg_right (le_max_right ..) (Real.sqrt_nonneg _))⟩⟩

namespace Gate

lemma spread_out (q : Gate j t) {p : ι→ Momentum} {F : Thread j t α β} (h : Secured F)
    (V W : ι→Train j) {w r : ι→ℝ} (k : ℕ) (u : ℕ) (s : List Axis) (hs : s.length≤j-2)
    [Fintype α] [Fintype β] (hp : Range p w) (hr : ∀ i,0≤r i) (hh : ∀ l : Site q.L, Boards w r k
      (fun x=> F (q.ride (V x)) (p x) l) (fun x=> F (q.ride (W x)) (p x) l)) :
    Boards w r k (fun x=> (advanceC q.L (meshBook F u [] (q.ride (V x))) s).read (p x))
      (fun x=> (advanceC q.L (meshBook F u [] (q.ride (W x))) s).read (p x)) := by
  rintro ⟨x,i⟩ b
  let j' := q.sample.legal
  have he x' : Differentiable ℂ (fun p : Momentum=> chip (p x')) := by unfold chip; fun_prop
  have hw : Continuous (fun p=> toll q.L u*listChip p s) := by
    apply Continuous.const_mul
    have hy (s : List Axis) : Continuous (fun p=>listChip p s) := by
      induction s with
      | nil => exact continuous_const
      | cons a s ih=> exact Continuous.mul ((he a).continuous) ih
    exact hy s
  have hy l : Continuous (fun p : Momentum=>mode p (lift (l:Site q.L))) := by unfold mode; fun_prop
  let B (l : Site q.L) (V : ι→Train j) (a) := mode (aliasAt (p a) l) (lift x) • ((toll q.L u*listChip (aliasAt (p a) l) s) • F (q.ride (V a)) (p a) l)
  have ha (l:Site q.L) : Boards w r k (B l V) (B l W) := by
    have hv := hp.images q.L q.sample.odd l
    exact (Boards.sm (hv.on_axis hr _ (hy x)) (Boards.sm (hv.on_axis hr _ hw) (hh l))).extra hp.atLeast hr (by omega : 0+(0+k)≤k)
  have hv := Boards.sum Finset.univ hp.atLeast hr (fun l=> B l V) (fun l=> B l W) (fun l _=>ha l) i b
  have hy T (l:ι) : Row.read (advanceC q.L (meshBook F u [] (q.ride (T l))) s) (p l) (x,i) b = (∑ j, B j T l) i b := by
    rw [show advanceC q.L (meshBook F u [] (q.ride (T l))) s = meshBook F u s (q.ride (T l)) from Secured.traverse h j' u hs (q.ride (T l))]
    exact Secured.bankRead h j' u hs (q.ride (T l)) x (hp.cube l) i b
  exact hv.plugs (fun i=> (hy V i).symm) (fun i=> (hy W i).symm)

theorem cross_money (q : Gate j t) {V W : ι→Train j} {A : ι→Levels G} {i u N N' : ι→ℕ}
    (h : Probe V W A i N N') (ht : 4≤t) (hc : Probe (fun x=> (q.ride (V x)).land) (fun x=> (q.ride (W x)).land) A u N N')
    (X : ι→ℝ) (hp : ∀ x,0<X x) (hx : ∀ x, X x≤1) (hr : ∀ x,fineR (A x) (N x) (i x)≤X x^(28+1))
    (hs : ∀ x,fineR (A x) (N x) (u x)≤X x^(28+1))
    (k : ℝ) (hk : 0<k) (s : List Axis) (hS : s.length≤j-2) (σ E : ℝ) (hσ : 0<σ) (hE : 0<E)
    (hw : ∀ x : Train j, (advanceC q.L (Flight.duo k (q.ride x)).A0 s).strip σ E ∧ (advanceC q.L (Flight.duo k (q.ride x)).T s).strip σ E) :
    ∃ C : ℝ,0<C ∧ ∀ l,
      (minusRows (advanceC q.L (Flight.duo k (q.ride (V l))).A0 s) (advanceC q.L (Flight.duo k (q.ride (W l))).A0 s)).strip (σ/4) (C*Real.sqrt (X l)) ∧
      (minusRows (advanceC q.L (Flight.duo k (q.ride (V l))).T s) (advanceC q.L (Flight.duo k (q.ride (W l))).T s)).strip (σ/4) (C*Real.sqrt (X l)) := by
  let f:= Detail.city (ι:=ι); have H:=probe_more f h
  let v:= V ∘ f; let w:= W ∘ f
  have ht': Probe (fun x=> (q.ride (v x)).land) (fun x=> (q.ride (w x)).land) (A ∘ f) (u ∘ f) (N ∘ f) (N' ∘ f) := probe_more f hc
  have R : Range (Detail.ray (ι:=ι)) Detail.toll:=Detail.uses
  let r:= fun l:Detail ι=> X l.city^(28+1)
  have hR l := (show fineR ((A ∘ f) l) ((N ∘ f) l) ((i ∘ f) l) ≤ r l from hr l.city)
  have hz l := (show fineR ((A ∘ f) l) ((N ∘ f) l) ((u ∘ f) l) ≤ r l from hs l.city)
  have hX l := (fineR_pos ..).le.trans (hR l)
  obtain ⟨hA,hT⟩:=secure_both k hk q.sample.legal ht
  obtain ⟨C,hC,hc⟩ := interior _ _ E σ hE hσ (fun x : ι=>⟨(hw (V x)).1,(hw (W x)).1⟩) X hp hx 28
    (spread_out q hA v w 28 1 s hS R hX fun l=> (pilot_tabs R q H hR k hk ht ht' hz l).extra R.atLeast hX (show 16≤28 by decide))
  obtain ⟨D,hD,hd⟩ := interior _ _ E σ hE hσ (fun x : ι=>⟨(hw (V x)).2,(hw (W x)).2⟩) X hp hx 28
    (spread_out q hT v w 28 2 s hS R hX (wire_tabs R q H hR k hk ht ht' hz))
  exact ⟨max C D,lt_max_of_lt_left hC,fun l=>⟨strip_mono (hc l) le_rfl (mul_le_mul_of_nonneg_right (le_max_left ..) (Real.sqrt_nonneg _)),strip_mono (hd l) le_rfl (mul_le_mul_of_nonneg_right (le_max_right ..) (Real.sqrt_nonneg _))⟩⟩
end Gate
end YM.FormalBulk08.Flat
