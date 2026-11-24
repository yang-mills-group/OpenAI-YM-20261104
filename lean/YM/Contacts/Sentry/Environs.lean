import YM.Contacts.Sentry.Puppet
set_option autoImplicit false
noncomputable section
namespace YM.Contacts.Sensor
open Function Set Filter Metric MeasureTheory Extraction Table Org Spec Power Next.UVStress Costar Analysis Ward
open scoped Topology BigOperators ContDiff

variable {α β :Type*}{ι J :Type} {P:Pace α}{a b l m:ℝ}
-- name spaces for relative geometry
abbrev Allotment (x:α→ E4)(y:α→ E4)(b:ℝ)(P:Pace α) := P.Priced (-b) fun i=> x i-y i
def Distinctly (P:Pace α)(b:ℝ)(x y:α→ E4) : Prop := P.Longer (-b) fun i=> ‖x i-y i‖
lemma Distinctly.symm {x y:α→ E4} (h:Distinctly P b x y): Distinctly P b y x:=h.congr (Eventually.of_forall fun i=> norm_sub_rev ..) -- invalid dot
lemma Distinctly.paying {x y:α→ E4}(h:Distinctly P b x y)(hh:b ≤ a): Distinctly P a x y:= Pace.Longer.decrease h (by linarith)
lemma Distinctly.also {x y z:α→ E4}(h:Distinctly P b x y)(hh:Allotment z y a P)(ha:b<a): Distinctly P b x z:= Pace.Longer.between h hh.abs_cost (by linarith) (Eventually.of_forall fun i=> by simp_rw [← dist_eq_norm]; apply dist_triangle)
lemma Distinctly.congr' {x y z:α→ E4}(h: Distinctly P b x y)(he:y =ᶠ[P.net] z) :Distinctly P b x z:= Pace.Longer.congr h (he.mono fun i hi=>by dsimp only; rw [hi])
lemma Allotment.trans {x y z:α→ E4}(h:Allotment x y a P)(ht:Allotment y z a P) : Allotment x z a P:= (h.add_cap ht).congr (by simp [Filter.EventuallyEq])
lemma Allotment.flip {x y:α→ E4}(h:Allotment x y a P): Allotment y x a P:= h.neg.congr (by simp)
lemma Allotment.narrows {x y:α→ E4}(h:Allotment x y a P)(hh:b ≤ a): Allotment x y b P:= h.mono (by linarith)

variable {x x':α→ι→ E4}{y y':α→ J→ E4}{o o':α→ E4}
structure Upcoming (P:Pace α)(x:α→ι→ E4)(b:ℝ) : Prop where
    front (i j:ι) : i≠j → Distinctly P b (fun s=>x s i) (fun s=>x s j)
def Modal (P:Pace α)(x:α→ι→ E4)(o:α→ E4)(a:ℝ):Prop:=∀ i, Allotment (fun s=>x s i) o a P
structure Trailhead (P:Pace α)(x:α→ι→ E4)(o:α→ E4)(m l:ℝ) :Prop where
    clear (i:ι): Distinctly P m (fun s=> x s i) o
    apart : Upcoming P x l
lemma Upcoming.inj [Fintype ι](h:Upcoming P x b) : ∀ᶠ i in P.net,Injective (x i):= by
    filter_upwards [eventually_all.mpr fun i=> eventually_all.mpr fun j=> eventually_all.mpr fun H=> (Pace.Longer.pos (h.front i j H))] with j h i k hh
    by_contra hk; specialize h i k hk; rw [hh,sub_self,norm_zero] at h; exact lt_irrefl _ h
lemma Upcoming.finer (h:Upcoming P x b)(he:b ≤ a): Upcoming P x a:= ⟨fun i j H=> (h.front i j H).paying he⟩
lemma Upcoming.moves (h:Upcoming P x b)(he:∀ i:ι, Allotment (fun j=> x' j i) (fun j=> x j i) a P)(ht:b<a): Upcoming P x' b:= ⟨fun i j H=> ((((h.front i j H).also (he j) ht).symm.also (he i) ht).symm)⟩
lemma Upcoming.replaces (h:Upcoming P x b)(he:x =ᶠ[P.net] x'): Upcoming P x' b:=⟨fun i j H=>
    Pace.Longer.congr (h.front i j H) (he.mono fun l hl=> by dsimp only; rw [hl])⟩
lemma Modal.replaces (h:Modal P x o a)(he:x =ᶠ[P.net] x'): Modal P x' o a:= fun i=> (h i).congr (he.mono fun i hi=> by dsimp only; rw [hi])
lemma Modal.fewer (h:Modal P x o a)(he:b ≤ a): Modal P x o b:= fun i=> Allotment.narrows (h i) he
lemma Trailhead.finer (h:Trailhead P x o m l)(hm:m ≤ b)(hl:l ≤ a): Trailhead P x o b a:=⟨fun i=> (h.clear i).paying hm,h.apart.finer hl⟩
lemma Trailhead.recenter (h:Trailhead P x o m l)(he:Allotment o' o a P)(ht:m<a): Trailhead P x o' m l:=⟨fun i=>(h.clear i).also he ht,h.apart⟩
lemma Trailhead.shifts (h:Trailhead P x o m l)(he:∀ i:ι,Allotment (fun j=>x' j i) (fun j=>x j i) a P)(ht:l<a)(hm:m ≤ l): Trailhead P x' o m l:=
    ⟨fun i=> (((h.clear i).symm.also (he i) (hm.trans_lt ht)).symm),h.apart.moves he ht⟩
lemma Modal.moves (h:Modal P x o a)(he:∀ i:ι, Allotment (fun j=>x' j i) (fun j=>x j i) b P)(ht:a ≤ b): Modal P x' o a:= fun i=> Allotment.trans ((Allotment.narrows (he i)) ht) (h i)

variable (h: Modal P x o a)(ht:Trailhead P y o m l) (ha:m<a)
include h ht ha
lemma Modal.different (i j): Distinctly P m (fun s=> x s i) (fun s=> y s j):= ((ht.clear j).also (h i) ha).symm
lemma Modal.allOf (hx:Upcoming P x b): Upcoming P (fun i=>Sum.elim (x i) (y i)) (max m (max b l)):= by
    constructor; rintro (i|i) (j|j) H
    · exact (hx.front i j fun hh=> H (congr_arg _ hh)).paying ((le_max_left ..).trans (le_max_right ..))
    · exact (h.different ht ha i j).paying (le_max_left ..)
    · exact (h.different ht ha j i).symm.paying (le_max_left ..)
    exact (ht.apart.front i j fun hh=> H (congr_arg _ hh)).paying ((le_max_right ..).trans (le_max_right ..))
omit h ht ha in
lemma one_center : Upcoming P (fun i=>fun _:Unit=> o i) a:= ⟨fun i j hh=> (hh (Subsingleton.elim ..)).elim⟩
omit h ht ha in
lemma Upcoming.lights (h: Upcoming P x a)(u:ι): Lit u P x a a:= ⟨fun i he=> h.front i u he,fun i j H=> h.front i j H⟩
lemma Modal.inner_lit (hh:Upcoming P x b)(hb:m≤ b)(u:ι) : Lit (Sum.inl u) P (fun i=>Sum.elim (x i) (y i)) b (max b l):=by
    refine ⟨?_,(h.allOf ht ha hh |>.finer (max_le (hb.trans (le_max_left ..)) le_rfl)).front⟩; rintro (i|i) he; exacts [hh.front i u (fun H=> he (congr_arg _ H)), (h.different ht ha u i).symm.paying hb]
lemma Modal.outer_lit (hh:Upcoming P x b)(hb:m ≤ l)(u:J) : Lit (Sum.inr u) P (fun i=>Sum.elim (x i) (y i)) l (max b l):=by
    refine ⟨?_, (h.allOf ht ha hh|>.finer (max_le (hb.trans (le_max_right ..)) le_rfl)).front⟩; rintro (i|i) he; exacts [(h.different ht ha i u).paying hb,ht.apart.front i u (fun H=> he (congr_arg _ H))]
omit h ha in
lemma Trailhead.lit (hb:m ≤ l): Lit (Sum.inl ()) P (fun i=>Sum.elim (fun _:Unit=> o i) (y i)) m l:= by
   have h: Modal P (fun i=>fun _:Unit=> o i) o (m+1):= fun _=> by unfold Allotment; simpa only [sub_self] using! -- simp using zeros?
       ((Pace.Priced.zeros P (-(m+1)) (X:=E4)))
   simpa only [max_eq_right hb] using Modal.inner_lit h ht (by linarith) one_center (le_refl _) ()
omit h ht ha
-- translations
lemma Allotment.offset (u: α→ E4)(h: Allotment o o' a P): Allotment (fun i=>o i+u i) (fun i=>o' i+u i) a P:=by simpa only [Allotment,add_sub_add_right_eq_sub] using h -- check name
lemma Modal.translated (u:α→ E4)(h:Modal P x o a) : Modal P (fun i j=> x i j+u i) (fun i=>o i+u i) a:= fun i=> Allotment.offset u (h i)
end YM.Contacts.Sensor
