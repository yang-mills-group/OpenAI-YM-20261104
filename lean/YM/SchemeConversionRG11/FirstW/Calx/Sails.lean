import YM.SchemeConversionRG11.FirstW.Calx.Bits
/-! One-derivative and point stencils. All orientation signs retained. Finite native power budget. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent
open scoped BigOperators Classical
variable {T : Itinerary} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {R r:ℝ} {a b u v k l:ℤ} {G:Gauge}{A B C:ℕ → Field4 G}
variable {X:Type*}[One X][AddCommGroup X]
abbrev flareL (s:Step) : ℝ:= if s.neg then -1 else 1
def torMark (s:Step) : Four X := if s.neg then -step s.dir else 0
lemma board_spin (s:Step) (x:Four X) (A: Wind G X) : boardAt x s A= flareL s • A (x+torMark s,s.dir) := by rcases s with ⟨s,h|h⟩ <;> simp [boardAt, flareL,Step.used,torMark,sub_eq_add_neg]
lemma back_step (x:Four X)(s:Step)(A:Wind G X) : boardAt (x+s.vec) s.rev A= -boardAt x s A := by cases s with|mk b n=>cases n <;> simp [boardAt,Step.rev,Step.used,Step.vec,sub_eq_add_neg]
lemma close_read (i j:Step) (x:Four X) (A:Wind G X): rail x (icon i j) A=(boardAt (x+i.vec) j A-boardAt x j A) - (boardAt (x+j.vec) i A-boardAt x i A) := by
 rw [icon,rail,LinearMap.add_apply,rail,LinearMap.add_apply,rail,LinearMap.add_apply,rail,LinearMap.add_apply,rail,Step.vec_rev]; rw [add_right_comm x,add_neg_cancel_right,back_step,back_step]; simp only [LinearMap.zero_apply]; abel
def CapS (T:Itinerary)(r:ℝ)(a b:ℤ)(A:ℕ→ Field4 G): Prop:=∀ s:Axis, Credit T r a b (fun i x=>A i (x,s))
def Scrip (T:Itinerary)(r:ℝ)(a b:ℤ)(A:ℕ→ Field4 G): Prop:= CapS T r a b A ∧ ∀ i s : Axis,Credit T r a (b-1) (fun j x=> up s (field4 i (A j)) x)
lemma CapS.downgrade (h:CapS T R a b A)(e:r≤R) : CapS T r a b A:=fun s => (h s).weaken le_rfl e
lemma Scrip.bound (h:Scrip T R a b A) (e:b≤k)(he:r≤R): Scrip T r a k A:=⟨fun s=>(h.1 s).weaken e he,fun i s=>(h.2 i s).weaken (by omega) he⟩
lemma leg_cap (i : Step)(h:CapS T R a b A)(e:r<R) : Credit T r a b (fun j x=> boardAt x i (A j)) := by
 simp_rw [board_spin]; exact Credit.fixed ((h i.dir).drift e _) _
lemma rail_cap (i:Walk)(h:CapS T R a b A)(e:r<R) : Credit T r a b (fun j x=> rail x i (A j)) := by
 induction i generalizing r with
 | nil=>simp only [rail,LinearMap.zero_apply]; exact Credit.pure
 | cons i B ih=> obtain ⟨q,hq,hB⟩:= exists_between e; simp only [rail,LinearMap.add_apply]; exact Credit.evolve (leg_cap i h e) ((ih hB).drift hq i.vec)
lemma spire_cap (i:Walk)(h:CapS T R a b A)(hp:CapS T R u v B)(e:r<R) : Credit T r (a+u) (b+v) (fun j x=> spire G x i (A j) (B j)):=by
 obtain ⟨L,hL⟩:= doubles G.ad
 have ht {a b u v:ℤ}(A B:ℕ→Field4 G)(h:CapS T R a b A)(hp:CapS T R u v B): Credit T r (a+u) (b+v) (fun j x=>swerve x i (A j) (B j)):= by
   induction i generalizing r with
   | nil=> simp only [swerve,LinearMap.zero_apply]; exact Credit.pure
   | cons d W ih=> obtain ⟨q,hq,hB⟩:=exists_between e; simp_rw [swerve_eq,←hL]; exact Credit.evolve ((leg_cap d h e).pays ((rail_cap W hp hB).drift hq _) L) ((ih hB).drift hq _)
 simp only [spire,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.flip_apply]; refine Credit.fixed ((ht A B h hp).evolve ?_) _; simpa only [add_comm v b,add_comm u a] using ht B A hp h
lemma slip_fee (s:Step)(f:ℕ → Cover→ E) (h:∀ i:Axis,Credit T R a b (fun j x=>up i (f j) x)) (hp:r<R) : Credit T r a b (fun i x=> f i (x+s.vec)-f i x):= by
 rcases s with ⟨d,m|m⟩
 · exact (h d).weaken le_rfl hp.le
 let p:Cover:= -step d
 have he (x:Cover)(i): f i (x+p)-f i x= (-1:ℝ) • up d (f i) (x+p):= by rw [up,add_assoc]; simp [p]
 change Credit T r a b (fun i x=> f i (x+p)-_); simp_rw [he]; exact ((h d).drift hp p).fixed _
lemma sail_legs (i j:Step)(h:Scrip T R a b A)(e:r<R): Credit T r a (b-1) (fun v x=> rail x (icon i j) (A v)):= by
 have hs (s t:Step): Credit T r a (b-1) (fun v x=> boardAt (x+t.vec) s (A v)-boardAt x s (A v)):= by
   simp_rw [board_spin,← smul_sub]; obtain ⟨q,hq,hR⟩:= exists_between e
   have hp:= slip_fee t (fun v=>field4 s.dir (A v)) (h.2 s.dir) hR; simp_rw [add_right_comm _ t.vec (torMark s)]; exact Credit.fixed (hp.drift hq _) _ -- overlapping rewriting T? simp alt
 simp_rw [close_read]; exact Credit.less (hs j i) (hs i j)
lemma roof_cap (i j:Step)(h:Scrip T R a b A)(ht:Scrip T R u v B)(hp:Scrip T R k l C)(e:r<R):
    Credit T r (a+u+k) (b+v+l-1) (fun s x=>tower G x (icon i j) (A s) (B s) (C s)) := by
 let w:=icon i j
 have he {a b u v k l:ℤ}(A B C:ℕ→Field4 G)(h:Scrip T R a b A)(ht:Scrip T R u v B)(hp:Scrip T R k l C): Credit T r (a+u+k) (b+v+l-1) (fun s x=>inner ℝ (rail x w (A s)) (spire G x w (B s) (C s))) := by rw [show a+u+k=a+(u+k) by omega,show b+v+l-1=(b-1)+(v+l) by omega]; exact Credit.pays (sail_legs i j h e) (spire_cap _ ht.1 hp.1 e) (innerSL ℝ (E:=G.Color))
 simp_rw [tower_eq]
 -- sectors likely C,A,B orientation
 refine Credit.fixed (Credit.evolve (Credit.evolve (he A B C h ht hp) ?_) ?_) _ -- inspect
 · rw [show a+u+k=u+k+a by omega, show b+v+l-1=v+l+b-1 by omega]; exact he B C A ht hp h
 rw [show a+u+k=k+a+u by omega,show b+v+l-1=l+b+v-1 by omega]; exact he C A B hp h ht
end YM.RG11.FirstW
