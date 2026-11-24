import YM.SchemeRG11.Wisp.Settle
/-! Native tallies and finite-performance scaling. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Long
open Function Filter Asymptotics Topology MeasureTheory Metric
open Flock Lattice Pert Align Full Maxwell Haze Pile Catch World
open scoped Classical
variable {T:Align.Itinerary} {R:ℝ} {I:Type*}
variable {u v x y:ℤ}
abbrev Slate:=ℕ → Cover→ℝ
def Wall (T:Align.Itinerary)(S:ℕ → Cover→Prop)(u v:ℤ)(f:Slate): Prop:=∃ C>0,∀ᶠ i in atTop,∀z,S i z→|f i z|≤ C*T.gap i^u*d z^v -- ambiguity d z^v
abbrev Near(T: Align.Itinerary)(R:ℝ)(i:ℕ)(z:Cover): Prop:= baseU T i z ≤R
abbrev Local(T: Align.Itinerary)(R:ℝ)(u v) := Wall T (Near T R) u v
def Streams (T:Align.Itinerary)(S:E4→Prop)(v:ℤ)(f:Slate):Prop:=∀ y:E4,y≠0→S y→∀p:ℕ → Cover,Along T p y→ Finishes (fun i=>T.gap i^v*f i (p i))
variable {f g:Slate}
lemma Wall.mul {S}(h:Wall T S u v f)(w:Wall T S x y g):Wall T S (u+x) (v+y) (f*g):=by
 obtain ⟨A,a,h⟩:=h; obtain ⟨B,b,w⟩:=w
 refine ⟨A*B, by positivity, ?_⟩; filter_upwards [h,w] with i h w z hz; have he:=T.positive i; have hx:=d_pos z; simp only [Pi.mul_apply,abs_mul,zpow_add₀ he.ne',zpow_add₀ hx.ne']; exact (mul_le_mul (h z hz) (w z hz) (abs_nonneg _) (by positivity)).trans_eq (by ring)
lemma Wall.add {S}(h:Wall T S u v f)(w:Wall T S u v g):Wall T S u v (f+g):=by
 obtain ⟨A,a,h⟩:=h; obtain ⟨B,b,w⟩:=w
 refine ⟨A+B, by positivity,?_⟩; filter_upwards [h,w] with i h w z hz; exact (abs_add_le ..).trans ((add_le_add (h z hz) (w z hz)).trans_eq (by ring))
lemma Wall.neg {S}(h:Wall T S u v f):Wall T S u v (-f):=by unfold Wall at *; simpa only [Pi.neg_apply,abs_neg]
lemma Wall.sub {S}(h:Wall T S u v f)(w:Wall T S u v g):Wall T S u v (f-g):=by rw [sub_eq_add_neg]; exact h.add w.neg
lemma Wall.zero {S}:Wall T S u v 0:=by refine ⟨1,by norm_num,Eventually.of_forall ?_⟩; intro i z h; simp only [Pi.zero_apply,abs_zero]; have :=T.positive i; have :=d_pos z; positivity
lemma Wall.scale(u:ℤ){S}:Wall T S u 0 (fun i _=> (T.gap i)^u):=by
 refine ⟨1,zero_lt_one,Eventually.of_forall ?_⟩; intro i p h; simp only [one_mul,zpow_zero,mul_one,abs_of_pos (zpow_pos (T.positive _) _),le_refl]
lemma Wall.const {S}(c:ℝ):Wall T S 0 0 (fun _ _=>c):=by refine ⟨|c| +1,by positivity,Eventually.of_forall ?_⟩; intro i p h; simp
lemma Wall.switch{S}(h:Wall T S u v f)(p:∀ᶠ i in atTop,∀x,S i x→f i x=g i x):Wall T S u v g:=by obtain ⟨C,hC,e⟩:=h; refine ⟨C,hC,?_⟩; filter_upwards [e,p] with i h hi x hx; rw [← hi x hx]; exact h x hx
lemma Wall.pay_s {S}(h:Wall T S u v f)(c:ℝ):Wall T S u v (c • f):=by simpa only [zero_add, show (fun (_:ℕ) (_:Cover)=>c)*f = c • f from rfl] using (Wall.const (T:=T) c).mul h
lemma Wall.inherit{S W}(h:Wall T S u v f)(p:∀ᶠ i in atTop,∀x,W i x→S i x):Wall T W u v f:=by obtain ⟨C,hC,H⟩:=h; exact ⟨C,hC,(H.and p).mono fun i h x hx=> h.1 x (h.2 x hx)⟩
lemma Wall.weaken{S}(h:Wall T S u v f)(p:v≤y):Wall T S u y f:=by obtain ⟨C,a,H⟩:=h; refine ⟨C,a,H.mono (fun i hi k hk=>(hi k hk).trans (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (d_le k) p) (mul_nonneg a.le (zpow_pos (T.positive _) _).le)))⟩
lemma Wall.sum {S}(s:Finset I)(f:I→ Slate)(h:∀i∈s,Wall T S u v (f i)):Wall T S u v (∑i∈s,f i):=by induction s using Finset.induction_on with
 | empty=> rw [Finset.sum_empty]; exact .zero
 | insert i s hi ih=> rw [Finset.sum_insert hi]; exact (h i (by simp)).add (ih (fun j hj=>h j (by simp [hj])))
lemma Wall.sums {S}(s:Finset I)(f:I→ Slate)(h:∀i∈s,Wall T S u v (f i)):Wall T S u v (fun i p=>∑ k∈s,f k i p):=by
 apply (sum s f h).switch; apply Eventually.of_forall; intro i x _; simp only [Finset.sum_apply]
lemma fold{S:ℝ}(h:Local T S u v f)(a:ℤ)(ha:0≤a): Local T S (u-a) (v-a) f:=by
 obtain ⟨C,hC,h⟩:=h
 let e:= (|S| +1)^a
 have he:e>0:= zpow_pos (by positivity) _
 refine ⟨C*e,by positivity,h.mono (fun i hi x hx=> (hi x hx).trans ?_)⟩
 have hf:=T.positive i; have hg:=d_pos x; have ht : (baseU T i x)^a≤ e:=by
   exact zpow_le_zpow_left₀ ha (mul_pos hf hg).le ((show _≤S from hx).trans ((le_abs_self _).trans (by linarith)))
 calc _ = C*(baseU T i x)^a*T.gap i^(u-a)*d x^(v-a):=by rw [baseU,mul_zpow,zpow_sub₀ hf.ne',zpow_sub₀ hg.ne']; field_simp
      _ ≤ _ := by gcongr
lemma d_plus (x:Cover):∃ C>0,∀ y,d (x+y)≤C*d y ∧ d y≤ C*d (x+y):=by
 have hi (x y:Cover): d (x+y)≤(diam x+1:ℝ)*d y:=by
   have hh:=diam_add x y; unfold d; apply (add_le_add_left (Nat.cast_le.mpr hh) 1).trans; push_cast; nlinarith [Nat.cast_nonneg (α:=ℝ) (diam x),Nat.cast_nonneg (α:=ℝ) (diam y)]
 exact ⟨_,show 0<(diam x+1:ℝ) by positivity,fun y=>⟨hi x y,by simpa only [neg_add_cancel_left,diam_neg] using hi (-x) (x+y)⟩⟩
lemma d_pow(x:Cover)(v:ℤ):∃ C>0,∀ y, d (x+y)^v ≤ C*d y^v:=by
 obtain ⟨C,hC,H⟩:=d_plus x; by_cases h:0≤v
 · exact ⟨_,zpow_pos hC v,fun y=>(zpow_le_zpow_left₀ h (d_pos _).le (H y).1).trans_eq (mul_zpow _ _ _)⟩
 refine ⟨_,zpow_pos hC (-v),fun y=>?_⟩; apply (mul_le_mul_iff_right₀ (zpow_pos hC v)).mp -- check
 have he:= zpow_le_zpow_left₀ (show 0≤ -v by omega) (d_pos y).le (H y).2
 have hb:= (inv_le_inv₀ (zpow_pos (mul_pos hC (d_pos _)) (-v)) (zpow_pos (d_pos _) (-v))).2 he
 rw [zpow_neg,←mul_assoc, mul_inv_cancel₀ (zpow_pos hC v).ne',one_mul]; simpa [zpow_neg, mul_zpow] using hb
lemma Wall.moving{x:Cover}{S W}(p:∀ᶠ i in atTop,∀z,W i z→ S i (x+z))(h:Wall T S u v f):Wall T W u v (fun i z=>f i (x+z)):=by
 obtain ⟨C,hC,H⟩:=h; obtain ⟨D,hD,K⟩:=d_pow x v
 refine ⟨C*D, by positivity,(H.and p).mono (fun i w z hz=>?_)⟩
 have ha:=T.positive i; exact (w.1 _ (w.2 z hz)).trans ((mul_le_mul_of_nonneg_left (K z) (by positivity)).trans_eq (by ring))
lemma Wall.pass {r:ℝ}{x:ℕ → Cover}(h:Local T r u v f)(hp:∀ᶠ i in atTop, Near T r i (x i)): ∃ C>0,∀ᶠ i in atTop,|f i (x i)|≤ C*T.gap i^u*(d (x i))^v:=by obtain ⟨C,hC,H⟩:=h; exact ⟨C,hC,(H.and hp).mono fun i a=> a.1 _ a.2⟩

lemma Streams.mul {S}(h:Streams T S u f)(b:Streams T S v g): Streams T S (u+v) (f*g):=by
 intro p hp hh z hz; apply ((h p hp hh z hz).mul (b p hp hh z hz)).same; apply Eventually.of_forall; intro i; simp only [Pi.mul_apply,zpow_add₀ (T.positive i).ne']; ring
lemma Streams.add {S}(h:Streams T S u f)(k:Streams T S u g):Streams T S u (f+g):=by intro p hp w z hz; simp only [Pi.add_apply,mul_add]; exact (h p hp w z hz).add (k p hp w z hz)
lemma Streams.neg {S}(h:Streams T S u f):Streams T S u (-f):=by intro p hp w z hz; simp only [Pi.neg_apply,mul_neg]; exact (h p hp w z hz).neg
lemma Streams.sub {S}(h:Streams T S u f)(w:Streams T S u g):Streams T S u (f-g):=by rw [sub_eq_add_neg]; exact h.add w.neg
lemma Streams.zero {S}:Streams T S u 0:=by intro p hp w z hz; simp only [Pi.zero_apply,mul_zero]; exact .const _
lemma Streams.const {S}(c:ℝ):Streams T S 0 (fun _ _=>c):=by intro p hp w z hz; simp only [zpow_zero,one_mul]; exact .const _
lemma Streams.weaken {S}(h:Streams T S u f)(hu:u≤v):Streams T S v f:=by
 intro p hp w z hz; have he:Finishes (fun i=> T.gap i ^ (v-u)):=by
    rw [← Int.toNat_of_nonneg (by omega : 0≤v-u)]; simp_rw [zpow_natCast]; apply Finishes.of (T.cutoff.pow _)
 apply (he.mul (h p hp w z hz)).same; apply Eventually.of_forall; intro i; dsimp only; rw [← mul_assoc,← zpow_add₀ (T.positive _).ne',sub_add_cancel]
lemma Streams.pod{S}(h:Streams T S u f)(v:ℝ):Streams T S u (v • f):= by simpa only [zero_add, show (fun (_:ℕ) (_:Cover)=>v)*f = v • f from rfl] using (Streams.const (T:=T) v).mul h
lemma Streams.sum {S}(s:Finset I)(f:I→Slate)(h:∀i∈s,Streams T S u (f i)): Streams T S u (∑i∈s,f i):=by
 intro p hp a z hz; simp only [Finset.sum_apply,Finset.mul_sum]; exact Finishes.sum s _ fun i hi=> h i hi p hp a z hz
lemma Streams.moving {S}(x:Cover)(h:Streams T S u f): Streams T S u (fun i z=>f i (x+z)):=by intro p hp w z hz; simp_rw [add_comm x]; exact h p hp w _ (hz.shift x)
end YM.SchemeRG11.Long
