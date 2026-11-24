import YM.SchemeConversionRG11.FirstW.Calx.Crops
/-! Local gradient bill recycles boundary currents at mask shell.
No based rotational covariance of nearest lift needed. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function MeasureTheory Filter Set Metric Topology Lattice Pert Align Laurent Position Deck SchemeConversionRG11 SchemeConversionRG11.Horizon
open scoped BigOperators Classical ContDiff
variable {G:Gauge} {T:Itinerary} {n:Side} {c:ℕ→Side} {R:ℝ} {W:ℕ→ Field4 G}
def ribbon (n : Side)(W:Field4 G): FullT G n := fun l=> W (lift l.1,l.2)
lemma turnTurn (T:Itinerary)(R:ℝ)(s:Cover): ∀ᶠ i in atTop,∀ x:Site (T.period i), let N:=T.period i; let v:=lift x+s; let u:=lift (wrap N v); Jam T R i u ∨ Jam T R i v → u=v := by
 let r:=R+1
 filter_upwards [entryM T R,entryM T r,birthM (T:=T) (lt_add_one R) (-s)] with i hi hq hj x N v u he; rcases he with H|H
 · have hx:=hq (u+ -s) (hj u H); have ht : wrap N (u + -s)=x := by unfold u v N; simp
   have hy : u+ -s=lift x := hx.symm.trans (congrArg lift ht)
   unfold v; rw [←hy,add_assoc,neg_add_cancel,add_zero]
 exact hi v H
lemma laced (T:Itinerary) (s:Cover)(w:Axis)(h:Lives T R (fun i x=> W i (x,w))): ∀ᶠ i in atTop,∀ x:Site (T.period i), terms (0:Site (T.period i)) (ribbon (T.period i) (W i)) (lift x+s,w)= W i (lift x+s,w) := by
 filter_upwards [turnTurn T R s,h] with i hi he x
 dsimp only [terms,ribbon, Prod.fst, Prod.snd, LinearMap.proj_apply,LinearMap.pi_apply]; rw [add_zero]; let v:=lift x+s; let u := lift (wrap (T.period i) v)
 by_cases hu:W i (v,w)=0
 · by_cases ht:W i (u,w)=0; · exact ht.trans hu.symm
   rw [hi x (Or.inl (he _ ht))]
 rw [hi x (Or.inr (he _ hu))]
lemma tied (T : Itinerary)(h:∀ w:Axis,Lives T R (fun i x=> W i (x,w)))(s:Walk): ∀ᶠ i in atTop,∀ x:Site (T.period i), rail (lift x) s (W i)=rail x s (ribbon (T.period i) (W i)) := by
 suffices he:∀ t: Cover,∀ᶠ i in atTop,∀ x : Site (T.period i), rail (lift x+t) s (terms 0 (ribbon (T.period i) (W i)))=rail (lift x+t) s (W i) by
   filter_upwards [he 0] with i hi x; simpa only [add_zero, rail_wrap,wrap_lift] using (hi x).symm
 intro t
 induction s generalizing t with
 | nil=> simp [rail]
 | cons a l ih=>
   have hp:=laced T (t+torMark a) a.dir (h _)
   filter_upwards [hp,ih (t+a.vec)] with i hi hq x
   simp only [rail,LinearMap.add_apply,add_assoc]; rw [hq]; rw [board_spin,board_spin]; simp only [add_assoc,hi]
lemma owes (n:Side)(a:Who G 6)(Z:FullT G n): wheels (fun x w=>inner ℝ (rail x w Z) (rail x w (canal a.val 0)))= 8*native a.val 0 Z:= by
 have he (ε:Site n→ G.Color): native a.val (0:Site n) (Orb.grad (V:=G.Color) ε)=0:= by rw [show Orb.grad ε= momentE ε from rfl]; exact letter_T a.val 1 _ ε
 have hc(r:Axis→ G.Color): native a.val (0:Site n) (r ∘ Prod.snd)=0:=letter_C ..
 have hh:= active_equation (native a.val (0:Site n)) (fun v=>by unfold Orb.grad at he ⊢; apply he v) hc Z; rw [flat_cross]; unfold canal; rw [hh]
lemma tied_wheels (T:Itinerary)(a : Who G 6)(h:∀ w:Axis,Lives T R (fun i x=> W i (x,w))) : ∀ᶠ i in atTop,
   expenditure T (fun i x=>∑ t:Ticket,∑ s:Ticket,inner ℝ (rail x (icon (fresh t) (fresh s)) (tin G (T.period i) a)) (rail x (icon (fresh t) (fresh s)) (W i))) i = 8*native a.val 0 (ribbon (T.period i) (W i)) := by
 filter_upwards [eventually_all.mpr (fun t:Ticket=> eventually_all.mpr fun v:Ticket=> tied T h (icon (fresh t) (fresh v)))] with i hi
 have e (x:Site (T.period i))(t s:Ticket): rail (lift x) (icon (fresh t) (fresh s)) (W i)=rail x (icon (fresh t) (fresh s)) (ribbon (T.period i) (W i)):= hi t s x
 apply Eq.trans _ (owes (T.period i) a _)
 unfold wheels expenditure; apply Finset.sum_congr rfl; intro x _; apply Finset.sum_congr rfl; intro s _; apply Finset.sum_congr rfl; intro v _
 rw [e]; simp only [tin,rail_wrap,wrap_lift,add_zero]; rw [real_inner_comm]
-- mask applied at initial vertex of each positive link
abbrev tabL (T:Itinerary)(Q:Wash)(i)(x:Cover):= soft Q (Moss T i x)
def windM (T:Itinerary) (Q:Wash)(i:ℕ)(A:Field4 G):Field4 G := fun x=>tabL T Q i x.1 • A x
lemma readyM (T:Itinerary)(Q:Wash)(p:ℕ→Field4 G)(a:Axis): Lives T Q.rOut (fun i x=> windM T Q i (p i) (x,a)):=Eventually.of_forall fun i x hi=>by by_contra h; exact hi (by simp only [windM,tabL,soft_life Q _ (lt_of_not_ge h).le,zero_smul])
lemma term_fit (T:Itinerary)(Q:Wash)(W:ℕ→Field4 G)(x:Cover)(a:Axis): ∀ᶠ i in atTop, terms (0:Site (T.period i)) (ribbon (T.period i) (windM T Q i (W i))) (x,a) = W i (x,a) := by
 have hu:= laced T x a (readyM T Q W a); let μ := fun i=> windM T Q i (W i)
 filter_upwards [hu,Tendsto.norm (inc_const T x) |>.eventually (ge_mem_nhds (show ‖(0:E4)‖<Q.rIn from by rw [norm_zero]; exact Q.rIn_pos))] with i hi he
 have hp: lift (0:Site (T.period i))=0:=by funext i; simp
 have hh:= hi 0; rw [hp,zero_add] at hh; rw [hh]; simp only [windM,tabL,soft_clear Q _ he, one_smul]
lemma native_copy (v : Cover)(x y: ℕ→Field4 G)(h:∀ i j:Edge Cover,i=j → ∀ᶠ t in atTop,x t i=y t j)(a:Labels.Key G):
   ∀ᶠ i in atTop,native a v (x i)=native a v (y i) := by
 have e (s:Signed)(p: Cover)(w:Axis): ∀ᶠ i in atTop,Bare.wideLink G s (x i) (p,w) = Bare.wideLink G s (y i) (p,w) := by
   simp_rw [Bare.wideLink_apply]; exact (h _ _ rfl).mono fun i hi=> congrArg _ hi
 have hP (k:Signed)(p:Cover) (i j:Axis): ∀ᶠ m in atTop,Bare.wideCurl (Bare.wideLink G k (x m)) p i j=Bare.wideCurl (Bare.wideLink G k (y m)) p i j := by filter_upwards [e k p i,e k (p+step i) j,e k (p+step j) i,e k p j] with m h u ht he; simp [Bare.wideCurl,h,u,ht,he]
 have hu (s:Signed) (p:Cover): ∀ᶠ m in atTop,Bare.wideCore G a.1 p (Bare.wideLink G s (x m))=Bare.wideCore G a.1 p (Bare.wideLink G s (y m)) := by
   filter_upwards [eventually_all.mpr (fun i:Axis=> eventually_all.mpr (fun j:Axis=> eventually_all.mpr (fun l:Fin a.1→Axis=>eventually_all.mpr fun w:Finset (Fin a.1)=>hP s (p+∑ i∈w,step (l i)) i j)))] with m hm; funext i j l; simp only [Bare.wideCore_apply]; apply congrArg _; apply Finset.sum_congr rfl; intro w _; rw [hm i j l w]
 filter_upwards [eventually_all.mpr (fun s => hu s (affine s⁻¹ 0 v))] with m hi
 simp only [native,tape,LinearMap.comp_apply,Bare.wideLinear,LinearMap.smul_apply, LinearMap.sum_apply,hi]
lemma earn (T:Itinerary)(a:Who G 6)(Q:Wash)(W:ℕ→ Field4 G) : ∀ᶠ i in atTop,
  expenditure T (fun i x=> ∑ t:Ticket,∑ s:Ticket,inner ℝ (rail x (icon (fresh t) (fresh s)) (tin G (T.period i) a)) (rail x (icon (fresh t) (fresh s)) (windM T Q i (W i)))) i =8*native a.val 0 (W i) := by
 let Y i:= terms (0:Site (T.period i)) (ribbon (T.period i) (windM T Q i (W i)))
 filter_upwards [tied_wheels T a (readyM T Q W),native_copy 0 Y W (fun ⟨v,j⟩ l hl=>hl ▸ term_fit T Q W v j) a.val] with i hi h
 rw [hi,←h]; unfold Y; rw [native_wrap,map_zero,zero_add]
end YM.RG11.FirstW
