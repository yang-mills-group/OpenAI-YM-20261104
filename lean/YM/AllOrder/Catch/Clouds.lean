import YM.AllOrder.Local.Cumulant
import YM.AllOrder.Catch.Tower
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch
open Function Filter Finset Topology Metric
open PhysicalNext Repeat Lantern ConnectedActivityE6 Blaze Brush
open scoped Topology Classical BigOperators ContDiff
variable {X Y ι:Type*}{V U W:X → Type}
variable [∀ i,NormedAddCommGroup (V i)][∀ i,NormedSpace ℝ (V i)] [∀ i,NormedAddCommGroup (U i)][∀ i,NormedSpace ℝ (U i)][∀ i,NormedAddCommGroup (W i)][∀ i,NormedSpace ℝ (W i)]
variable {T:Clock X} {a b c:ℝ} {f g:∀ i, V i→ U i}{h:∀ i, V i→W i}{l g':X→ℝ} {x:∀ i,V i}{k j:ℕ}
local notation "H"=> T.Meter
/-- Fixed finite derivative scales, ω horizon separate. Cannot assert at comparison earlier Theta. Rents on event with true radius ∝ d⁻¹. -/
def Cover (T:Clock X) (k:ℕ)(p:ℝ)(d:X→ℝ)(u:∀ i,V i→U i)(x:∀ i,V i): Prop:= ∀ e>p,∀ᶠ i in T.rail, Brush k (T.cost i^e) (d i) (u i) (x i)
namespace Cover
lemma value (hs:Cover T k a l f x) : H (fun i=> ‖f i (x i)‖) a:=fun e he=>by filter_upwards [hs e he] with i hi; exact (abs_of_nonneg (norm_nonneg _)).trans_le hi.bound
lemma has (hs:H g' a)(h:∀ᶠ i in T.rail, Brush k (g' i) (l i) (f i) (x i)): Cover T k a l f x:=fun e he=>by filter_upwards [h,hs e he] with i hi hw; exact hi.climb ((le_abs_self _).trans hw) le_rfl
lemma small (hs:Cover T k a l f x)(he:j≤k)(ht:a≤b)(hc:l≤ᶠ[T.rail] g'):Cover T j b g' f x:=fun e hb=> ((hs e (ht.trans_lt hb)).and hc).mono fun i h=> (h.1.smaller he).climb le_rfl h.2
lemma orientation (hs:Cover T k a l f x){Y:Clock ι}(u:ι→X)(hp:T.Fare (U:=Y) u): Cover (V:=fun i=>V (u i)) (U:=fun i=> U (u i)) Y k a (fun i=> l (u i)) (fun i=> f (u i)) (fun i=> x (u i)):= by
 intro e he; filter_upwards [hp.tends.eventually (hs e he),hp.same] with i hi hx; rw [hx]; exact hi
-- canonical certificate to use H words: Brush estimate assembled pointwise choose normJ prices. choose no selection ∃ e^ etc. Avoid pole-zero.
lemma display (hs:Cover T k a (fun _=>1) f x): ∃ p:X→ℝ, H p a∧∀ᶠ i in T.rail, Brush k (p i) 1 (f i) (x i):= by
 let pp i:= ∑ j ∈ range (k+1), normJ j (f i) (x i); have hp : H pp a:= by
    unfold pp; apply Clock.Meter.sum; intro j hj b hb; filter_upwards [hs b hb] with i hi; rw [abs_of_nonneg (norm_nonneg _)]; exact (Brush.offer.1 hi).inside j (by rw [mem_range] at hj; omega)
 refine ⟨pp,hp,(hs (a+1) (by linarith)).mono fun i hi=> Brush.offer.2 ⟨hi.smooth, fun j hj=> single_le_sum (f:=fun j=>normJ j (f i) (x i)) (fun _ _=> norm_nonneg _) (mem_range.mpr (by omega))⟩⟩
lemma quite (p:Cover T k a (fun _=>1) f x):T.Quite (fun i=> ‖f i (x i)‖):= Exists.intro a p.value
lemma cert (hs:H (fun i=> ‖f i (x i)‖) a)(he:∀ᶠ i in T.rail, ∀ y,f i y=f i (x i) ∧0≤l i): Cover T k a l f x:= has hs (he.mono (fun i hi=> (Brush.certified (hi (x i)|>.2) _).shimmy (Eventually.of_forall fun x=>(hi x).1)))
lemma fixed (c:∀ i,U i)(he:∀ᶠ i in T.rail,0≤l i)(hx:H (fun i=> ‖c i‖) a): Cover T k a l (fun i (_:V i)=>c i) x:= has hx (he.mono fun i hi=> certified hi _)
lemma opposite (hs:Cover T k a l f x):Cover T k a l (fun i=>-f i) x:=fun e he=> (hs e he).mono fun _ hi=> hi.opposite
lemma add (hs:Cover T k a l f x)(hg:Cover T k a l g x):Cover T k a l (fun i=>f i+g i) x:= by
 intro e he; obtain ⟨p,hp,h⟩:=exists_between he; filter_upwards [hs p hp,hg p hp,T.slack h 2] with i hi hg hG; exact (hi.gathering hg).climb (by rw [two_mul] at hG; exact hG.le) le_rfl
lemma sub (hs:Cover T k a l f x)(hg:Cover T k a l g x):Cover T k a l (fun i=>f i-g i) x:= by simpa only [sub_eq_add_neg] using hs.add hg.opposite
lemma mul {F G:∀ i,V i→ℝ}(hs:Cover T k a (fun _=>1) F x)(he:Cover T k b (fun _=>1) G x):Cover T k (a+b) (fun _=>1) (fun i=> F i* G i) x:= by
 obtain ⟨p,hp,H'⟩:=hs.display; obtain ⟨q,hq,hQ⟩:=he.display; exact has ((hp.mul hq).rscale _) ((H'.and hQ).mono fun i hi=>(hi.1.paints hi.2).trim)
lemma smul (hs:Cover T k a (fun _=>1) f x)(hc:H l b): Cover T k (b+a) (fun _=>1) (fun i=> l i • f i) x:= by
 obtain ⟨p,hp,H'⟩:=hs.display; exact has (((show H (fun i=>‖l i‖) _ from hc.ab)).mul hp) (H'.mono fun i hi=> hi.smul _)
lemma join (hs:Cover T k a l f x)(hc:Cover T k a l h x): Cover (U:=fun i=>U i×W i) T k a l (fun i t=> (f i t,h i t)) x:= by
 intro e he; obtain ⟨p,hp,h'⟩:=exists_between he; filter_upwards [hs p hp,hc p hp,T.slack h' 2] with i hi hg hG; exact (hi.pair hg).climb (by rw [two_mul] at hG; exact hG.le) le_rfl
lemma comp (ha:0≤a)(hs:Cover T k a (fun _=>1) f x) {u:∀ i,U i→ W i}(hu:Cover T k b (fun _=>1) u (fun i=> f i (x i))) : Cover T k (b+a*k) (fun _=>1) (fun i=> u i ∘ f i) x:= by
 obtain ⟨p,hp,H'⟩:=hs.display; obtain ⟨m,hm,H₃⟩:=hu.display; apply has (g':=fun i=>clump k (p i) (m i)) _ ((H'.and H₃).mono fun i hi=> composite hi.1 hi.2); unfold clump; have ht z: H (fun _=>z) a:= (Clock.Meter.const T z).weak ha; have hv:= ((ht 1).add (((ht 1).add hp).rscale 1)).pow k; exact (hm.lscale _).mul hv
lemma collects {f:ι→∀ i:X,V i→U i} (s:Finset ι)(he:∀ i∈s,Cover T k a (fun _=>1) (f i) x): Cover T k a (fun _=>1) (∑ i∈s, f i) x:= by
 induction s using Finset.induction_on with
 | empty=> rw [Finset.sum_empty]; refine cert (?_) (Eventually.of_forall (fun i y=> ⟨rfl,zero_le_one⟩)); simp_rw [Pi.zero_apply,norm_zero]; exact Clock.Meter.nil T a
 | insert i s hs ih=>rw [Finset.sum_insert hs]; exact (he i (mem_insert_self ..)).add (ih fun i hi=> he i (mem_insert_of_mem hi))
lemma weak (hs:Cover T k a l f x)(he:a≤b):Cover T k b l f x:=fun e hb=> hs _ (he.trans_lt hb)
lemma trim (hs:Cover T k a l f x)(ht:H l b)(he:0≤b): Cover T k (a+b*k) (fun _=>1) f x:= by
 -- reverse display: trim since l rates.P.W
 let g j i:= normJ j (f i) (x i); have hg (j:ℕ)(hj:j≤k):H (g j) (a+b*j) := by
   intro e he; obtain ⟨w,hw,h⟩:=exists_between he; let s:=w-(b*j); have he':a<s:=(by unfold s; linarith); have H':= (((Clock.Meter.pale T s).mul (ht.pow j)) _ (show s+b*j<e by unfold s; linarith))
   filter_upwards [T.positive,hs s he',H'] with i hi hz hp; unfold g; rw [abs_of_nonneg (norm_nonneg _ : 0≤normJ j (f i) (x i))]; exact (hz.order j hj).trans ((le_abs_self _).trans hp)
 intro e he'; filter_upwards [hs (a+1) (by linarith), eventually_all.mpr (show ∀ i:Fin (k+1),∀ᶠ x in T.rail,|(g i.val) x|≤ T.cost x ^e from fun i=> (hg i.val (by have h':= i.isLt; omega)).weak (by gcongr; have h':=i.isLt; simpa using Nat.le_of_lt_succ h') e he')] with i hi hz
 refine Brush.offer.2 ⟨hi.smooth,fun j hj=>(le_abs_self _).trans (hz ⟨j,(by omega)⟩)⟩
end Cover
end YM.AllOrder.Catch
