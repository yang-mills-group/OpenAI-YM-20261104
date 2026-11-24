import YM.FVA2.Extras.Theater
/-! # Linearity for the Lucent/assessment reduction

Auxiliary to `YM/FVA2/Extras/Result.lean`. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Extras
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal O
open O.Lives MS.City MS.Rake O.Tune Flux Book Convolve O.Serve O.Pad Vane High Detect O.Ward
open MS.Local.Physical MS.Land Outlook Rough Emit
open scoped Topology ContDiff Interval BigOperators
open Job.Belt Rake.Geo O.Hue O.Fuse O.Cool
variable {I E:Type}{G:Gauge}{B:Deck G}{K:Booked B}{M:MS_Data G K}{P:Geo I} {F Z U W V:T (Glade G I)} {a:I→QP}{b:ℤ}{k:ℕ}{X Y:E→ T (Glade G I)}{u:ℝ}
def nest (L:List (Cart G I))(a:I→QP) : MH ( T (Glade G I) ) where
    toFun T:= merge G I L (a,T)
    map_add' X Y:= by induction L with| nil=> exact map_add (swing G a) X Y | cons i l ih=> rw [merge,ih,map_add]; rfl
    map_smul' z X:= by induction L with|nil=> exact map_smul (swing G a) z X| cons i l ih=> rw [merge,ih,map_smul]; rfl
variable {L:List (Cart G I)}
abbrev Source (F:T (Glade G I)) (u:T ℝ):= entrance (fun i (_:I)=>u i) F
abbrev row (F:T (Glade G I))(u:T ℝ)(n:ℕ):= Hue.hall (fun i (_:I)=>u i) F n
lemma draw (H:sameΛ k F Z): sameΛ k (nest L a F) (nest L a Z):= by
    induction L with| nil => intro n hn; exact congr_arg ( Serve.tilt G a ) (H n hn) | cons i l IH=> exact pairΛ _ ( swing G i.1 i.2 ) IH
lemma pay (k:ℕ) : nest L a (hold0 k F)=hold0 k (nest L a F):= by
    induction L with
    | nil=> exact split_Z ( Serve.tilt G a )
    | cons i l IH=> change bond G I _ ( nest l a (hold0 k F))=_; rw [IH]; exact split_h _
lemma row_s (u:T ℝ)(n:ℕ): row F u n=∑ i∈ Finset.range (n+1),hold0 i ((u i:ℂ) • F):= rfl
lemma circleN (u:T ℝ) : nest L a (Source F u)=Source (nest L a F) u:= by
    funext n; rw [ ← show nest L a (row F u n) n= nest L a (Source F u) n from draw (fun i h=>hereΛ h) n (le_refl n), ← show row (nest L a F) u n n=Source (nest L a F) u n from hereΛ (le_refl n),row_s,row_s,map_sum ]; simp_rw [pay,map_smul]
lemma shade (h:Lucent P M b V U) (g:ℝ): Lucent P M b ((g:ℂ) • V) ((g:ℂ) • U):= ⟨ Response.scale h.1 (fun _=>g),(by rw [← smul_sub ]; exact h.2.scale _ ) ⟩
lemma added (he:Lucent P M b V W)(hr: Lucent P M b U Z): Lucent P M b (V+U) (W+Z):= by refine ⟨ he.1.add hr.1,?_ ⟩; rw [show V+U-(W+Z)= V-W+(U-Z) from (by abel) ]; exact he.2.add hr.2
lemma summing (A:Finset E)(he:∀ i∈A, Lucent P M b ( X i ) ( Y i )): Lucent P M b (∑ i∈ A,X i) (∑ i∈A,Y i):= by classical induction A using Finset.induction_on with| empty=> simp only [Finset.sum_empty]; exact ⟨ Response.zero,(by simpa only [sub_zero] using Sweep.unit) ⟩| insert i s hi ih=> rw [ Finset.sum_insert hi,Finset.sum_insert hi ]; exact added (he i (by simp)) (ih fun j hj=> he j ( mem_insert_of_mem hj ))
lemma aria (he:Lucent P M b V W): Lucent P M b (hold0 k V) (hold0 k W):= by
    refine ⟨ shift_Response he.1,?_⟩; intro i; rw [Pi.sub_apply]; by_cases hi:k≤ i; rw [hx_holder hi,hx_holder hi]; exact he.2 _; rw [low_hold (by omega), low_hold (by omega),sub_zero]; exact Nilp.zero
lemma freed (he:Lucent P M b V W)(u:T ℝ): Lucent P M b (Source V u) ( Source W u ):= by
    have H(i:ℕ): Lucent P M b (row V u i) (row W u i):= by rw [row_s,row_s]; exact summing _ fun i _=> aria ( shade he ( u i ) )
    have ht (U:T (Glade G I))(i:ℕ): sameΛ i (row U u i) (Source U u):= fun j hj=>hereΛ hj
    refine ⟨ ⟨ fun i=> ( show row V u i i=Source V u i from hereΛ (le_refl i) ) ▸ ( H i ).1.life i,fun i=>?_ ⟩,( fun i=>?_ )⟩;
    · rw [← ht V i i (le_refl i),← show helm M P.η (row V u i) i=helm M P.η (Source V u) i from commuteΛ _ _ _ (ht V i) i (le_refl i) ]; exact (H i).1.vital i
    rw [Pi.sub_apply,← ht V i i (le_refl i), ← ht W i i (le_refl i) ]; exact ( H i ).2 i
abbrev assessment (F:T (Glade G I))(x:I): T ℂ:= fun i=> blade (F i) x
lemma grants_plus (x:I)(hp:Response U M P.η b)(hv:Response W M P.η b): assessment (U+W) x=assessment U x+assessment W x:= funext fun i=> tendsto_nhds_unique ( total_peak (hp.add hv) x i ) ((total_peak hp x i).add (total_peak hv x i))
lemma grants (x:I)(he:Lucent P M b V W) (u:T ℝ): assessment (Source V u) x k=∑ i∈Finset.range (k+1), (u i:ℂ)* assessment V x (k-i):= by
    refine tendsto_nhds_unique ( total_peak ( freed he u ).1 x k ) ?_; unfold Source entrance; simp_rw [ Finset.sum_apply ]; convert! tendsto_finsetSum _ (fun i (hi:i∈Finset.range (k+1))=> (( total_peak he.1 x ( k-i ) ).const_mul ( u i:ℂ )) ) using 2; exact Finset.sum_congr rfl fun i hi=> by rw [ hx_holder (by obtain hh:= mem_range.mp hi; omega) ]; rfl
lemma grants_all (x:I)(s:Finset E) (he:∀ i∈s,Response (X i) M P.η b): assessment (∑ i∈s,X i) x = ∑ i∈s,assessment (X i) x:= by classical induction s using Finset.induction_on with| empty=> rw [ Finset.sum_empty,Finset.sum_empty ]; exact funext fun i=> Filter.Tendsto.limUnder_eq (f:=atTop) (g:=fun (_:ℝ)=> (0:ℂ)) tendsto_const_nhds| insert i s hi ih=> rw [ Finset.sum_insert hi, Finset.sum_insert hi,grants_plus x ( he i (by simp) ) ( Response.all_fin _ (fun j hj=> he j ( mem_insert_of_mem hj ))),ih (fun j hj=> he j (mem_insert_of_mem hj) )]
end YM.FVA2.Extras
