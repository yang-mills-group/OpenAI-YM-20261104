import YM.FVA2.O.Tune.Reach
/-!
# Ward condition on the FAR Taylor slices

`X_closed`: at every placement i in a fixed family, see the free
Ward-closed identity on the Taylor slices when taking limits to extract
at the given rank and engineering weight. Use in `O/Hue`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Tune
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Flux Book High Detect MS.Color MS.Local.Physical MS.Land Domain Convolve
open Lives O.Ward MS.City MS.Rake Outlook
open scoped Topology ContDiff
variable {E I:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
variable {G:Gauge} {F Y H:Glade G I}{B:Deck G}{K:Booked B}{M:MS_Data G K}{η:I→ℝ}{P:IntervalFamily I}{n j k r:ℕ}{b h u:ℤ}{i:P.Inst}{x:E}
variable {w:Wire (BH G) E QP}{a:P.Inst→ℝ}{X:T (Glade G I)}
def decay (P:IntervalFamily I)(h:ℤ) : P.Inst→ℝ:= fun i=> P.primary.length i ^ (-h)*rate P eps_gain i
lemma decay_p : Latch.nn ( decay P h ):= fun _=> mul_nonneg (length_p ..) (exp_pos _|>.le)
lemma decay_next : decay P (h+1)= die P*decay P h:= by ext i; unfold decay; rw [neg_add_rev, zpow_add₀ (P.primary.pos i).ne',zpow_neg_one, mul_assoc]; rfl
lemma value_h (i:P.Inst): P.primary.length i ^ pitch w * decay P h i = pays 1 ((fieldDim wfield w-h:ℤ)-eps_gain) i:= by unfold decay; rw [← mul_assoc,← zpow_add₀ (P.primary.pos i).ne',← sub_eq_add_neg]; exact Plane.small_fact P eps_gain _ i
lemma absolute (i:P.Inst)(h:ℤ)(w:Legs (Lane4 G)): P.primary.length i ^ fieldDim wfield w * decay P h i = P.primary.length i ^ (fieldDim wfield w-h) * rate P eps_gain i:= by unfold decay; rw [← mul_assoc, ← zpow_add₀ (P.primary.pos i).ne']; rfl
abbrev width (P:IntervalFamily I)(F:Glade G I)(h:ℤ)(k:ℕ): Prop:= Lens false P.primary (sweep P F) (decay P h) k
abbrev paidC (P:IntervalFamily I)(F:Glade G I)(h:ℤ): Prop:= Latch.Lease false false P.primary (sweep P F) (decay P h)
abbrev canvas (F:Glade G I)(w:Wire (BH G) E QP): I→ℝ→ E→ℂ:= fun i t=> fieldVal (F i t) w
lemma caption : Cape P.primary (sweep P F) (decay P h) w ↔ Bound P.primary (here (canvas F w)) (pays 1 ((fieldDim wfield w-h:ℤ)-eps_gain)):= by rw [Cape,funext (fun i=> value_h (P:=P) i )]; rfl
lemma U0 {c:Bool}(w:Wire (BH G) E QP)(hx:Lens c P.dawn (fun i=>F i 0) 1 w.length)(hr:Course c w)(hp:P.beg=0): Bound P.dawn (fun i=> fieldVal (F i (P.beg i)) w) (fun i=>pays 1 ((fieldDim wfield w-h:ℤ)-eps_gain) (P.start i)):= by
    obtain h:=hx E w rfl hr; unfold pays; simp only [ show ∀ i, t (P.start i)= (0:ℝ) from fun i=> congr_fun hp i, show ∀ i, P.beg i=(0:ℝ) from fun i=> congr_fun hp i, mul_zero,exp_zero, Pi.one_apply,mul_one ]; exact h.raise ( Cost.of_le fun i p _=>(show P.dawn.length i^pitch w*1≤1 from by simp [hp] ) )
abbrev Every (P:IntervalFamily I) : Prop:= ∀ i,P.window i=Set.Ici (P.beg i)
lemma limitsW (hT:Every P)(ha:Warm F false)(hv:Warm H false)(hp:Velocity F H)(hx:width P H h w.length)(hz:fieldDim wfield w+j≤h)(i:I): ∃ k,Tendsto (fun t=>iteratedFDeriv ℝ j ( canvas F w i t ) 0) atTop (𝓝 k):= (P.needs_limit (fun _=>zero_le_one) (Track_now P ha hv hp w j) ((caption.mp (hx E w rfl (fun i=>Bool.noConfusion i))).quoted j) (( int_need p_gain s_gain ).mpr (show (fieldDim wfield w-h:ℤ)+j≤0 from by omega)) hT i)
abbrev col (F:Glade G I)(i:I): Reading G:=fun x=>F i x.2
lemma broadW (hv:Warm F false)(ht:Warm H false)(he:Every P)(hp:Velocity F H)(hx:width P H h r)(i:I): Mature (col F i) false r h:= by
    refine ⟨ fun E _ _ w _ _ _ t=> (booking hv i w).sm t, fun E _ _ w _ hr j hz _=>limitsW he hv ht hp ( hr.symm ▸ hx ) hz i ⟩
lemma continueW (hv:Warm F false)(ht:Warm H false)(he:Every P)(hp:Velocity F H)(hT:P.beg=0)(hI:Lens false P.dawn (fun i=>F i 0) 1 r)(hx:width P H h r)(hL:∀ i, Absent ( col F i ) false r (h+1)): width P F h r:= by
    intro E _ _ w hw hz; apply caption.mpr; exact P.comparison ( fun _=>zero_le_one ) he (Track_now P hv ht hp w) (fun i=> (booking hv _ w).sm _) (caption.mp (hx E w hw hz)) (U0 w ( hw.symm ▸ hI ) hz hT) (fun j hj i=> ( broadW hv ht he hp hx i ).enough (hL i) hz hw hj 0 )
lemma barZ [Nonempty I] (P:IntervalFamily I)(G:Gauge) : Charge.Criteria P ( A:= Leg Axis G.ColorIndex ) wfield eps_gain (send id) (send id) := by
    obtain h:= criterion (R:=P) (C:=G.ColorIndex) (A:=Axis) (primary_large s_gain.le); exact ⟨ fun i j=> Like.same (fun _=>exp_pos _|>.le ) (h.cost i j|>.std), h.shape⟩
def flash (F:Glade G I)(k:ℕ)(u:ℤ)(i:I): Law G:= High.slice ( col F i ) false k u 0
lemma rankQ {X:Law G}(h:Ranked false r X): Ranked false r (natQ X):= by
    intro w hp hw; rw [natQ,visit_Z]; have hz : ∀ l i k, l++i::k=w→ ∑ j:Branch G Axis,(send id).table i.1 j i.2*X (l++(j,i.2)::k)=0:= by intro l i k hi; exact Finset.sum_eq_zero fun j hj=> mul_eq_zero_of_right _ (h _ (fun i=>Bool.noConfusion i) (by simpa only [← hi,List.length_append,List.length_cons] using hw))
    rw [visit_agree _ _ (V:=fun _ _ _=>0) hz,visit_zero]
lemma W_torch {w:List ( Lane4 G )}(he: Warm F false)(hy:u ≤ h)(hr:∀ i, Mature ( col F i ) false w.length h)(hx:∀ i, Absent ( col F i ) false w.length u)(hT:Every P)(hp:width P ( Lives.Z G I F ) (h+1) w.length)(i:I): natQ ( flash F w.length u i ) w=0:= by
    haveI : Nonempty I:= ⟨i⟩; let M (p:Clock I):= F p.1 p.2; apply Plane.class_kernel (M:=M) (b:=false) (barZ P G) hT p_gain s_gain u hy (fun i=> Bool.noConfusion i) (fun w _ _ t=> (booking he t.1 _).sm t.2) i ?_ ?cost; · exact ( hr i ).uses hy (hx i) 0
    obtain hh:= (hp ℝ (ray w) (ray_len ..) (fun i=>Bool.noConfusion i)); unfold Cape at hh; simp_rw [pitch,ray_dim] at hh; exact hh.raise (Cost.of_le fun i p _=>( absolute i (h+1) w ).le )
lemma X_closed (hV: O.Lives.Certified X M η 0)(hy:u ≤ h)(he:allowance P η)(ht:Every P)(hp:width P (X n) h (r+2))(hq:∀ m<n,paidC P (X m) h)(hx:∀ i, Absent ( col (X n) i ) false r u)(i:I): natQ ( flash ( X n ) r u i ) =0:= by
    have hJ:=hV.1; have hv:Warm ( helm M η X n ) false:= ((( plenary M ).lives hJ.life) n).cross; obtain he':= hJ.life n |>.cross; obtain hη:= broadW he' hv ht (hJ.vital n) ( h_cost he' he decay_p hp hq ); obtain hQ:width P ( Lives.Z G I (X n) ) (h+1) r:= by unfold width; rw [decay_next]; exact Q_ok hV decay_p he hp hq
    funext w; by_cases hr:w.length=r; · subst r; exact W_torch he' hy hη hx ht hQ i
    exact (rankQ ( X:=flash ( X n ) r u i ) High.rank_slice ) w (fun i=>Bool.noConfusion i) hr
end YM.FVA2.O.Tune
