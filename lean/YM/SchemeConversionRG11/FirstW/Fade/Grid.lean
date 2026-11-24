import YM.SchemeConversionRG11.FirstW.Fade.Lost
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW
open Function Filter Set MeasureTheory Metric Lattice Pert Align Topology Maxwell
open scoped ContDiff Topology BigOperators Classical
variable {T:Itinerary} {c:ℕ→Side}{G:Gauge}
variable {o p r:StepPath T}{A B C:Sight T G}{S:Set E4}{P:Hall T ℝ}{y x z:E4}{a b k:Labels.Key G}{R:ℝ}
def resiteR (T:Itinerary)(k:Hall T ℝ)(o:StepPath T):Hall T ℝ:=fun i x=>k i (x+o i)
def passA (T:Itinerary)(s:StepPath T)(A:Sight T G) : Sight T G:= fun i=> tracing (s i) (A i)
def Mask (T:Itinerary)(o:StepPath T)(Q:Wash): Hall T ℝ:= fun i x=> soft Q (out T i (x-o i))
lemma rose_mask (o:StepPath T)(Q:Wash): Mask T o Q=resiteR T (slide T 0 (soft Q)) (-o):= funext fun i=>funext fun x=> by simp [Mask,resiteR,slide,sub_eq_add_neg]
lemma roseSite (h:Pleased T univ P)(hv:sails T o x) : Pleased T univ (resiteR T P o):=by obtain ⟨Y,H⟩:= h; exact ⟨_,H.resite _ hv _ (fun _ _ => mem_univ _)⟩
lemma warm_site (hp:sails T o x)(Q:Wash) : Pleased T univ (Mask T o Q):= by rw [rose_mask]; exact roseSite (show Pleased T univ (slide T 0 (soft Q)) from ⟨_,slide_scores (soft_price Q) _⟩) (sails_neg hp) -- p implicit?
lemma mask_budget (T:Itinerary)(Q:Wash)(o:StepPath T)(i:ℕ)(x:Site (T.period i)): ‖Mask T o Q i x‖≤ 1 := by
 unfold Mask soft; let p:=out T i (x-o i); have hv : (0:ℝ)< Fintype.card Signed:= Nat.cast_pos.mpr Fintype.card_pos
 rw [norm_mul, Real.norm_of_nonneg (by positivity), inv_mul_le_iff₀ hv]; exact (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i (_:i∈_)=> show ‖Q (Ortho.move i.ortho p)‖ ≤ 1 from by rw [Real.norm_of_nonneg Q.nonneg]; exact Q.le_one)).trans_eq (by simp))
lemma iced_way (o:StepPath T)(Q:Wash) : Leeway T o (1-Mask T o Q):=by
 refine ⟨Q.rIn/2,half_pos Q.rIn_pos,Eventually.of_forall fun i x hx=>?_⟩
 by_contra! h; refine hx ?_; simp only [Pi.sub_apply,Pi.one_apply]; rw [Mask,soft_clear,sub_self]; apply le_trans (high_at _ (T.positive i).le); unfold Gulf growsOut at h; linarith [T.positive i]
lemma mask_placed (Q:Wash) : Placed T Q.rOut (Mask T 0 Q) := Eventually.of_forall fun i x hx=> by by_contra h; apply hx; simp only [Mask,Pi.zero_apply,sub_zero]; exact soft_life Q _ (le_of_lt (lt_of_not_ge h))
lemma resite_mask (o p:StepPath T)(Q:Wash): resiteR T (Mask T o Q) p=Mask T (o-p) Q := funext fun i=>funext fun x=> by simp only [Mask,resiteR,Pi.sub_apply]; rw [show x+p i-o i = x-(o i-p i) by abel]
lemma pass_sea (o s:StepPath T)(a:Labels.Key G): passA T s (SeaA T a o)=SeaA T a (o-s):= funext fun i=> by simp only [passA,SeaA,river,map_smul,consumes]; rfl
lemma riseP (o:StepPath T)(hx:sails T o x)(a:Labels.Key G)(h:S⊆{u|u≠x}): HatP T S (SeaA T a o):=fun i=>⟨_, Score.restrict h (arrived a o hx i)⟩
lemma blotted (he:R<‖x-y‖): Town R ⊆ ({v|v≠x-y}:Set E4):= fun v hv e=> he.not_ge (by rw [← (show v=x-y from e)]; simpa using hv)
lemma ara (o:StepPath T)(Q:Wash): Gloam T P 0 (1-Mask T o Q):=by refine ⟨2,by norm_num,Eventually.of_forall fun i x hx=>?_⟩; simp only [pow_zero,one_mul,Pi.sub_apply,Pi.one_apply]; exact (norm_sub_le ..).trans ((add_le_add_right (mask_budget T Q o i x) _).trans_eq (by norm_num)) -- add right?
lemma waymore {V:Hall T ℝ}(h:Leeway T o P) (hu:∀ i x,V i x≠0→ P i x≠0): Leeway T o V := by obtain ⟨R,hR,H⟩:=h; exact ⟨R,hR,H.mono fun i hi x hx=>hi x (hu _ _ hx)⟩
lemma seats_swap (T:Itinerary) (A B C:Sight T G) (i j:Step)(s:StepPath T): resiteR T (SeatD T A B C i j) s=SeatD T (passA T s A) (passA T s B) (passA T s C) i j:= funext fun l=>funext fun x=> by simp only [resiteR,SeatD,passA,tower_translate]
def CrestBill (T:Itinerary)(A B C:Sight T G)(i j:Step)(P:Hall T ℝ)(s:ℕ) := T.gap s ^ 4 * ∑ x, P s x*SeatD T A B C i j s x
lemma crest_move (i j:Step)(p:Hall T ℝ)(s:StepPath T): CrestBill T (passA T s A) (passA T s B) (passA T s C) i j (resiteR T p s)=CrestBill T A B C i j p:= by -- placeholders
 unfold CrestBill; rw [← seats_swap]; funext k; apply congrArg _; exact Equiv.sum_comp (Equiv.addRight (s k)) (fun x=>p k x * SeatD T A B C i j k x)
lemma near_lattice (Q:Wash)(T:Itinerary){o r p:StepPath T}(hv:sails T o x)(hz:sails T p y)(hk: sails T r z)(hr:Q.rOut<R)(hh:R<‖y-x‖)(hR:R<‖z-x‖)(P:Hall T ℝ)(hp:Pleased T univ P)(a b c': Labels.Key G)(i j:Step)(hg:MarkGrid T c): Helen (CrestBill T (SeaA T a o) (SeaA T b p) (SeaA T c' r) i j (Mask T o Q * P)) := by
 rw [←crest_move _ _ _ o]; let Z:= resiteR T P o; have Hm: resiteR T (Mask T o Q*P) o=Mask T 0 Q*Z:= by
   rw [show Mask T 0 Q=resiteR T (Mask T o Q) o from by rw [resite_mask,sub_self]]; rfl
 rw [Hm,pass_sea,pass_sea,pass_sea,sub_self]
 have H₁ := riseP (p-o) (sails_sub hz hv) b (blotted hh)
 have H₂ := riseP (r-o) (sails_sub hk hv) c' (blotted hR)
 have he : sails T 0 0:= by have H:= sails_sub hv hv; simpa using H
 apply tollD (soggy hg _) H₁ H₂ i j (Mask T 0 Q * Z) (Pleased.squash (S:=univ) ?_ (subset_univ _)) (R:=R) ?_ Q.rOut_pos hr
 · exact (warm_site he Q).map₂ (roseSite hp hv) (ContinuousLinearMap.mul ℝ ℝ)
 exact Eventually.mono (mask_placed Q) (fun i hi x hx => hi x ((mul_ne_zero_iff.mp hx).1))
end YM.RG11.FirstW
