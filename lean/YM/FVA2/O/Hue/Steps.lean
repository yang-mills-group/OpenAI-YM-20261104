import YM.FVA2.O.Hue.Motion
/-!
# Build the approximation at high scales (in physical and exact output space)

Each order separately. Work down the rank axis (number of legs); subtract
at each engineering weight (`shine_price`, `Stage.level`). Have
the additional weight/`eps_gain` suppression of the error terms from `paidC`. Does
not require scale-dependent guesses; one choice through all the needed orders
and test geometry here. See `field_whole`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Hue
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Flux Book High Detect MS.Color MS.Local.Physical MS.Land Domain Convolve
open Lives O.Ward MS.City MS.Rake Outlook Tune O.Pad Submodule Knobs
open scoped Topology ContDiff
variable {I:Type} {G:Gauge}{B:Deck G}{K: Booked B}{M:MS_Data G K}{P:IntervalFamily I}{η:I→ℝ}{n j d k h:ℕ}{X Y:T ( Glade G I )}{f:I→ Law G}
structure LiveR (P:IntervalFamily I)(η:I→ℝ): Prop where
   home: P.beg=0
   days: Every P
   allow: allowance P η
abbrev Starts (P:IntervalFamily I)(X:T ( Glade G I )):= ∀ n,prime P (X n)
structure PactE (M:MS_Data G K)(η:I→ℝ)(P:IntervalFamily I)(h n:ℕ)(X:T ( Glade G I )) : Prop where
    owns : Certified X M η 0
    base : Starts P X
    earlier m (h':m<n): paidC P ( X m ) h
structure Stage (M:MS_Data G K)(η:I→ℝ)(P:IntervalFamily I)(h n k:ℕ)(X:T ( Glade G I )) : Prop extends PactE M η P h n X where
    next r (hv:k<r): width P ( X n ) h r
lemma Stage.keep (H:LiveR P η)(h0:Stage M η P h n k X)(hp:Flame M η P h n k Y f): Stage M η P h n k (X-Y):= {
    owns:= C_sub h0.owns hp.uses.usesC
    base n:= Latch.Lease.minus (h0.base _) (home_price H.home (hp.uses.usesV H.allow) n)
    earlier m hx:= by rw [Pi.sub_apply,hp.low m hx, sub_zero ]; exact h0.earlier m hx
    next r hv:= reaches (h0.next r hv) fun i w _ he=> by unfold sweep; simp only [ Pi.sub_apply,hp.band (index i) (t i) w (by omega),sub_zero] }
lemma StepDust (H:LiveR P η)(h0: Stage M η P h n k X): ∀ i,Mature ( col (X n) i ) false k h:= broadW (h0.owns.1.life n|>.cross) (((plenary M).lives h0.owns.1.life n)|>.cross) H.days (h0.owns.1.vital n) ( h_cost ( h0.owns.1.life n|>.cross ) H.allow decay_p (h0.next (k+2) (by omega)) h0.earlier ) -- omit hd
lemma vanish_step (H:LiveR P η)(hd:d≤h)(h0:Stage M η P h n k X)(he:∀ i,Absent (col (X n) i) false k d)(hx:Flame M η P h n k Y ( flash ( X n ) k d )): ∀ i,Absent (col ((X-Y) n) i) false k (d+1):= by
    intro i l p hv j hu u; have hp:= StepDust H h0 i; let Y0:= flash ( X n ) k d i; let U(t:ℝ):= col (X n) i (0,t); let V(t:ℝ):= col (Y n) i (0,t); have H' t : ContDiff ℝ ∞ ( fieldVal ( V t ) ( ray l ) ):= (booking ((hx.uses.usesC.1.life n).cross) _ _ ).sm _; let Q:= (if fieldDim wfield l+j=(d:ℤ) then Y0 l else 0 ); have hC : Tendsto (fun t=> torch j (U t) l) atTop (𝓝 Q):= (hp.uses (by omega) (he i) 0).1 l p hv j (by omega); have hv(t): torch j (V t) l=Q:= by
       unfold torch; rw [show fieldVal ( V t ) (ray l)=fieldVal Y0 (ray l) from funext (fun v=> hx.top _ _ _ ( by rw [ sail_len,ray_len,hv ] )) ]; exact ( slice_form hp ( v:=(d:ℤ) ) ( by omega ) ).const_term l p
    change Tendsto (fun t=> torch j ( U t - V t ) l ) atTop (𝓝 0); have hZ(t:ℝ): torch j (U t-V t) l=torch j (U t) l-Q:= by rw [torch_sub l (by apply Tune.Gym.sm (f:=fun t=> fieldVal (X n i t) (ray l)); exact booking ((h0.owns.1.life n).cross) _ _) (H' _),hv]
    simp_rw [hZ]; simpa only [ sub_self ] using ( hC.sub_const Q )
abbrev Rest (_P:IntervalFamily I)(X:T ( Glade G I )) (n k d:ℕ): Prop:= ∀ i, Absent ( col ( X n ) i ) false k d
lemma Stage.level (H:LiveR P η)(hd:d≤h+1)(hp:Stage M η P h n k X): ∃ Y, Total η M h P Y ∧ Stage M η P h n k (X-Y)∧ Rest P (X-Y) n k d := by
    induction d with
    | zero=> exact ⟨0, Total.exists0,(by simpa using hp), fun i=> zero_absent _ ⟩
    | succ d ih=>
       obtain ⟨Y,hY,hS,hF⟩:= ih (by omega); have he:d≤h:= by omega
       obtain ⟨Z,hZ⟩:= shine_price H.home H.days he H.allow hS.owns (hS.base n) (hS.next (k+2) (by omega)) hS.earlier hF; refine ⟨ Y+Z,hY.plus hZ.uses,( sub_sub X Y Z ) ▸ Stage.keep H hS hZ,(sub_sub X Y Z) ▸ ?_⟩; intro i; exact_mod_cast ( vanish_step H he hS hF hZ i) -- sub_sub_eq?
lemma Stage.rises (H:LiveR P η)(h0:Stage M η P h n k X)(hr: Rest P X n k (h+1)): width P (X n) h k:= by
    have hP := ( h0.owns.1.life n ).cross; exact continueW hP ((( plenary (η:=η) M ).lives h0.owns.1.life n)|>.cross) H.days ( h0.owns.1.vital n ) H.home ( pinch ( h0.base n ) (fun i=>Bool.noConfusion i) ) ( h_cost hP H.allow decay_p (h0.next (k+2) (by omega)) h0.earlier ) ( fun i=> ( by simpa only [Nat.cast_add,Nat.cast_one] using hr i) )
lemma all_step (H:LiveR P η)(hp:PactE M η P h n X): ∃ Y,Total η M h P Y∧ PactE M η P h (n+1) (X-Y):= by
    obtain ⟨r,hη⟩:= (hp.owns.1.life n).heat; have ht (k:ℕ)(hr:k≤r): ∃ Y, Total η M h P Y∧ Stage M η P h n k (X-Y):= by
       induction hr using Nat.decreasingInduction with
       | self =>
          refine ⟨ 0,Total.exists0,?_⟩; rw [sub_zero]; refine ⟨hp, fun i hi=>?_⟩; apply reaches ( b:=false ) (pinch ( Latch.Lease.zero decay_p ) ( c:=false ) ?z); case z=> exact fun i=>Bool.noConfusion i
          exact fun j w hn hx=> ( hη (index j) (t j) w (by omega) )
       | of_succ k he ih=>
          obtain ⟨Y,hY,hS⟩:= ih; obtain ⟨Z,hZ,hB,hC⟩:= Stage.level H (le_refl (h+1)) hS; refine ⟨ Y+Z,hY.plus hZ,?_⟩; rw [← sub_sub]; refine ⟨ hB.toPactE,fun i hi=>?_⟩; obtain hi|hi:= lt_or_eq_of_le (Nat.succ_le_of_lt hi); exact hB.next i hi; exact hi ▸ Stage.rises H hB hC
    obtain ⟨Y,hY,hS⟩:= ht 0 (by omega); obtain ⟨Z,hZ,hT,hR⟩:=Stage.level H (le_refl (h+1)) hS; refine ⟨ Y+Z,hY.plus hZ,?_⟩; rw [← sub_sub]; refine ⟨hT.owns,hT.base,fun m hm=>?_⟩; rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hx|hx; exact hT.earlier m hx; subst m; apply poses; intro r hx; by_cases he:r=0; subst r; exact Stage.rises H hT hR; exact hT.next r (Nat.pos_of_ne_zero he)
lemma convert_x (H:LiveR P η)(hp:Certified X M η 0)(hr: Starts P X)(n:ℕ)(k:ℕ): ∃ Y, Total η M k P Y∧ PactE M η P k n (X-Y):= by
    induction n with| zero=> refine ⟨0,Total.exists0,?_⟩; rw [sub_zero]; exact ⟨hp,hr,fun m h=>False.elim ((Nat.not_lt_zero m) h)⟩| succ n ih=> obtain ⟨Y,hY,hT⟩:= ih; obtain ⟨Z,hZ,hB⟩:= all_step H hT; exact ⟨ Y+Z,hY.plus hZ,( sub_sub X Y Z ) ▸ hB ⟩
end YM.FVA2.O.Hue
