import YM.Contacts.Milling.Mint
import YM.Contacts.Pulse.Prism
/-! Steam: period steam measurement, real positive orders. No periodic approximations
    at isolated momentum; sum complete root masses. -/
noncomputable section
namespace YM.Contacts.Milling.Steam
open Filter Function Set Finset Lattice RG Wilson Bid Exterior Precision Tree Matrix
open Bloch Stationary Garf Pulse Spine Larch Origin PertExtension.Series MeasureTheory
open Pulse.Form Spark House Radial Forge Next.Free Laurent MergeProof Push.AbsoluteSums Extra.Iteration
open scoped Topology BigOperators Classical Matrix NNReal
variable {α β X Y Z ι D: Type}{l:Range X}{b c d B:ℝ}{F: Field ι X}{G: Field ι Y}{p: X→ Y}{s η:ℝ≥0}
-- deterministic total shadow. Special stub when no anchors exist.
def Launch (_n:Side):= Multiplicative Cover
@[reducible, instance] def launchGroup (n:Side): Group (Launch n):= by unfold Launch; infer_instance
instance waterWay (n:Side): MulAction (Launch n) (Node α) where
   smul t x:= backpack (n.val • (Multiplicative.toAdd t)) x
   one_smul x:= by change backpack (n.val • (0:Cover)) x=x; simp [backpack]
   mul_smul x y z:= Prod.ext (by
      let X:=Multiplicative.toAdd (α:=Cover) x; let Y:=Multiplicative.toAdd (α:=Cover) y; change z.1+n.val • (X+Y)= z.1+n.val • Y+n.val • X; rw [smul_add]; abel) rfl
lemma voyage (n:Side): Gaugeway (lower (α:=α) n) (Launch n):= by
   refine ⟨fun z v=>wrap_slot n z (Multiplicative.toAdd v),fun x y h=>?_ ,fun x a b h=>?_,lower_onto n⟩
   · exact ⟨(show Launch n from Multiplicative.ofAdd (rent n y.1-rent n x.1)),lower_eq n x y h⟩
   have h: berth n x (Multiplicative.toAdd a)=berth n x (Multiplicative.toAdd b):= Subtype.ext h; exact (berth n x).injective h
-- periodization APIs. Teleports
variable {n:Side} {P:House (Node α)}{e k r:ℕ}
def printShadow (F:Field ι (Node α))(n:Side): Field ι (Co n α) := if h:Nonempty ι then (voyage n).lower F else 0
def hair (P:House (Node α)) (n:Side): House (Co n α):= fun e r=> printShadow (P e r) n
lemma focused [Nonempty ι](h:Shadow p F G)(hp:Surjective p){g:Field ι Y}(he:Shadow p F g) : G=g:= by
   funext x; let j:= Classical.arbitrary ι; obtain ⟨b,hb⟩:=hp (x j); exact (h.rule x j b hb).trans (he.rule x j b hb).symm
lemma heritage {F:Field ι (Node α)} (h:∀ a:Cover,Mirrored (backpack a) F) (n:Side) : Carried (Launch n) F:= fun i=> h _
lemma printFeeds {F:Field ι (Node α)}(h: Carried (Launch n) F): Shadow (lower n) F (printShadow F n):= by rcases isEmpty_or_nonempty ι with H|H; exact fun i=> isEmptyElim i; rw [printShadow,dif_pos H]; apply Gaugeway.lower_shadow _ h
lemma shadowEven {F:Field ι (Node α)}(h: Carried (Launch n) F)(hp:Poem F): Poem (printShadow F n):= by
   intro e t; rcases isEmpty_or_nonempty ι with g|g; · rw [printShadow,dif_neg (not_nonempty_iff.mpr g)]; rfl -- printShadow,g,not_nonempty_iff]
   let q:=printShadow F n; have he: Shadow (lower n) F q:=printFeeds h; have hh: Shadow (lower n) F (reorder e q):= by
     let ht:= he.replace (e:=e.symm); have hv : reorder e F=F:= funext (hp e); exact hv ▸ (show Shadow (lower n) (reorder e F) (reorder e q) from ht)
   exact congr_fun (focused hh (lower_onto n) he) t
lemma printLull : printShadow (n:=n) (0:Field ι (Node α))= (0:Field ι (Co n α)) := by rcases isEmpty_or_nonempty ι with g|g; rw [printShadow,dif_neg (not_nonempty_iff.mpr g)]; exact focused (printFeeds (fun _ _=>rfl)) (lower_onto n) (Shadow.empty _)
-- need stage and comparisons across m; use cheap on PERIODIC, exponential suffices in amount

def voyageW (m:Side)(s:ℝ≥0)(α:Type) : MirrorWay (lower m) (Launch m) (terrain s α) (Range.cheap (Co m α)) where
   gears:= voyage m
   t:= terrain s α
   closed a b x y:= by change _*1≤ _; rw [mul_one]; exact le_max_left ..
lemma together_due {F:Field ι (Node α)}{Q:Field ι (Co n α)}[Fintype ι] (h: Carried (Launch n) F)(hp: Rooted (terrain s α) F b)(he:Shadow (lower n) F Q): Two (voyageW n s α) F Q b 0:= ⟨h,hp,(he.cost hp (voyageW ..|>.lower) (lower_onto n)),Q,he,by rw [sub_self]; exact Rooted.tranquility _⟩
-- fin & cheap range bills
lemma ticket (z:Cover)(x:Node α)(y:Node β)(s:ℝ≥0): (terrain s Unit).step ((backpack z x).1, ()) ((backpack z y).1,())= (terrain s Unit).step (x.1, ()) (y.1,()):= by simp [backpack]
def tunnel (s:ℝ≥0)(x:Node α)(y:Node β):= (terrain s Unit).step (x.1, ()) (y.1,())
lemma fareFoot : Ripple (terrain s α) (terrain s β) (tunnel s):= ⟨fun _ _=>Range.one_fee _,fun i j k l=> (Range.echo (terrain s Unit)).span (i.1, ()) (j.1, ()) (k.1, ()) (l.1,())⟩
lemma flight_stem {R: Row α β} [Fintype α][Fintype β] (h:R.strip s b)(hp:0≤b): Weirs (tunnel s) (plane R) ((Fintype.card α:ℝ)*b) ((Fintype.card β:ℝ)*b):= by
   refine ⟨by positivity,by positivity,fun y=> ?_,fun x=> ?_⟩
   · let Y (x:Node α):= (x.2,y.1-x.1); have hy: Injective Y:= by intro p q hp; simp [Y] at hp; exact Prod.ext hp.2 hp.1
     let E := Extra.Iteration.Cost.product (F:=fun z:α×Cover=> Real.exp ((s:ℝ)*Laurent.size z.2)*‖R z.1 y.2 z.2‖) (Cost.finite b hp) (fun i=> h i y.2); apply budget_map E Y hy (fun x=> by exact mul_comm ..)
   let Y (y:Node β):=(y.2,y.1-x.1); apply budget_map (Cost.product (F:=fun z:β×Cover=> Real.exp ((s:ℝ)*Laurent.size z.2)*‖R x.2 z.1 z.2‖) (Cost.finite b hp) (fun i=> h x.2 i)) Y; · intro p q hp; simp [Y] at hp; exact Prod.ext hp.2 hp.1
   intro p; exact mul_comm ..
lemma flat_ripple : Ripple (Range.cheap α) (Range.cheap β) (fun _ _=>1) := ⟨fun _ _=>le_rfl,fun p q x y=>by change (1:ℝ) ≤ 1*1*1; simp⟩
lemma inners (w:X→ℝ)(b:ℝ){t:X→ℝ}(h:SumBudget (fun x=> ‖w x‖*t x) b)(q:Y→ℝ){p:X→Y}(hp:Scroll p w q)(ht:∀ x,1≤t x) : SumBudget (fun x=> ‖q x‖*1) b:= by
   have hh : SumBudget (fun x=> ‖w x‖*1) b:= budget_mono h (fun _=> mul_nonneg (norm_nonneg _) zero_le_one) (fun i=>mul_le_mul_of_nonneg_left (ht i) (norm_nonneg _)); exact hp.cost (fun i=>zero_le_one) (by apply Summable.of_norm; simpa using hh.2.1) hh
lemma seats {m:Range Z}{t:X→ Z→ ℝ}{G:X→ Z→ℝ}{K:Y→D→ℝ}{q:Z→D} (h:Ripple l m t)(hp:Weirs t G b c)(hv:Trails p q G K)(hz:Surjective p)(he:Surjective q) : Weirs (fun _ _=>1) K b c := by
  refine ⟨hp.left,hp.right,?_,?_⟩; · intro y; obtain ⟨t,rfl⟩:=he y; exact inners _ _ (hp.columns t) _ (hv.col t) (fun i=> h.one i t)
  intro x; obtain ⟨i,rfl⟩:=hz x; exact inners _ _ (hp.rows i) _ (hv.row i) (fun v=>h.one i v)

-- root-cost inflow factor r
lemma flat_track {α:Type}{g:Node α→Node α→ℝ} {K:Co n α→Co n α→ℝ} (h:Track (terrain s α) g b)(hp:Trails (lower n) (lower n) g K): Track (Range.cheap _) K b:= by
  have hz:=seats (Range.echo _) h.flow hp (lower_onto n) (lower_onto n); exact ⟨h.cash, hz.rows,hz.columns⟩
lemma difference_far (n:Side)(s:ℝ≥0) : ∀ (x y:Node α), x≠y→lower n x=lower n y → Real.exp (s*(n.val:ℝ)) ≤ (terrain s α).step x y:= by
   intro x y hx he; let t:= rent n y.1-rent n x.1; have hp: backpack (n.val • t) x=y:= lower_eq _ _ _ he; have ht:t≠0:= fun q=> hx (Eq.trans (Prod.ext (by rw [show y.1=_ from (congr_arg Prod.fst hp).symm]; simp [backpack,q]) (show x.2=y.2 from (congr_arg (fun z:Co n α=>z.2) he))) rfl)
   obtain ⟨i,hi⟩:= Function.ne_iff.mp ht; simp only [terrain_step]; apply Real.exp_monotone; gcongr; suffices h:n.val ≤ size (y.1 - x.1) by exact h -- maybe asked ℕ
   rw [←hp]; have hu:=single_le_sum (s:=Finset.univ) (f:=fun j=> (n.val*(t j).natAbs)) (fun _ _=> Nat.zero_le _) (Finset.mem_univ i); change n.val≤ Laurent.size ( (x.1+n.val • t) - x.1); rw [add_sub_cancel_left]; simp only [Laurent.size, Pi.smul_apply,nsmul_eq_mul,Int.natAbs_mul, Int.natAbs_natCast]; exact le_trans (Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hi)) hu

def hush (s:ℝ≥0)(n:Side) := (Real.exp (s*(n.val:ℝ)))⁻¹
lemma torch {g:Node α→Node α→ℝ}{K:Co n α→Co n α→ℝ} (h:Track (terrain s α) g b)(hp:Trails (lower n) (lower n) g K) (he:∀ x y z,g (backpack z x) (backpack z y)=g x y) : Waves (voyageW n s α) g K b (hush s n*b) 0:= by
 let B:=flat_track h hp; refine ⟨h,B,fun i j t=> he _ _ _, mul_nonneg (inv_nonneg.mpr (Real.exp_pos _).le) h.cash,K,hp,B,by simp only [sub_self]; constructor; rfl; all_goals intros; simpa using budget_zero, fun x y=> (winding_cost h hp (Real.exp_pos _) (difference_far n s) x y).trans_eq ?_⟩
 unfold hush; change _ = _ * ((terrain s _).step x y); ring
lemma hoist_pay {m:Range Y}{t:X→Y→ℝ}{R:X→Y→ℝ}{F:Field (Fin k) X} (h:Ripple l m t)(hp:Weirs t R b c)(hv:Rooted l F B): Rooted m (hoist R F) (b* B * c^(k-1)) := by
   apply Rooted.even; exact all_root hv h (fun _=> hp) (fun i=> (by simp)) (mul_nonneg (mul_nonneg hp.left hv.cash) (pow_nonneg hp.right _))
lemma hoist_period {X Y α β:Type}{l:Range X}{m:Range Y}{t:X→ Y→ ℝ}{F:Field (Fin k) X}{G:Field (Fin k) α}{R:X→Y→ℝ}{K:α→ β→ℝ}{p:X→α}{q:Y→β} (h:Ripple l m t)(hp:Weirs t R b c)(hv: Rooted l F B)(hh:Shadow p F G)(hz:Trails p q R K): Shadow q (hoist R F) (hoist K G):= by
   cases k; exact fun i=> Fin.elim0 i; rename_i k; refine (basin hh (fun _=> hz) hv h (fun _=> hp)).even (all_root (d:= b*B*c^k) hv h (fun _=> hp) ?_ ?_); rotate_left; · exact mul_nonneg (mul_nonneg hp.left hv.cash) (pow_nonneg hp.right k) -- implicit succ not inferred
   intro i; simp
lemma hoist_comp (R:Row α β)(n:Side)[Fintype α][Fintype β]{s:ℝ≥0} (h:R.strip s b)(ha:0≤b){F:Field (Fin k) (Node α)}{P:Field (Fin k) (Co n α)}(he: Two (voyageW n s α) F P B c) : let i:ℝ:=Fintype.card α*b; let j:ℝ:=Fintype.card β * b; Two (voyageW n s β) (hoist (plane R) F) (hoist (R.acts n) P) (i*B*j^(k-1)) (i*c*j^(k-1)):= by
   intro i j; have hi:= flight_stem h ha; have hz:= row_ship R n; have hv:= seats fareFoot hi hz (lower_onto n) (lower_onto n); obtain ⟨V,hT,hV⟩:= he.owes; let f:= hoist (r:=k) (R.acts n); refine ⟨fun j=> print_mirror (e:= MulAction.toPerm j) _ (mir_allAt (e:=MulAction.toPerm j) (he.risen j) (fun i x y=>?_)), hoist_pay fareFoot hi he.ground, hoist_pay flat_ripple hv he.seats, f V,hoist_period fareFoot hi he.ground hT hz,?_⟩
   · change plane R (backpack _ x) (backpack _ y) = _; simp [plane,backpack]
   -- finite lin
   suffices ha: f (P-V)= f P-f V by change Rooted _ (f P-f V) _; rw [←ha]; exact hoist_pay flat_ripple hv hV
   unfold f hoist; ext1 i; simp [printRun,reorder,allAt,sum_sub_distrib,sub_mul,tsum_fintype,mul_sub]
section
variable {V:Equiv.Perm X}
def Dorm (V:Equiv.Perm X) (F:House X) := ∀ i r, Mirrored V (F i r)
lemma harvest {F:α→Field ι X}(s:Finset α)(h:∀ i∈s,Mirrored V (F i)): Mirrored V (∑ i∈s,F i):= fun x=> by simp_rw [Finset.sum_apply]; exact sum_congr rfl fun i hi => h i hi _
lemma bend (h: Mirrored V F)(b:ℝ): Mirrored V (b • F):= fun x=> congr_arg (b*·) (h x)
lemma dent {R:Node α→Node β→ℝ}{W:Field (Fin k) (Node α)}{v w:Cover}(h: Mirrored (backpack w) W)(hk:∀ x y,R (backpack w x) (backpack v y)=R x y): Mirrored (backpack v) (hoist R W):= print_mirror _ (mir_allAt h (fun _=> hk))
lemma convect {G:X→X→ℝ}{F:House X}(h:∀ i j,G (V i) (V j)=G i j)(hp:Dorm V F)(n:ℕ): Dorm V (gathering G F n):= by
    induction n using Nat.strongRecOn with | _ n ih=>
    cases n with
    | zero=> rwa [gathering]
    | succ n=>
      intro e r; rw [gathering_next]; apply bend; let Z:= gathering G F
      have hs: Mirrored V (Pulse.degree G (Z n e (r+2))) := bend (print_mirror _ (mir_loop (fun i=>(ih n (by omega) e (r+2)) _) h)) _
      have he: Mirrored V (∑ p∈antidiagonal e,∑ q∈antidiagonal n,listPay G (Z q.1 p.1) (Z q.2 p.2) r):= harvest _ fun i _=> harvest _ fun j hj=> harvest _ fun k hk=>by
        have hi:= ih j.1 (by have hh:= mem_antidiagonal.mp hj; omega); have hp:=ih j.2 (by have hh:= mem_antidiagonal.mp hj; omega); obtain ⟨x,y⟩:=k; have hx: x+y=r:= mem_antidiagonal.mp hk; subst r; unfold light; rw [dif_pos (by rfl)]; refine bend (print_mirror _ (fun g=>?_)) _; exact (mir_stitch (G:=G) (e:=V) (F:=squeeze (gathering G F j.1 i.1 (x+1))) (K:=squeeze (gathering G F j.2 i.2 (y+1))) h (fun t=> hi i.1 (x+1) _) (fun t=>hp i.2 (y+1) _) (g ∘ finSumFinEquiv)) -- e, reorder commute
      intro x; exact congr_arg₂ (·+·) (hs x) (he x)
lemma levitate {G:X→X→ℝ}{F:House X}(h:∀ i j,G (V i) (V j)=G i j)(hp:Dorm V F): Dorm V (massaged G F):= fun i r=> harvest _ fun p _=> convect h hp p i r
lemma wakeup_fees (a b c x d : ℝ)(P H:TableFee)(n k e:ℕ): lowland a (x*b) (x*c) P (x • H) n k e= x*lowland a b c P H n k e:= by
    induction n using Nat.strongRecOn generalizing k e with| _ n ih=>
    cases n with
    | zero=> rw [lowland,lowland]; rfl
    | succ n=> rw [mazy,mazy,mul_left_comm]; unfold wakeup; rw [mul_add x]; refine congr_arg₂ _ rfl (congr_arg₂ _ ?_ ?_); · rw [ih n (by omega)]; ring
               simp_rw [mul_sum]; refine sum_congr rfl fun i hi=> sum_congr rfl fun j hj=> sum_congr rfl fun k hk=> ?_; have ht:= mem_antidiagonal.mp hj; unfold lichtQ; rw [ih j.1 (by omega),ih j.2 (by omega)]; ring
end
end YM.Contacts.Milling.Steam
