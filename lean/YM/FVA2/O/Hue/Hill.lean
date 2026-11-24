import YM.FVA2.O.Hue.Amber
/-!
# Physical + exact output space for the FAR approximation

`Total`: the required form (including the coefficient budgets, and
allowing the image under `nav` of a degree -1 generator). See
`Steps` and `Filled` to use this. No OPE assumptions in the final theorem.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Hue
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Flux Book High Detect MS.Color MS.Local.Physical MS.Land Domain Convolve
open Lives O.Ward MS.City MS.Rake Outlook Tune O.Pad
open scoped Topology ContDiff
variable {I J E:Type} {G:Gauge}{B:Deck G}{K: Booked B}{M:MS_Data G K}{P:IntervalFamily I}{η:I→ℝ}{n d k h:ℕ}{b t:ℤ}{X Y:T ( Glade G I )}{a b':I→ℝ}
-- `C.L`: field horizon explicit
abbrev Counter (B:Deck G)(h:ℕ):= Σ d:Fin (h+1), Plaid B d.val
abbrev Details (B:Deck G)(I:Type)(h:ℕ) := Counter B h→ T ( I→ℝ )
def roadZ (η:I→ℝ)(M:MS_Data G K)(i:Counter B h): T ( Glade G I ):= soloV i.1.val η M i.2
def Physical (η:I→ℝ)(M:MS_Data G K)(f:Details B I h) : T ( Glade G I ):= ∑ i:Counter B h, entrance (f i) (roadZ η M i)
abbrev Valid (P: IntervalFamily I)(f:Details B I h): Prop:= ∀ i n,Profit P.dawn (f i n)
variable {s p:Details B I h}
lemma V_road (h: allowance P η)(i: Counter B k): Certified (roadZ η M i) M η 0 ∧ Reps (roadZ η M i) i.1.val P:= ⟨Certified.first _,repreprice h ( M.markOK _ _ )⟩
lemma V_plus (h: Valid P s)(hv:Valid P p): Valid P (s+p):= fun i n=> (h i n).plus (hv i n)
lemma H_add (p q: Details B I k): Physical η M (p+q)= Physical η M p+Physical η M q:= by unfold Physical; simp_rw [Pi.add_apply,exact_f, Finset.sum_add_distrib]
lemma PH_C : Certified (Physical η M s) M η 0:= C_ο _ (fun _ _=> entrance_C _ (Certified.first _) ) -- unif
lemma PH_V (hp: allowance P η)(hx: Valid P s): Reps (Physical η M s) 0 P:= Reps_sum Finset.univ (fun i _=> volume_C ( Reps_desc ( V_road hp i ).2 (Int.natCast_nonneg _) ) (hx i))
lemma H_zero : Physical η M (0:Details B I k)=0:= by unfold Physical; simp only [Pi.zero_apply,exact_z,Finset.sum_const_zero]
lemma singled (x: Counter B k)(f:T ( I→ℝ )): Physical η M ( ( Pi.single x f ):Details B I k ) = entrance f (roadZ η M x):= by unfold Physical; rw [ Finset.sum_eq_single x, Pi.single_eq_same]; intro i hi hp; rw [Pi.single_eq_of_ne hp,exact_z]; simp
-- inclusion of primitives and budget.
def Total (η:I→ℝ)(M:MS_Data G K)(k:ℕ)(P:IntervalFamily I)(X:T ( Glade G I )):=∃ p:Details B I k, Valid P p ∧∃ Y:T ( Glade G I ), Response Y M η (-1) ∧ Reps Y 0 P ∧ X=Physical η M p+nav M η Y
namespace Total
lemma exists0 : Total η M k P (0:T ( Glade G I )):= ⟨0,(fun i n=> Profit.z),0, Response.zero,Reps_zero,(by rw [H_zero,map_zero,zero_add])⟩
lemma plus (hx:Total η M k P X)(hv:Total η M k P Y): Total η M k P (X+Y):= by obtain ⟨p,hp,E,hE,HE,rfl⟩:=hx; obtain ⟨v,hv,F,hF,HF,rfl⟩:=hv; exact ⟨ p+v,V_plus hp hv,E+F,hE.add hF, Reps_add HE HF,( by rw [map_add,H_add]; abel) ⟩
lemma total (s:Finset J){F:J→ T ( Glade G I )}(h:∀ i∈s,Total η M k P (F i)): Total η M k P (∑ i∈s,F i):= by classical induction s using Finset.induction_on with| empty=> rw [Finset.sum_empty]; exact exists0 | insert i s hi ih=> rw [ Finset.sum_insert hi ]; exact plus ( h i (by simp) ) (ih fun j hj=> h j (mem_insert_of_mem hj))
lemma usesC (h: Total η M k P X): Certified X M η 0:= by obtain ⟨p,hp,Y,h,hh,rfl⟩:=h; apply C_add PH_C; exact h.ward
lemma usesV (h: Total η M k P X)(hp: allowance P η): Reps X 0 P:= by obtain ⟨p,hs,Y,h,hh,rfl⟩:=h; exact Reps_add (PH_V hp hs) (Reps_desc ( RVA hp h hh ) (by norm_num))
lemma q_form (h:Response Y M η (-1))(he:Reps Y 0 P): Total η M k P (nav M η Y):= ⟨0,fun _ _=>Profit.z,Y,h,he,by rw [H_zero,zero_add]⟩
lemma unique_form (i:Counter B k)(hc:Profit P.dawn a): Total η M k P ( hold0 n (seat a (roadZ η M i)) ):= by
    refine ⟨ Pi.single i (Pi.single n a),?_,0,Response.zero,Reps_zero,(by rw [singled,solo_h,map_zero,add_zero])⟩; rintro j m; by_cases hp:j=i; swap; · rw [ Pi.single_eq_of_ne hp ]; exact Profit.z
    subst j; rw [Pi.single_eq_same]; by_cases he:m=n; · subst m; rwa [Pi.single_eq_same]
    rw [Pi.single_eq_of_ne he]; exact Profit.z
-- economic scalars preserve flags
lemma starr (h:Total η M k P X)(hv:Profit P.dawn a): Total η M k P (seat a X):= by
    -- simple scalar multiplication corresponds to p*Φ. proof by auxiliary lemma
    obtain ⟨s,hS,Y,hs,hH,rfl⟩:=h; rw [ distributeR,seat,seat,← res_cash ]; apply Total.plus ?_ ( q_form ( hs.scale a ) ( Reps_profit hv hH )); let f: Details B I k:= fun i m=> a * s i m; refine ⟨ f,(fun i m=> hv.cash (hS i m)), 0,Response.zero,Reps_zero,(by rw [ map_zero,add_zero ]; exact holdCash a) ⟩
where
 holdCash (a:I→ℝ) {p: Details B I k}: seat a ( Physical η M p )= Physical η M (h:=k) ( fun i m=> a*p i m ):= by
    funext n k t l; unfold seat pay Physical entrance; simp_rw [ Finset.sum_apply, Pi.smul_apply ]; simp only [smul_eq_mul, Finset.sum_apply]; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j hj=>?_ ; obtain hv:j≤n:= Nat.le_of_lt_succ (Finset.mem_range.mp hj); simp only [hx_holder hv,seat,pay,Pi.smul_apply,Pi.mul_apply,Complex.ofReal_mul,smul_eq_mul]; ring
end Total
end YM.FVA2.O.Hue
