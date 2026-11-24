import YM.AllOrder.Local.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Catch
open Function Filter Finset Topology
open scoped Topology Classical BigOperators
structure Clock (X:Type*) where
 rail : Filter X
 cost : X→ℝ
 drive : Tendsto cost rail atTop
namespace Clock
variable {X Y α:Type*}{V:X→Type*} (S:Clock X){U:Clock Y} {f g:X→ℝ}{a b c:ℝ}
local notation "Z"=>S.rail
local notation "h"=>S.cost
def Meter (f:X→ℝ) (a:ℝ): Prop:= ∀ b>a,∀ᶠ i in Z, |f i| ≤ (S.cost i)^b
local notation "H"=> S.Meter
lemma pos : ∀ᶠ i in Z, 1 ≤ S.cost i:= S.drive.eventually_ge_atTop _
lemma positive : ∀ᶠ i in Z, 0<S.cost i:= (pos S).mono fun i hi=> zero_lt_one.trans_le hi
lemma slack (h0:a<b) (c:ℝ): ∀ᶠ i in S.rail, c*(S.cost i)^a< (S.cost i)^b:= by
 filter_upwards [((tendsto_rpow_atTop (sub_pos.mpr h0)).comp S.drive).eventually_gt_atTop c,S.positive] with i hi hI
 change c<(S.cost i)^(b-a) at hi; rwa [Real.rpow_sub hI, lt_div_iff₀ (Real.rpow_pos_of_pos hI _)] at hi
structure Fare (f:Y→X) : Prop where
 tends : Tendsto f U.rail S.rail
 same : U.cost =ᶠ[U.rail] (S.cost∘ f)
namespace Meter
variable {S}
lemma weak (hs:H f a)(hp:a≤b): H f b:=fun i hv=> hs i (hp.trans_lt hv)
lemma smaller (hs:H f a) (he: ∀ᶠ i in S.rail, |g i|≤ |f i|) : H g a:=fun b hb=> (he.and (hs b hb)).mono fun i hi=> hi.1.trans hi.2
lemma eq_mem (hs:H f a)(he:f=ᶠ[Z] g): H g a:= smaller hs (he.mono fun _ hi=> le_of_eq (congr_arg abs hi.symm))
lemma pay (hs:∀ᶠ i in Z, |f i| ≤ (S.cost i)^a): H f a:= by intro b hb; filter_upwards [hs,S.pos] with i hI hx; exact hI.trans (Real.rpow_le_rpow_of_exponent_le hx hb.le)
lemma pale (S:Clock X)(a:ℝ): S.Meter (fun i=>(S.cost i)^a) a:=pay (S.positive.mono fun i hi=>(abs_of_pos (Real.rpow_pos_of_pos hi a)).le)
lemma pays (hs:H f a)(k:Y→X)(hp:S.Fare (U:=U) k): U.Meter (f∘ k) a:= by
 intro b hb; filter_upwards [hp.tends.eventually (hs b hb),hp.same] with i hi hv; rw [hv]; exact hi
lemma nil (S:Clock X)(a:ℝ): S.Meter (fun _=>0) a:= pay (by filter_upwards [positive S] with x hX; change |(0:ℝ)|≤_; simp only [abs_zero]; positivity)
lemma const (S:Clock X)(a:ℝ): S.Meter (fun _=>a) 0:=fun b hb=> ((tendsto_rpow_atTop hb).comp S.drive).eventually_ge_atTop |a|
lemma neg (hs:H f a):H (fun i=> -f i) a:= smaller hs (Eventually.of_forall fun i=>(abs_neg _).le)
lemma ab (hs:H f a):H (fun i=> |f i|) a:= smaller hs (Eventually.of_forall fun i=>(abs_abs _).le)
lemma mul (hs:H f a)(ht:H g b): H (fun i=> f i*g i) (a+b):= by
 intro t he; let x:=(t-(a+b))/2; have hx:0<x:=half_pos (sub_pos.mpr he); have ha:a<a+x:= lt_add_of_pos_right _ hx; have hb:b<b+x:=lt_add_of_pos_right _ hx; filter_upwards [hs _ ha,ht _ hb,S.positive] with i hv hI hh; rw [show t=(a+x)+(b+x) by unfold x; ring,Real.rpow_add hh,abs_mul]; exact mul_le_mul hv hI (abs_nonneg _) (Real.rpow_pos_of_pos hh _).le
lemma add (hs:H f a)(ht:H g a): H (fun i=> f i+g i) a:= by
 intro t he; obtain ⟨x,ha,hb⟩:= exists_between he; filter_upwards [hs x ha,ht x ha, S.slack hb 2] with i hp hv ht; exact (abs_add_le ..).trans ((add_le_add hp hv).trans (by rw [← two_mul]; exact ht.le))
lemma sub (hs:H f a)(ht:H g a):H (fun i=>f i-g i) a:=by simpa only [sub_eq_add_neg] using hs.add ht.neg
lemma sum {v:α→X→ℝ} (u:Finset α)(ht:∀ i∈u,H (v i) a):H (fun i=> ∑ x∈u,v x i) a:= by
 induction u using Finset.induction_on with
 | empty=> simpa using nil S a
 | insert i s hs ih=> simpa only [sum_insert hs] using (ht i (mem_insert_self ..)).add (ih fun j hj=>ht j (mem_insert_of_mem hj))
lemma pow (hs:H f a)(n:ℕ):H (fun i=> f i^n) (a*n):= by
 induction n with | zero=> simpa using const S 1 | succ n ih=>simpa [pow_succ,mul_add] using ih.mul hs
lemma lscale (hs:H f a)(c:ℝ):H (fun i=> c*f i) a:= ((const S c).mul hs).weak (by simp)
lemma rscale (hs:H f a)(c:ℝ):H (fun i=> f i*c) a:= (hs.mul (const S c)).weak (by simp)
lemma stricter (hs:H f a)(he:a<b):∀ᶠ i in Z, |f i| < S.cost i ^ b:= by obtain ⟨p,hp,hb⟩:=exists_between he; filter_upwards [hs p hp,S.slack hb 1] with i hq hI; rw [one_mul] at hI; exact hq.trans_lt hI
lemma low (hs:H f a)(he:a<0)(hp:0<b) : ∀ᶠ i in Z, |f i| < b:= by
 obtain ⟨p,ht,hb⟩:=exists_between he
 let m := ((tendsto_rpow_neg_atTop (neg_pos.mpr hb)).comp S.drive).eventually (gt_mem_nhds hp); filter_upwards [m,hs p ht] with i hi hv; change S.cost i ^ (-(-p))<b at hi; rw [neg_neg] at hi; exact hv.trans_lt hi
lemma down (hs:H f a)(he:a<0):Tendsto f Z (𝓝 0):= Metric.tendsto_nhds.mpr fun i hi=> by simpa only [dist_zero_right,Real.norm_eq_abs] using hs.low he hi
lemma unitPay (hs:H f a)(he:a≤ 0)(hg:H g b): H (fun i=>f i*g i) b:= (hs.mul hg).weak (by linarith)
lemma burden {Y:X→Type*}[∀ i,SeminormedAddCommGroup (Y i)]{f g:∀ i, Y i}(hs:H (fun i=> ‖f i‖) a)(hv: H (fun i=> ‖g i‖) a):H (fun i=> ‖f i+g i‖) a:= (hs.add hv).smaller (Eventually.of_forall fun i=> by rw [abs_of_nonneg (show 0 ≤ ‖f i+g i‖ from norm_nonneg _)]; exact (norm_add_le ..).trans (le_abs_self _))
end Meter
abbrev liftZ (S:Clock X)(f:Y→X):Clock Y:=⟨ Filter.comap f S.rail,S.cost∘ f,S.drive.comp tendsto_comap⟩
lemma liftF (f:Y→X): S.Fare (U:=S.liftZ f) f := ⟨tendsto_comap,EventuallyEq.refl ..⟩
abbrev stage (V:X→Type*) :Clock (Sigma V):= S.liftZ Sigma.fst
lemma pays (W:X→Type*)(hs:H f a): (S.stage W).Meter (f ∘ Sigma.fst) a:= hs.pays _ (S.liftF _)
lemma everybody (p:Sigma V→ Prop) : (∀ᶠ i in (stage S V).rail,p i)↔∀ᶠ i in S.rail,∀ b:V i,p ⟨i,b⟩:= by
 change Filter.Eventually _ (Filter.comap _ S.rail) ↔_; rw [eventually_comap]; apply eventually_congr; apply Eventually.of_forall; intro i; exact ⟨fun hx k=>hx ⟨i,k⟩ rfl,by rintro hx ⟨j,k⟩ (he:j=i); subst i; exact hx k⟩
abbrev book (s:∀ i,Set (V i)):= S.stage fun i=>{x:V i//x∈s i}
lemma bookF (s:∀ i,Set (V i)) : S.Fare (U:=S.book s) Sigma.fst:= S.liftF _
lemma booked (s:∀ i,Set (V i)) (p:(i:X)→V i→ Prop): (∀ᶠ i in (S.book s).rail,p i.1 i.2)↔∀ᶠ i in S.rail,∀ b∈s i,p i b:= by
 rw [everybody S]; simp only [Subtype.forall]
end Clock
end YM.AllOrder.Catch
