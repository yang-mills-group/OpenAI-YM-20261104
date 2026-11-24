import YM.GapsContact.Power.Mars
import YM.Frontier6.Exact.Palette

/-!
# Fitting the ledger to the physical complement

At one scale `r`, closest complement doesn't mean the exact contact prescription. Compare
uniformly via persistence and higher sector growth under decreasing scale. Thus the fixed scheme
can really use these power estimates on ALL relative ratios even with projections at length s.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GapsContact.Power
open Function Filter Set MeasureTheory Metric Extraction Climb Spec Ascent
open Trace Trace.Terrace Trace.Pilot MergeProof.East Next.UVStress Trace.Over Frontier6
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{C: Family G} {d e n:ℕ}{r s x a ε c R p:ℝ}{𝓛: Ultrafilter (ℕ × ℕ)} {f:Extraction.Order} {S:Table C.book}
variable (F:Final C f S) {H:(Climb.Bel C.book).Hierarchy}{Z:Trace.Terrace.Arch C}
variable (hG:G.Simple) (Y:Bliss F 𝓛 Z H)
set_option quotPrecheck false
local notation "I" => F.phase.transport.injection
local notation "T" => F.sector.derivatives
local notation "Hh" => F.room.kernel
local notation "O" => F.phase.transport.rights

namespace ScaleFirm

abbrev Hi (x:S.Field d): Prop:= x ∈ Grade F d
lemma solid (x:S.Field (d+1)) (he:Hi F x)(hx:x≠0) : x∉LinearMap.range (Up T d):=by
    intro hp; obtain ⟨w,hw⟩:=hp; subst x; exact hx (((weight_space ..).mp he).symm.trans (weight_away F w (Nat.lt_succ_self d)))
lemma cap_sip (he:Good Hh d s)(hs:0<s)(x:S.Field (d+1)) : sip Hh T d s (weight F (d+1) x)= sip Hh T d s x:=by
   symm; apply sip_leaves Hh T I O hs he; rw [weight_up,sub_sub_cancel]; exact ⟨_,rfl⟩

variable (P':ScaleFirm F R r ε d) (he:0<ε)(he':ε<1/2)
local notation "s0" => R*r⁻¹
include P'
set_option maxHeartbeats 750000 in
lemma starts :∃ B:ℝ,1≤B ∧ ∀ x:S.Field (d+1), Hi F x → ∀ t∈Icc (R*r⁻¹) R, chip Hh (d+1) t x ≤ B*sip Hh T d t x:=by
   have hr:R ∈Ioc 0 R:=⟨P'.length,le_refl _⟩; have hs:= incline hr P'.mover|>.1
   let U:= projectBelow F (Nat.le_succ d); let V:= (U.restrictScalars ℝ)
   let p(x:S.Field (d+1)):= sip Hh T d R x+‖U x‖
   letI : FiniteDimensional ℝ (S.Field (d+1)):= Module.Finite.trans ℂ _
   have he (u:S.Field (d+1))(hu:u≠0):0<p u:=by
      unfold p; by_cases hf:U u=0
      · rw[hf,norm_zero,add_zero]; apply sip_lt Hh T (P'.valid _ hr|>.2) u; rintro ⟨v,hv⟩; subst u; exact hu ((show v=0 from ((projects_fix F (Nat.le_succ d) v).symm.trans hf)).symm ▸ map_zero _)
      exact add_pos_of_nonneg_of_pos (sip_nn ..) (norm_pos_iff.mpr hf)
   obtain ⟨B,hB,hX⟩:= metric_paid (chip F.room.kernel (d+1) (s0)) p (chip_cont Hh (d+1) _ hs.1) ((sip_cont Hh T d P'.length).add (V.continuous.norm)) (fun c x=> chip_real Hh _ _ c) (fun c x=> by change sip Hh T d R (c • x)+‖V (c • x)‖=_;rw [sip_smul,map_smul,norm_smul]; unfold p; rw[mul_add]; rfl) he
   · refine ⟨B,hB,fun x hx t ht=> ?_⟩; have h := sip_go Hh T I O P'.length (P'.valid _ hr|>.1) (hs.1.trans_le ht.1) ht.2 x; specialize hX x
     unfold p at hX; rw [show U x=0 from ((weight_space ..).mp hx) ▸ projects_pure F (Nat.lt_succ_self d) x,norm_zero,add_zero] at hX
     exact ((power_signal Hh _ hs.1 ht.1).trans hX).trans (mul_le_mul_of_nonneg_left h (zero_le_one.trans hB))

include he'
lemma honour : ∃ B:ℝ,1≤ B∧ ∀ s∈Ioc 0 R,∀ u:S.Field (d+1), Hi F u → chip Hh (d+1) s u≤ B*sip Hh T d s u:=by
   let M:= r^((d:ℝ)+1+ε); let l:=r^((d:ℝ)+1-ε); let m:=r^((d:ℝ)+ε)
   obtain ⟨b,hb,hG⟩:= starts F P'; have hℓ:m<l:= Real.rpow_lt_rpow_of_exponent_lt P'.mover (by linarith only [he']); have hr:=P'.mover; have hr':0<r:=zero_lt_one.trans hr; have hm:0 ≤ m:= Real.rpow_nonneg hr'.le _
   let B:=max b (M/(l-m));have hB:1 ≤ B:= hb.trans (le_max_left ..)
   have hP:M+m*B≤B*l:=by have he := (div_le_iff₀ (sub_pos.mpr hℓ)).1 (le_max_right b (M/(l-m))); change M≤B*_ at he; linarith only [he]
   refine ⟨B,hB,persistence hr (fun s=> ∀ u:S.Field (d+1), Hi F u → chip Hh (d+1) s u≤ B*sip Hh T d s u) P'.length (fun t ht u hu=> ?_) (fun t ht P u hu=>?_)⟩
   · exact (hG u hu t ht).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (sip_nn ..))
   let x:=t*r⁻¹; have hx:x∈Ioc 0 R:=(incline ht P'.mover).2
   let v:= ridge Hh T d t u; let w :=edge Hh T d t u; let U:= Up T d w; have hZq : u=v+U:=by unfold v; rw[ridged,sub_add_cancel]
   have ha:= edge_le Hh T I O ht.1 (P'.valid _ ht|>.1) u
   have hh: chip Hh (d+1) x u ≤ (M+m*B)*sip Hh T d t u:=by
       have hZ: chip Hh (d+1) x v ≤ M*sip Hh T d t u:= by simpa only[Nat.cast_add,Nat.cast_one] using! (P'.arrival _ ht|>.1 v)
       have hf: chip Hh (d+1) x U ≤ m*(B*sip Hh T d t u):= by
         rw[show _ = chip Hh d x w from (chip_inherit Hh T I O (Nat.le_succ d) hx.1 w).symm]
         exact (P'.paid _ ht w).trans (mul_le_mul_of_nonneg_left (ha.trans (P _ hu)) hm)
       nth_rw 1 [hZq]; exact (chip_add Hh hx.1 ..).trans ((add_le_add hZ hf).trans_eq (by ring))
   exact hh.trans ((mul_le_mul_of_nonneg_right hP (sip_nn ..)).trans (by rw[mul_assoc]; exact mul_le_mul_of_nonneg_left (P'.arrival _ ht|>.2 u|>.1) (zero_le_one.trans hB)))

lemma uniform_top : ∃ B:ℝ,1 ≤ B ∧ ∀ s∈ Ioc 0 R,∀ u:S.Field (d+1),
      chip Hh (d+1) s (weight F (d+1) u) ≤ B*chip Hh (d+1) s u ∧
        chip Hh d s (projectBelow F (Nat.le_succ d) u) ≤ B*chip Hh (d+1) s u:= by
    obtain ⟨B,hB,hU⟩:= honour F P' he'; refine ⟨1+B,(by linarith),fun s hs u=> ?_⟩
    let v:= weight F (d+1) u; have hg:=P'.valid s hs|>.1
    have he':chip Hh (d+1) s v≤B*chip Hh (d+1) s u:=(hU s hs v ⟨u,rfl⟩).trans (mul_le_mul_of_nonneg_left ((cap_sip F hg hs.1 u).trans_le (sip_le Hh T I O hs.1 hg u)) (zero_le_one.trans hB))
    rw [add_mul,one_mul]; constructor
    · exact he'.trans (le_add_of_nonneg_left (chip_nn ..))
    rw[chip_inherit Hh T I O (Nat.le_succ d) hs.1]; let p:=projectBelow F (Nat.le_succ d) u; show chip Hh (d+1) s (Up T d p)≤ _; have hf: Up T d p=u + (-v):=by unfold v; rw[← sub_eq_add_neg,weight_up,sub_sub_cancel]; rfl
    rw [hf]; exact (chip_add Hh hs.1 ..).trans (add_le_add (le_refl _) ((chip_neg Hh ..).trans_le he'))

lemma sales : ∃ B:ℝ,1 ≤ B ∧ ∀ s∈ Ioc 0 R, ∀ t∈Ioc 0 s, ∀ u:S.Field (d+1), Hi F u→
     chip Hh (d+1) s u ≤ B*(t/s)^((d:ℝ)+1-ε)*chip Hh (d+1) t u:=by
   obtain ⟨B,hB,hU⟩:= honour F P' he'; let m:ℝ:= (d:ℝ)+1-ε; have he:0 ≤ m:=by unfold m; linarith only [he',Nat.cast_nonneg (α:=ℝ) d]
   have hrm : 1≤ r^m:=Real.one_le_rpow P'.mover.le he
   refine ⟨B*r^m,one_le_mul_of_one_le_of_one_le hB hrm,fun s hs t ht u hp=> ?_⟩
   have hx:t∈Ioc 0 R:=⟨ht.1,ht.2.trans hs.2⟩
   have hh:= ((discounted F P' hs ht (sub_nonneg.mp he) u).trans (mul_le_mul_of_nonneg_left (sip_le Hh T I O ht.1 (P'.valid t hx|>.1) u) (zero_le_one.trans hrm)))
   refine (hU s hs u hp).trans ((mul_le_mul_of_nonneg_left ((le_inv_mul_iff₀ (Real.rpow_pos_of_pos (div_pos hs.1 ht.1) m)).mpr hh) (zero_le_one.trans hB)).trans_eq ?_)
   rw [← Real.inv_rpow (div_pos hs.1 ht.1|>.le),inv_div]; ring
end ScaleFirm

-- Market on actual witness, explicit cupboard. Use projections ∀ near horizon eventually via `transit 
structure Market (d:ℕ)(ε R B:ℝ) : Prop where
   road : 0<R
   budget : 1≤B
   uniform_top : ∀ s∈Ioc 0 R, ∀ x:S.Field d,cost F d s (weight F d x) ≤ B*cost F d s x
   tier : ∀ e:ℕ, ∀ he:e≤d, ∀ s∈Ioc 0 R,∀ x:S.Field d,cost F e s (projectBelow F he x) ≤ B*cost F d s x
   horizon : ∀ s∈Ioc 0 R,Good Hh d s
   left {s t:ℝ}(hs:s∈Ioc 0 R)(ht:t∈Ioc 0 s)(u:S.Field d): cost F d t u ≤ B*(s/t)^((d:ℝ)+ε)*cost F d s u
   sale {s t:ℝ}(hs:s∈Ioc 0 R)(ht:t∈Ioc 0 s)(u:S.Field d)(hp:u∈ Grade F d): cost F d s u ≤ B*(t/s)^((d:ℝ)-ε)*cost F d t u

lemma Market.refresh {A A':ℝ} (h:Market F d ε R A)(hc:0<x)(hy:x ≤ R)(hA:A≤ A')(hε:ε≤r): Market F d r x A' where
   road:= hc
   budget:= h.budget.trans hA
   uniform_top s hs v:= (h.uniform_top _ ⟨hs.1,hs.2.trans hy⟩ v).trans (mul_le_mul_of_nonneg_right hA (Ascent.cost_pos ..))
   tier e he s hs v:= (h.tier e he s ⟨hs.1,hs.2.trans hy⟩ v).trans (mul_le_mul_of_nonneg_right hA (Ascent.cost_pos ..))
   horizon s hs:= h.horizon _ ⟨hs.1,hs.2.trans hy⟩
   left hs ht u:= by
      apply (h.left ⟨hs.1,hs.2.trans hy⟩ ht u).trans; refine mul_le_mul_of_nonneg_right ?_ (Ascent.cost_pos ..)
      exact mul_le_mul hA (Real.rpow_le_rpow_of_exponent_le ((one_le_div ht.1).2 ht.2) (add_le_add_right hε _)) (Real.rpow_nonneg (div_nonneg hs.1.le ht.1.le) _) (zero_le_one.trans (h.budget.trans hA))
   sale hs ht u hp:= by
      apply (h.sale ⟨hs.1,hs.2.trans hy⟩ ht u hp).trans; refine mul_le_mul_of_nonneg_right ?_ (Ascent.cost_pos ..)
      exact mul_le_mul hA (Real.rpow_le_rpow_of_exponent_ge (div_pos ht.1 hs.1) ((div_le_one hs.1).2 ht.2) (sub_le_sub_left hε _)) (Real.rpow_nonneg (div_nonneg ht.1.le hs.1.le) _) (zero_le_one.trans (h.budget.trans hA))

include hG Y
lemma given_market (d:ℕ) (he:0<ε)(he':ε<1/2):∃ R B:ℝ, Market F d ε R B:=by
   induction d with
   | zero=>
       obtain ⟨R,t,h⟩:= mars F hG Y 0 ε he
       have hB:1 ≤ t^ε:= Real.one_le_rpow h.mover.le he.le
       let B:= t^ε; let Z(u:S.Field 0)(t:ℝ): cost F 0 t u ≤ B*cost F 0 t u:= le_mul_of_one_le_left (Ascent.cost_pos ..) hB
       refine ⟨R,B,⟨h.length,hB,fun r _ u=> Z u r,?_,fun r hr=> (h.valid _ hr).1, fun {s t'} hs ht u=> ?_, fun {s t'} hs ht u hp=>?_⟩⟩
       · intro e he s _ u; obtain rfl:= Nat.eq_zero_of_le_zero he; rw [projects_self]; exact Z u s
       · simpa only [Nat.cast_zero,zero_add] using! (ScaleFirm.pay F h he s hs t' ht u)
       apply le_trans (b:=cost F 0 t' u) (power_signal Hh (d:=0) u ht.1 ht.2); refine le_mul_of_one_le_left (Ascent.cost_pos ..) ?_
       have hv := Real.rpow_le_rpow_of_exponent_ge (div_pos ht.1 hs.1) ((div_le_one hs.1).mpr ht.2) (show (↑(0:ℕ):ℝ)- ε ≤ 0 by norm_num; positivity)
       rw [Real.rpow_zero] at hv; exact one_le_mul_of_one_le_of_one_le hB hv
   | succ d ih=>
       obtain ⟨r,b,hM⟩:= ih; obtain ⟨R,t,h⟩:= mars F hG Y d ε he; obtain ⟨R',t',h'⟩:= mars F hG Y (d+1) ε he; obtain ⟨B,hB,hu⟩:= ScaleFirm.uniform_top F h he'; obtain ⟨C',hc,hT⟩:= ScaleFirm.sales F h he'
       let l:ℝ:=t'^((↑(d+1):ℝ)+ε);have hl:1 ≤ l:= Real.one_le_rpow h'.mover.le (by positivity)
       obtain ⟨A, ha, hb,hL,hC⟩:= ((eventually_ge_atTop 1).and ((eventually_ge_atTop (b*B)).and ((eventually_ge_atTop l).and (eventually_ge_atTop C')))).exists
       let v:= min (min R R') r; have hv:0<v:= lt_min (lt_min h.length h'.length) hM.road
       have Hx:v≤ R:= (min_le_left ..).trans (min_le_left ..); have Hy:v≤ R':= (min_le_left ..).trans (min_le_right ..); have Hz:v≤ r:= min_le_right ..
       have hE:B ≤ A:= (le_mul_of_one_le_left (zero_le_one.trans hB) hM.budget).trans hb
       refine ⟨v,A,⟨hv,ha,fun s hs u=> ((hu _ ⟨hs.1,hs.2.trans Hx⟩ u).1.trans (mul_le_mul_of_nonneg_right hE (chip_nn ..))),?_,fun s hs=> (h.valid _ ⟨hs.1,hs.2.trans Hx⟩).2,fun {s t} hs ht u=> ?_,fun {s t} hs ht u hp=>?_⟩⟩
       · intro e he s hs u
         rcases Nat.eq_or_lt_of_le he with ht|ht
         · subst e; rw [projects_self]; exact le_mul_of_one_le_left (Ascent.cost_pos ..) ha
         have hh:e≤d:=by omega
         rw[← projects_comp F hh (Nat.le_succ d)]
         apply (hM.tier e hh s ⟨hs.1,hs.2.trans Hz⟩ _).trans; show _ ≤ A * chip Hh _ _ _
         exact (mul_le_mul_of_nonneg_left (hu _ ⟨hs.1,hs.2.trans Hx⟩ u).2 (zero_le_one.trans hM.budget)).trans ((mul_assoc ..).symm.trans_le (mul_le_mul_of_nonneg_right hb (chip_nn ..)))
       · exact (ScaleFirm.pay F h' he s ⟨hs.1,hs.2.trans Hy⟩ t ht u).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (div_pos hs.1 ht.1|>.le) _)) (chip_nn ..))
       rw [Nat.cast_add,Nat.cast_one]; exact (hT s ⟨hs.1,hs.2.trans Hx⟩ t ht u hp).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (div_pos ht.1 hs.1|>.le) _)) (chip_nn ..))

lemma marketplace0 (d:ℕ)(ε:ℝ)(he:0<ε):∃ R B, Market F d ε R B:=by
   let e:= min ε (1/4)
   obtain ⟨R,B,h⟩:=given_market F hG Y d (show 0<e from lt_min he (by norm_num)) (lt_of_le_of_lt (min_le_right ..) (by norm_num)); exact ⟨R,B,h.refresh F h.road le_rfl le_rfl (min_le_left ..)⟩

lemma marketplace (d:ℕ)(ε:ℝ)(he:0<ε): ∃ R B, ∀ e≤d, Market F e ε R B:=by
   induction d with
   | zero=>simpa using marketplace0 F hG Y 0 ε he
   | succ d ih=>
       obtain ⟨R,B,h⟩:= ih
       obtain ⟨r,b,h'⟩:= marketplace0 F hG Y (d+1) ε he
       have he:= lt_min (h d le_rfl).road h'.road
       refine ⟨min R r,max B b,fun e he' => ?_⟩
       rcases Nat.eq_or_lt_of_le he' with hu|hu; · subst e; exact h'.refresh F he (min_le_right ..) (le_max_right ..) le_rfl
       exact (h e (by omega)).refresh F he (min_le_left ..) (le_max_left ..) le_rfl
end YM.GapsContact.Power
