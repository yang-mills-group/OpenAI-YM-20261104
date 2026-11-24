import YM.OPE.Compatible.Maestro.Buoy
/-!
# End-to-end cutter geometry cost. leaf prices retained if comparable.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open MeasureTheory
open scoped Topology Classical
open YM.OPE.Allot Series
variable {G:Gauge}{C:Family G}{I V:Type}{φ:Filter I}{T z : I→ℝ}
variable [PartialOrder V][Fintype V][OrderBot V](D:Origin V){η : ℝ} {s:I→V→ℝ}{Q:Finset V}
variable (hG:G.Simple)(A:Allot C)(h: Glowing D Q φ T s η)
set_option quotPrecheck false
variable (b d:ℕ)
local notation "t"=>fun i=>schedule C b η (s i)
local notation "X"=>fun i=>scopeTick D C b d η (T i) (s i)
local notation "K!"=>fun i=>aperture D C b d η (T i) (s i)
local notation "NJ"=>fun i=> t i ⊥-1
local notation "r"=> C.S.a
local notation "R"=> fun i=> s i ⊥
local notation "χ"=> brim D Q
include hG A h
lemma prev_info : (∀ᶠ i in φ,NJ i+1=t i ⊥) ∧ Tendsto NJ φ atTop ∧ Round φ T (fun i=>β C (NJ i)) ∧ Round φ T (fun i=> r (NJ i)/R i):=by
   let j i:= t i ⊥; have hf:= lives D hG A h b h.crowned.base; have hj : ∀ᶠ i in φ,(NJ i)+1=t i ⊥:= (hf.eventually_gt_atTop 0).mono fun i hi=> Nat.sub_add_cancel hi
   have hb:Round φ T (fun i=>β C (NJ i)):= Round.if_inv (Eventually.of_forall fun _=> β_pos ..) ((thermal D hG A h b h.crowned.base).up.pointwise (hj.mono fun i hi=> (β_increases hG).monotone ((Nat.le_succ _).trans hi.le)) (Eventually.of_forall fun _=> (β_pos ..).le)) h.ray (Eventually.of_forall fun _=> (β_one ..).le)
   have hn:Tendsto NJ φ atTop:= tendsto_atTop.mpr fun n=>by filter_upwards [hf.eventually_gt_atTop n] with i hi; change n< j i at hi; change n ≤ j i-1; omega
   refine ⟨hj,hn,hb,((stands D hG A h b h.crowned.base).mul (block_score A h.ray hb)).adjust ?_⟩
   filter_upwards [hj] with i hi; change C.S.a (j i)/_ *_= _; rw [show j i= _ from hi.symm]; rw [C.S.a_step]; have hb:0< extent C (NJ i):=zero_lt_two.trans_le (extent_two ..); change (r _/extent C _)/_*extent C _=_; field_simp

def volume (D:Origin V)(Q:Finset V)(u:brim D Q →ℕ)(s:V→ℝ) := ∏ i:brim D Q,s (par D i.val)^(u i)
variable (u:brim D Q→ ℕ)(c:I→brim D Q→ℝ)
local notation "π"=> fun i=> CutOrder.grove D C Q (t i) (X i) (z i) (c i)
local notation "p!"=> fun i=>volume D Q u (s i)
variable (hz : Round φ T z)
lemma grove_pay (hz:Round φ T z)(hp : ∀ x:χ, Round φ T (fun i=>c i x / s i (par D x.val)^(u x))) : Round φ T (fun i=>π i/p! i):=by
    let w(i:I)(x:χ):= Run.Below C.path (c i x) (X i x.val+1) (finishAt D (t i) x.val)
    let f(i:I)(x:χ):= w i x / (s i (par D x.val))^(u x)
    have he(x:χ): Round φ T (fun i=> f i x):=by
       let y0 i:=s i (par D x.val); have hx:=parent_middle D h (x:=x.val) (Finset.mem_union_right _ x.2); have hb:= stands D hG A h b hx; obtain ⟨_,hs⟩:= arrive D hG A h b d (v:=x.val) (Finset.mem_union_right _ x.2)
       refine ((hp x).mul ((hs.div hb).power 4 h.ray)).adjust ?_; filter_upwards [(h.fade _ hx).eventually self_mem_nhdsWithin] with i hi; let j:= finishAt D (t i) x.val; let J:=aperture D C b d η (T i) (s i) x.val; let Y:=y0 i; have hp:0<Y:=hi
       change c i x / Y^_ * (C.S.a J/Y/(C.S.a j / Y))^4 = (c i x *(C.S.a J/C.S.a j)^4)/Y^_; field_simp
    refine ((hz.power (Q.card*(places V+places V)) h.ray).mul (Round.multiple Finset.univ (fun x:χ=> fun i=> f i x) h.ray (fun i _=>he i))).adjust ?_
    filter_upwards with i; unfold f; change z i^_*(∏ x, _)= z i^_*(∏ x,w i x)/volume D Q u (s i); rw [Finset.prod_div_distrib,mul_div_assoc]; rfl
variable (hp : ∀ x:brim D Q, Round φ T (fun i=>c i x / s i (par D x.val)^(u x)))
lemma all_pays (m K:ℕ)(hk:C.ref m ≤ K) (hz:Round φ T z)
   (hp : ∀ x:χ, Round φ T (fun i=>c i x / s i (par D x.val)^(u x))):
    Round φ T (fun i=> owed C (π i) m (NJ i)* p! i / (R i)^m) ∧ Round φ T (fun i=> rebate C (π i) m K (NJ i)*(R i)^m / p! i) :=by
    have hG':=grove_pay D hG A h b d u c hz hp
    have he: ∀ᶠ i in φ, 0 < volume D Q u (s i):=by
       filter_upwards [eventually_all.mpr (fun i:χ=>(h.fade _ ((on_brim ..).mp i.2|>.2.2)).eventually self_mem_nhdsWithin)] with i hi; exact Finset.prod_pos fun j _=> pow_pos (hi j) _
    have h':∀ᶠ i in φ,0 < π i:= by filter_upwards [hG'.pos,he] with i hi hp using pos_of_mul_pos_left (b:=(p! i)⁻¹) (by rwa [← div_eq_mul_inv]) (inv_nonneg.mpr hp.le)
    obtain ⟨_,hj,hq,hv⟩:= prev_info D hG A h b; constructor
    · refine (((owed_cost A hG h.ray hj hq h' m).mul (hv.power m h.ray)).div hG').adjust ?_; filter_upwards [he,h'] with i he hp; change π i>0 at hp; change owed C (π i) m (NJ i)*π i / (r (NJ i))^m* (_/_)^m/(_ / _) =_; rw [div_pow]; have hv:=C.S.a_pos (NJ i); field_simp
    refine (((repol A hG h.ray hj hq h' hk).div (hv.power m h.ray)).mul hG').adjust ?_; filter_upwards [he,h',(h.fade _ h.crowned.base).eventually self_mem_nhdsWithin] with i he hp ht; have hu:0<R i:=ht; change rebate C (π i) m K (NJ i) * (r (NJ i))^m / (π i)/(_/_)^m* (_/ (p! i))=_; rw [div_pow]; have hv:= C.S.a_pos (NJ i); field_simp
end YM.OPE.Arboreal
