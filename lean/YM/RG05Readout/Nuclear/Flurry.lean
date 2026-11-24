import YM.RG05Readout.Nuclear.Jolt
/-!
# Quasi-cardinal approximants with telescoping cost
Σ derivative degrees `L`. Unit patches at scales r,r/2 purchased linearly
in ∥profiles∥ with THIS valuation. `flutes` budget outside any inspected
 box.E.Support.Carriers.Intermediate terms already proper; next tier
 invoiced using only marginal and not entering every-form inspections here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Nuclear
open Tensor Analysis Function Filter Set MeasureTheory Native Pulse Lattice
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {n m d k:ℕ}{E:Type}[TopologicalSpace E]
variable {V J:Type}[Fintype V][DecidableEq V]
local notation "U"=>Cloud V
local notation "W"=> Wave V
set_option quotPrecheck false
section piece
variable (s:V→ℕ)(Ω:Set E)(C:Allow V)(F:E→Wave V)(C':ℝ)(x₀:ℝ)
local notation "D"=> ∑ i:V,(s i+2)
local notation "G"=>V→ Cover
local notation "Z!"=> 4*Fintype.card V
abbrev foam (V:Type)[Fintype V][DecidableEq V](S r:ℝ):=plot V (rateBlue S r)
noncomputable def scoreQ (V:Type)(j:V→Cover)(r:ℝ):=fun i=>clue r (j i)
local notation "Z"=> scoreQ V
noncomputable def originalQ (d:ℕ)(S r:ℝ) (u:E):= ∑ i∈ foam V S r,chord (bundle r (Z i r)) (package d (Z i r) (F u))
noncomputable def mintBase (s:V→ℕ) (S:ℝ) (d:ℕ):= load V S * bmint s d
lemma bmint_pos (d:ℕ):0≤bmint s d:=Finset.sum_nonneg fun _ _=> mul_nonneg (mortar_pos ..).le (Finset.prod_nonneg fun _ _=> (bond_pos ..).le)
lemma original_cap (h:Stone d Ω F) (hc:0 ≤ C')(hC: Plant Ω C F x₀)
    (r S:ℝ) (hr:0<r)(hx:r ≤ 1)(hrP:2*r ≤ x₀)(hs:0≤ S)(hd:∀ u∈Ω,Tall (F u) d 1 C'):
    Bouquet s Ω C (originalQ F d S r) (mintBase s S d*r⁻¹^(D+Z!)* C'):=by
    let T:= foam V S r; let k:= D; have hp:= Bouquet.all (F:=fun i:G=>fun z=> chord (bundle r (Z i r)) (package d (Z i r) (F z))) T (fun i _=>from_start s Ω C F C' _ _ r hr hx h hC hrP hc hd); apply hp.permit (fun _ _=>rfl); have hv:= leaves (V:=V) S r hs hr hx
    have hl:0 ≤ bmint s d*r⁻¹^k*C':=by have h:=bmint_pos s d; positivity
    apply (mul_le_mul_of_nonneg_right hv hl).trans_eq; unfold mintBase;rw [pow_add]; unfold k; ring
-- step between unit grids, plus allow single Hermite centers
noncomputable def links (r t:ℝ)(x:U)(L:Finset (V→Cover)): Finset (V→Cover) := L.filter fun j=> ‖Z j t - x‖ ≤ 4*r
lemma countCredit (r t:ℝ)(ht:0<t)(h:r ≤ 2*t)(x:U)(L:Finset (V→Cover)) : (links r t x L).card ≤ (plot V 16).card := by
    apply piece_count t ht 8 x; intro y hy; have he: ‖Z y t-x‖ ≤ 4*r:= (Finset.mem_filter.mp hy).2; change ‖scoreQ V y t-x‖ ≤ _; norm_num;linarith only [he,h]
-- purchase one patch over any subset
lemma one_frost (h:Stone d Ω F) (hc:0≤ C')(hC:Plant Ω C F x₀) (r t:ℝ)(ht:0<t)(hv:t≤r)(hx:r≤ 2*t)(hrP:2*r ≤x₀)(hr':r ≤1)(hd:∀ u∈Ω,Tall (F u) (d+1) 1 C') (hp:D ≤ d+1)(x:U)(K:Finset (V→Cover)) :
    Bouquet s Ω C (∑ i∈links r t x K,triangleX d x (Z i t) r t F) (((plot V 16).card:ℝ) * (pellets s d 4* r^(d+1-D)*C')):=by
      let f(i:G):=triangleX d x (Z i t) r t F; let L:= links r t x K; let H:= pellets s d 4*r^(d+1-D)*C'; have he:=Bouquet.all (F:=f) L (fun i hi=>spread s Ω C F C' _ h hc hC r t x (Z i t) ht hv hr' hx hrP (fun u hu x=>by simpa only [one_pow,one_mul] using hd u hu _ le_rfl x) (Finset.mem_filter.mp hi).2 hp)
      refine he.permit (fun i hi=>by rw [Finset.sum_apply]) ?_; exact mul_le_mul_of_nonneg_right (mod_cast countCredit r t ht hx x K) (mul_nonneg (mul_nonneg (pellets_good _ _) (pow_nonneg (ht.le.trans hv) _)) hc)
noncomputable def stepQ (d:ℕ)(S r t:ℝ) := ∑ i∈ foam V S r,∑ j∈ links r t (Z i r) (foam V S t), triangleX d (Z i r) (Z j t) r t F
noncomputable def redeem (s:V→ℕ)(d:ℕ)(S:ℝ):ℝ:= load V S*(plot V 16).card * pellets s d 4
lemma redeem_pos (d:ℕ)(S:ℝ)(hs:0≤ S):0 ≤ redeem s d S:=by unfold redeem load; have ht:=pellets_good (d:=d) s 4; positivity
lemma step_cap (h:Stone d Ω F)(hc:0≤ C')(hC:Plant Ω C F x₀)(r t S:ℝ)(ht:0<t)(hr:t ≤ r)(hx:r ≤ 2*t)(hv:2*r≤ x₀)(hr':r≤1)(hs:0≤S)(hH:∀ u∈Ω,Tall (F u) (d+1) 1 C')(hp:D+Z!<d+1): Bouquet s Ω C (stepQ F d S r t) (redeem s d S*r*C'):=by
    have h₁:= Bouquet.all (F:=fun i=>∑ j∈links r t (Z i r) (foam V S t), triangleX d (Z i r) (Z j t) r t F) (foam V S r) (fun i _=> one_frost s Ω C F C' _ h hc hC r t ht hr hx hv hr' hH (by omega) _ _); refine h₁.permit (fun i hi=> by unfold stepQ; rw [Finset.sum_apply]) ?_
    have hr'' := ht.trans_le hr; apply (mul_le_mul_of_nonneg_right (leaves S r hs hr'' hr') (mul_nonneg (Nat.cast_nonneg ((plot V 16).card)) (mul_nonneg (mul_nonneg (pellets_good s 4) (pow_nonneg hr''.le (d+1-D))) hc))).trans; let k:=d+1-(D+Z!); let Z₀:=Z!
    have he:r^(d+1-D) = r^ Z₀ * r^k:=by
        rw [←pow_add]; congr 1; unfold k Z₀; omega
    rw [he]; apply le_trans (le_of_eq (b:=redeem s d S * r^k * C') ?_)
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (show r^k ≤ r from calc
                           _ ≤ r^(1:ℕ) := pow_le_pow_of_le_one hr''.le hr' (by dsimp only [k]; omega)
                           _ = _ := pow_one _) (redeem_pos s d S hs)) hc
    change load V S * r⁻¹^Z₀ * _=_; unfold redeem; rw [inv_pow]; field_simp
-- activation. supplement a regular old patch to any fine list x over Z
omit [TopologicalSpace E] in
lemma unpair (S r t:ℝ)(hr:0<t)(ht:t≤ r)(x y:U)(j:V→Cover)(hj:j∈foam V S t)(he: j ∉ links r t x (foam V S t)) (p:W): (chord (bundle r x) (chord (bundle t (Z j t)) p)).val y=0:=by
    change (bundle r x).val y*((bundle t (Z j t)).val y*p.val y)=0; by_cases hx:y∈tsupport (bundle r x).val; swap; · rw [image_eq_zero_of_notMem_tsupport hx,zero_mul]
    have hp': ‖Z j t-x‖ ≤ ‖y-x‖+‖y-Z j t‖:=by rw [add_comm]; nth_rw 2 [norm_sub_rev]; exact norm_sub_le_norm_sub_add_norm_sub ..
    have hv: 4*r< ‖Z j t-x‖:=lt_of_not_ge (fun h=>he (Finset.mem_filter.mpr ⟨hj,h⟩)); rw [bundle_die (Z j t) y t,zero_mul,mul_zero]; exact hr; linarith only [hv,hp',ht,bundled x r (hr.trans_le ht) y hx]
omit [TopologicalSpace E] in
lemma step_glove (d:ℕ)(r t S:ℝ)(x:U)(j:E)(hx:‖x‖< S)(ht:0<t)(hr:t≤r): (stepQ F d S r t j).val x=(originalQ F d S t j).val x-(originalQ F d S r j).val x:=by
   let T:= foam V S t; let L:= foam V S r; let g(i:G):=(bundle r (Z i r)).val x; let w(i:G):=(bundle t (Z i t)).val x; let u(a:ℝ)(i:G):=(package d (scoreQ V i a) (F j)).val x; let R:=u r; let B:=u t; have htP:∑ i∈T,w i=1:=fair S t ht x hx -- edit
   have hrP:∑ i∈L,g i=1:=fair S r (ht.trans_le hr) _ hx
   have he(i:G): (∑ k∈ links r t (Z i r) T, ((triangleX d (Z i r) (Z k t) r t F j).val x))=∑ k∈T,g i*w k*(B k-R i):=by
       rw [← Finset.sum_subset (show links r t (Z i r) T⊆ T from Finset.filter_subset _ _)];
       · exact Finset.sum_congr rfl (fun k _=> (mul_assoc (g i) (w k) _).symm)
       intro k hk hl; rw [mul_assoc]; exact unpair S r t ht hr _ _ k hk hl (package d (Z k t) (F j)-package d (Z i r) (F j))
   unfold stepQ; simp only [Finset.sum_apply, AddSubmonoidClass.coe_finsetSum]; change (∑ i∈ L,∑ k∈ links r t (Z i r) T, ((triangleX d (Z i r) (Z k t) r t F j).val x))=_; simp_rw [he]; unfold originalQ; simp only [AddSubmonoidClass.coe_finsetSum,Finset.sum_apply];
   change _ = (∑ i∈T, w i * B i) - ∑ i∈L,g i*R i
   simp_rw [mul_sub,Finset.sum_sub_distrib]; refine congr_arg₂ Sub.sub ?_ ?_
   · simp_rw [mul_assoc,← Finset.mul_sum,← Finset.sum_mul]; rw [hrP,one_mul]
   conv_lhs =>
       arg 2; intro i
       arg 2; intro k
       rw [mul_right_comm (g i)]
   simp_rw [← Finset.mul_sum,htP, mul_one]
end piece
end YM.RG05Readout.Nuclear
