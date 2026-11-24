import YM.RG05Readout.Nuclear.Pings
/-! Expand.Torus/read presentation in C^t.Signed across all slots.
 Envelope via derivative-power budget global, gives uniform.Cap after
 localization.Box only.Regulator prices absolute. No sum underdetermined.
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
abbrev Allow (V:Type):= (V→Body)→Prop
variable (s:V→ℕ)(Ω:Set E)(C:Allow V)
-- exact decomposition consumes clearance per-call only. Norm unit **global**, also ensures Cap.
inductive Bouquet (s:V→ℕ)(Ω:Set E)(C:Allow V): (E→ Wave V)→ ℝ → Prop
    | empty : Bouquet s Ω C 0 0
    | bloom (f:V→Body)(a:E→ℂ)(t:ℝ) (h:ContinuousOn a Ω)(ha:∀ x∈ Ω, ‖a x‖≤ t)(ht:0 ≤ t)(hf:∀ i, Tall (E:=E4) (f i) (s i+2) 1 1)(hc:C f): Bouquet s Ω C (fun x=> a x • joint Finset.univ f) t
    | add {u v p q}(hu:Bouquet s Ω C u p)(hv:Bouquet s Ω C v q): Bouquet s Ω C (u+v) (p+q)
    | permit {u v p q}(hu:Bouquet s Ω C u p)(hx: EqOn u v Ω)(hp:p≤q): Bouquet s Ω C v q
-- stronger Tall patch cap for later Shot.Photo.Priced
namespace Bouquet
variable {s Ω C}
omit [DecidableEq V] in
lemma pos {v r}(h:Bouquet s Ω C v r):0≤r:=by induction h with|empty=>exact le_rfl| bloom _ _ _ _ _ ht _ _=> exact ht| add _ _ a b=> exact add_nonneg a b | permit _ _ h ih=> exact ih.trans h
omit [DecidableEq V] in
lemma sum (I:Finset J)(p:J→ℝ){F:J→ E→Wave V}(h:∀ i∈I,Bouquet s Ω C (F i) (p i)) : Bouquet s Ω C (∑ i∈I,F i) (∑ i∈I,p i) :=by
    induction I using Finset.induction with
    | empty=> simp only [Finset.sum_empty]; exact Bouquet.empty
    | insert i L he ih=> rw [Finset.sum_insert he,Finset.sum_insert he]; exact (h i (Finset.mem_insert_self ..)).add (ih (fun j hj=> h j (Finset.mem_insert_of_mem hj)))
omit [DecidableEq V] in
lemma all {F:J→E→ Wave V} (L:Finset J){p:ℝ}(h:∀ i∈L,Bouquet s Ω C (F i) p): Bouquet s Ω C (fun x=>∑ i∈L,F i x) ((L.card:ℝ)*p):= by
    have hp:= Bouquet.sum L (fun _=>p) h; rw [show (∑ i∈ L, F i)=fun x=>∑ i∈ L,F i x from funext fun i=> by rw [Finset.sum_apply],Finset.sum_const,nsmul_eq_mul] at hp; exact hp
omit [DecidableEq V] in
lemma normalize {c:V→ℝ}{F:V→Body}{a:E→ℂ}{t:ℝ} (ha:ContinuousOn a Ω)(hp:∀ x∈Ω,‖a x‖≤ t)(ht:0≤t)(h:∀ i,0<c i)(hc:∀ i,Tall (E:=E4) (F i) (s i+2) 1 (c i))(hF:C (fun i=> ((↑(c i):ℂ))⁻¹ • F i)): Bouquet s Ω C (fun x=>a x • joint Finset.univ F) (t*∏ i,c i):=by
    let y:= fun i=> ((↑(c i):ℂ))⁻¹ • F i; let z:ℂ:=∏ i,(c i:ℂ); have ha': ‖z‖=∏ i,c i:=by unfold z; rw [norm_prod]; exact Finset.prod_congr rfl (fun i _=>by simp [(h i).le])
    have hG(i):Tall (E:=E4) (y i) (s i+2) 1 1:=fun j hj x=>by
        unfold y; rw [SetLike.val_smul,iteratedFDeriv_const_smul_apply (body_smooth .. |>.contDiffAt),norm_smul,norm_inv,Complex.norm_real, Real.norm_of_nonneg (h i).le];
        exact (mul_le_mul_of_nonneg_left (hc i j hj x) (inv_pos.mpr (h i)).le).trans_eq (by rw [mul_left_comm,inv_mul_cancel₀ (h i).ne'])
    have hp' i : F i=(c i:ℂ) • y i:=(smul_inv_smul₀ (by exact_mod_cast (h i).ne') _).symm
    have hv: z • joint Finset.univ y= joint Finset.univ F:=Subtype.ext (funext fun x=>by change z*(∏ i,(y i).val (x i))=∏ i,(F i).val (x i); calc
                   _=∏ i,(c i:ℂ)*(y i).val (x i):= Finset.prod_mul_distrib.symm
                   _=_:= Finset.prod_congr rfl fun i _=> congr_fun (congr_arg Subtype.val (hp' i).symm) _ ) -- syntax
    have hm(x)(hx:x∈Ω): ‖a x*z‖ ≤ t*∏ i,c i :=by rw [norm_mul]; rw [← ha'];exact mul_le_mul_of_nonneg_right (hp x hx) (norm_nonneg _)
    exact (bloom y (fun x=>a x*z) _ (ha.mul continuousOn_const) hm (by rw [←ha']; positivity) hG hF).permit (fun i _=>by dsimp only; rw [mul_smul,hv]) le_rfl
end Bouquet
section
-- BR certificate *slot root Cartesian*: robust support around actual live coordinate
variable (F:E→Wave V)(C':ℝ)(x₀:ℝ)
abbrev Plant (Ω:Set E)(C:Allow V)(F:E→Wave V)(r:ℝ):Prop:= ∀ u∈ Ω,∀ x∈ tsupport (F u).val,∀ f:V→Body, (∀ i y,y∈tsupport (f i).val → ‖y-x i‖≤ r) → C f
-- smooth enough Θ steering (no cost on τ variation).
abbrev Stone (d:ℕ)(Ω:Set E)(F:E→Wave V) := ∀ i ≤ d,∀ (x:Cloud V),ContinuousOn (fun u=> iteratedFDeriv ℝ i (F u).val x) Ω
lemma soft_print (z:Column V d)(x:U)(r:ℝ)(h:Stone d Ω F): ContinuousOn (fun u=>print (fork r x (F u)) z) Ω:=by
    unfold print Tensor.coeff; simp_rw [shoots,smul_zero,add_zero]; let X:=page V z.fst; have hp:= h (deep z) (Nat.le_of_lt_succ z.fst.isLt) x; let g(u): Tensor.T U ℂ z.fst:= (↑(deep z).factorial:ℝ)⁻¹ • r^(deep z) • iteratedFDeriv ℝ (deep z) (F u).val x; have ht: ContinuousOn g Ω:= (hp.const_smul (r^(deep z))).const_smul ((↑(deep z).factorial:ℝ)⁻¹);
    exact ((continuous_apply z.snd.fst).comp_continuousOn (X.continuous.comp_continuousOn ht)).mul continuousOn_const
omit [DecidableEq V] in
lemma Stone.package (hs:Stone d Ω F)(x:U): Stone d Ω (fun u=> Nuclear.package d x (F u)):=by
   intro n hn y; unfold Nuclear.package; simp_rw [fork_at]; let T u:= fork 1 x (F u); let z := -x+y
   let V'(u):= port (T u) d
   let X(i:ℕ)(u:E):= Tensor.coeff (T u).val i 0
   have he (u:E):iteratedFDeriv ℝ n (V' u).val z=∑ i∈ Finset.range (d+1),iteratedFDeriv ℝ n (Tensor.diagonal (X i u)) z:= by
        change iteratedFDeriv ℝ n (∑ i∈ Finset.range _,Tensor.diagonal (X i u)) z=_
        rw [iteratedFDeriv_sum_apply (fun i _=> (diag_smooth ..).contDiffAt)]
   have hV:∀ i∈ Finset.range (d+1),ContinuousOn (fun u=> iteratedFDeriv ℝ n (Tensor.diagonal (X i u)) z) Ω:=by
        intro i hi; have ht:i ≤ d:=Nat.le_of_lt_succ (Finset.mem_range.mp hi); have hT:ContinuousOn (X i) Ω:= by
            unfold X Tensor.coeff T; simp_rw [fork_at, add_zero]; exact (hs i ht x).const_smul ((i.factorial:ℝ)⁻¹)
        let L : Tensor.T U ℂ i →ₗ[ℝ] Tensor.T U ℂ n:= {
            toFun:=fun u=> iteratedFDeriv ℝ n (Tensor.diagonal u) z
            map_add':=fun x y=> iteratedFDeriv_add_apply (diag_smooth x _|>.contDiffAt) (diag_smooth y _|>.contDiffAt)
            map_smul' :=fun c a=>iteratedFDeriv_const_smul_apply (diag_smooth a _|>.contDiffAt)}
        exact L.toContinuousLinearMap.continuous.comp_continuousOn hT
   change ContinuousOn (fun u=> iteratedFDeriv ℝ n (V' u).val z) Ω; simp_rw [he]; exact continuousOn_finsetSum _ hV
omit [TopologicalSpace E] [DecidableEq V] in
lemma zero_package (u:E)(x:U)(h:x∉tsupport (F u).val)(d:ℕ): Nuclear.package d x (F u)=0:=by
    unfold Nuclear.package; let Y:= Pulse.fork 1 x (F u); have hp: port Y d=0:= by
        apply Subtype.ext; change Work.G05.blockTaylor d Y.val=0; unfold Work.G05.blockTaylor; apply Finset.sum_eq_zero
        intro i _; unfold Y Tensor.coeff; rw [fork_at,add_zero,show iteratedFDeriv ℝ i (F u).val x=0 from notMem_support.mp (fun hx=> h (support_iteratedFDeriv_subset i hx)),smul_zero]; rfl
    rw [show port _ _=0 from hp,map_zero]
lemma scaled_support (a:ℂ)(x:Body): tsupport (a • x).val ⊆ tsupport x.val:= by
    apply closure_mono; intro i hi; exact fun he=> hi (by change a*x.val i=0;rw [show x.val i=0 from he,mul_zero])
-- stable budget for exact first patch from plant.Policy radius.Comparable derivatives
noncomputable def bmint (s:V→ℕ)(d:ℕ):ℝ:= ∑ z:Column V d, (mortar V d 1 z)* ∏ i,bond (popV z i) (s i+2)
lemma from_start (x:U) (r:ℝ)(hr:0<r)(hv:r ≤ 1)(h:Stone d Ω F) (φ:Plant Ω C F x₀) (hd:2*r≤ x₀)(hc:0≤ C')(hg:∀ z∈Ω, Tall (F z) d 1 C') :
     Bouquet s Ω C (fun z=> chord (bundle r x) (Nuclear.package d x (F z))) (bmint s d *r⁻¹^(∑ i:V,(s i+2))*C'):=by
    let V' u:= Nuclear.package d x (F u); let u (a:Column V d)(z):=print (fork r x (V' z)) a; let f (a:Column V d):=fun i:V=>patchShift (x i) r (popV a i); let K(a:Column V d):=fun i:V=> chord (pebble r (x i)) (f a i); let L:= Finset.univ (α:=Column V d);
    have hU(a:Column V d): ContinuousOn (u a) Ω:=soft_print Ω V' a x r (h.package Ω F x) -- edit
    let w(a:Column V d)(i:V):=r⁻¹ ^(s i+2)* bond (popV a i) (s i+2); let W'(a:Column V d):= mortar V d 1 a*C'
    have he:L.sum (fun a=> W' a*∏ i,w a i)= bmint s d*r⁻¹^(∑ i:V,(s i+2))*C':=by unfold W' bmint w; simp_rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro z _; rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]; ring
    let Y(i:Column V d)(z:E):Wave V := u i z • joint Finset.univ (K i)
    have hP:∀ u:E, chord (bundle r x) (V' u)=∑ i:Column V d,Y i u:=by
        intro u; unfold V'; nth_rw 1 [print_local _ (pol_above x (F u) d.lt_succ_self) r hr.ne' x]; rw [map_sum]; exact Finset.sum_congr rfl fun j _=> by rw [map_smul,bundle, tiedC]
    rw [← he]; by_cases hx: ∃ u∈Ω,x∈ tsupport (F u).val
    swap
    · refine Bouquet.permit Bouquet.empty ?_ ?_; exact fun i hi=>by rw [zero_package F i x (fun he=> hx ⟨i,hi,he⟩),map_zero]; rfl
      refine Finset.sum_nonneg fun a _=> mul_nonneg (mul_nonneg (mortar_pos ..).le hc) (Finset.prod_nonneg (fun i _=> mul_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) _) (bond_pos ..).le))
    obtain ⟨a,hΩ,hΦ⟩:= hx; refine (Bouquet.sum L (F:=Y) (fun a=> W' a*∏ i,w a i) ?_).permit (fun z hz=>by rw [Finset.sum_apply]; exact (hP z).symm) le_rfl
    intro i _; have hW (j:V):0<w i j:= mul_pos (pow_pos (inv_pos.mpr hr) _) (bond_pos ..)
    refine Bouquet.normalize (hU i) ?_ (mul_nonneg (mortar_pos ..).le hc) hW ?_ ?_
    · intro z hz; let A:= mortar V d 1 i
      have hf(i):= hg z hz i; have hp: ‖iteratedFDeriv ℝ (deep i) (V' z).val x‖ ≤C':=by rw [show iteratedFDeriv ℝ _ (V' z).val _=_ from (pol_cost x (F z) (show deep i≤d from Nat.le_of_lt_succ i.fst.isLt)).symm]; simpa using hf _ (Nat.le_of_lt_succ i.fst.isLt) x
      exact (press_cost i (V' z) r x hr hp).trans (by
           have ht :=pow_le_one₀ (n:=deep i) hr.le hv; unfold W' mortar; simp only [Nat.cast_one,one_pow,mul_one]; rw [mul_right_comm _ C' ]; apply mul_le_mul_of_nonneg_right _ hc; refine le_trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by positivity) ht) (norm_nonneg _)) (le_add_of_nonneg_left zero_le_one))
    · intro j t ht z; rw [one_pow,one_mul]; exact (Tiepatch (x j) (popV i j) r hr (s j+2) t ht z).trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (one_le_inv₀ hr|>.mpr hv) ht) (bond_pos ..).le) -- edit
    exact φ _ hΩ x hΦ _ (fun i' y hh => (pebble_live r hr _ y (collar (scaled_support _ _ hh)|>.1)).trans hd)
end
end YM.RG05Readout.Nuclear
