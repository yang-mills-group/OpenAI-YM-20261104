import YM.SchemeRG11.Wilson.Compare
import YM.SchemeRG11.Cover.Table
import YM.SchemeRG11.Cover.Shear
/-! Comparison on growing structures through polynomials in circumference. -/
set_option autoImplicit false
noncomputable section
namespace YM.SchemeRG11.Tile
open MvPolynomial Lattice Haze Catch Pert Align Filter Asymptotics Function
open scoped Classical Topology
variable {I J: Type*}
section trajectories
variable {U V W : ℕ→ℝ} {T:Itinerary}
def Capped (U:ℕ→ℝ) := ∃ C:ℝ,∀ᶠ i in atTop, |U i|≤ C
lemma Cap (u:ℕ→ℝ): Capped u ↔ u=O[atTop](fun _=>(1:ℝ)):=by rw [isBigO_iff]; simp [Capped]
lemma Capped.add(hu:Capped U)(hv:Capped V): Capped (fun i=>U i+V i):=(Cap _).2 (((Cap _).1 hu).add ((Cap _).1 hv))
lemma Capped.mul(hu:Capped U)(hv:Capped V): Capped (fun i=>U i*V i):=by apply (Cap _).2; simpa using (((Cap _).1 hu).mul ((Cap _).1 hv))
lemma capped_c (z:ℝ):Capped (fun _=> z):= ⟨|z|, Eventually.of_forall fun _=> le_rfl⟩
lemma flatC (hf:Flat T U): Capped U:=⟨1,hf.naked.abs.eventually (ge_mem_nhds (by simp))⟩
lemma flatter(hf:Flat T U)(hv:Capped V):Flat T (fun i=> V i*U i):=by
 intro d; have he:= hf d; rw [← isLittleO_one_iff (F:=ℝ)] at he
 simp_rw [mul_left_comm ((T.gap _)^(-(d:ℤ)))]; exact (isLittleO_one_iff (F:=ℝ)).1 (by simpa using (((Cap _).1 hv).mul_isLittleO he))
lemma powerFlat (k:ℕ)(hf:Flat T U): Flat T (fun i=> (T.gap i)⁻¹^k * U i) :=by
 intro d; have ht(i:ℕ): 0 < T.gap i:= T.positive i
 have hh i: (T.gap i)^(-(d:ℤ))* ((T.gap i)⁻¹^k*U i)= (T.gap i)^(-((d+k:ℕ):ℤ))*U i:=by push_cast; rw [neg_add,zpow_add₀ (ht i).ne',zpow_neg,zpow_natCast, zpow_neg,zpow_natCast, inv_pow]; ring
 simp_rw [hh]; exact hf (d+k)
lemma zeroF(T:Itinerary): Flat T (fun _ =>0):=by intro i; simp
lemma sameF(h: Flat T U)(he: U=ᶠ[atTop]V): Flat T V:=by intro i; apply (h i).congr'; filter_upwards [he] with j hj; rw [hj]
lemma subF(hu:Flat T (fun i=>U i-V i))(hv:Flat T (fun i=>V i-W i)): Flat T (fun i=>U i-W i):=by simpa only [sub_add_sub_cancel] using hu.add hv
lemma finFlat {ι:Type*}(s:Finset ι)(F:ι→ℕ→ℝ)(H:∀ i∈s, Flat T (F i)): Flat T (fun n=>∑ i∈s,F i n):=by induction s using Finset.induction_on with | empty=> simpa using zeroF T | insert a s ha hi=> simp only [Finset.sum_insert ha]; exact (H a (Finset.mem_insert_self ..)).add (hi fun i h=>H _ <| Finset.mem_insert_of_mem h)

variable {D N : ℕ→Dose I ℝ}
private lemma refund{B:Type*}(v:B → I) (D:Dose I ℝ)(s : Finset B)(i:B)(hi:i∈s):
 let m(t:Finset B):=∏ j∈t, (MvPolynomial.X (v j):Paper I ℝ)
 D.avg (m s)=∑ j∈s.erase i,D.pulse (v i) (v j)*D.avg (m ((s.erase i).erase j)):=by -- B binder
 dsimp only; rw [← Finset.prod_erase_mul _ _ hi,D.release]
 let g(a:B): Stem I ℝ:= Finsupp.single (v a) 1
 have hx a: MvPolynomial.X (v a)=leaf (g a):=by unfold leaf g; rw [Finsupp.linearCombination_single,one_smul]
 have he(w:I→ℝ)(b:B): sense w (g b)=w (v b):=by unfold sense g; rw [Finsupp.linearCombination_single,one_smul]
 simp_rw [hx,taste_prod, he,map_sum,map_smul,smul_eq_mul]
lemma trailedProd {B:Type*} (v:B→I)(s: Finset B)(H:∀ i j,Capped (fun k=>(D k).pulse i j))(L:∀ i j,Flat T (fun k=> (N k).pulse i j-(D k).pulse i j)) :
 let g(t:Finset B):= ∏ i∈t,(X (v i):Paper I ℝ)
 Capped (fun n=> (D n).avg (g s)) ∧ Flat T (fun n=>(N n).avg (g s)-(D n).avg (g s)):=by
 dsimp only
 let g(t:Finset B):= ∏ i∈t,(X (v i):Paper I ℝ)
 induction s using Finset.strongInduction with | H s ih =>
   by_cases hb : s.Nonempty
   · obtain ⟨a,ha⟩:=hb
     let f (U : ℕ→Dose I ℝ)(b:B) (i:ℕ):=(U i).pulse (v a) (v b) * (U i).avg (g ((s.erase a).erase b))
     have he (U :ℕ→Dose I ℝ)(i:ℕ): (U i).avg (g s) = ∑ b∈s.erase a,f U b i:= refund v _ s a ha
     have hp b:= ih ((s.erase a).erase b) (lt_of_le_of_lt (Finset.erase_subset _ _) (Finset.erase_ssubset ha))
     change Capped (fun n=>(D n).avg (g s)) ∧ Flat T _
     constructor
     · simp_rw [he]; apply (Cap _).2; apply Asymptotics.IsBigO.sum; intro b hb; exact (Cap _).1 ((H _ _).mul (hp b).1)
     change Flat T (fun n=>(N n).avg (g s)-(D n).avg (g s)); simp_rw [he,←Finset.sum_sub_distrib]; apply finFlat; intro b _
     have ht : Capped (fun n=>(N n).pulse (v a) (v b)):=by simpa only [sub_add_cancel] using (flatC (L (v a) (v b))).add (H (v a) (v b))
     have hj := (flatter (L (v a) (v b)) (hp b).1).add (flatter (hp b).2 ht)
     apply sameF hj; filter_upwards with i; dsimp [f,g]; ring
   rw [Finset.not_nonempty_iff_eq_empty.mp hb]; simp only [Finset.prod_empty,Dose.avg_one,sub_self]; exact ⟨capped_c 1,zeroF T⟩
lemma trails (p:Paper I ℝ)(H:∀ i j,Capped (fun k=>(D k).pulse i j))(L:∀ i j,Flat T (fun k=> (N k).pulse i j-(D k).pulse i j)): Capped (fun n=>(D n).avg p) ∧ Flat T (fun n=>(N n).avg p-(D n).avg p):=by
 have he(m:I→₀ℕ)(r:ℝ): Capped (fun n=>(D n).avg (monomial m r)) ∧ Flat T (fun n=>(N n).avg (monomial m r)-(D n).avg (monomial m r)):=by
   let B:=(u : ↥m.support)× Fin (m u.val)
   let v:B→I:=fun i=>i.1.val
   have hb: (monomial m r)=r • ∏ i:B, (X (v i):Paper I ℝ):=by
     rw [monomial_eq, C_mul',Finsupp.prod,← Finset.prod_attach]; congr 1; unfold B v; rw [Fintype.prod_sigma];simp
   have hp:=trailedProd v Finset.univ H L
   simp only [hb,map_smul,smul_eq_mul,←mul_sub]
   exact ⟨(capped_c r).mul hp.1,flatter hp.2 (capped_c r)⟩
 rw [←p.support_sum_monomial_coeff]; simp only [_root_.map_sum,← Finset.sum_sub_distrib]
 refine ⟨?_,finFlat _ _ (fun i _=>(he i _).2)⟩
 apply (Cap _).2; apply Asymptotics.IsBigO.sum; intro i _; exact (Cap _).1 ((he i _).1)
end trajectories
end YM.SchemeRG11.Tile
