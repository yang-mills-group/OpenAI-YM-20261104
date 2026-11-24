import YM.Ac.Tree
import YM.Push.ABSOLUTE_SUMS.Basic

/-!
# Tree estimates for distinct addresses

`expose` sums over the subsets of all buds meeting the incoming support.
Write `sites M = (2 * M + 1)^4`. For nonnegative weights, the hit estimate at
exponent `a + 1` and the bound `sites M * γ ≤ 1` give a sum budget for the
rooted terms at `a + spare M`. Its upper bound is `exp (keep M * γ) - 1`,
where `spare M = 1 / (8 * sites M)` and `keep M = 1 - 1 / (4 * sites M)`.

`against` gives the bound `exp γ - 1` at exponent `a` from a hit estimate
at `a + τ` and the inequality `sites M * γ ≤ τ`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.StellarTree
open Lattice Wilson RG Function Relation Finset
open scoped Topology BigOperators Classical
variable {ι : Type*} [DecidableEq ι] {n : Side} (X : ι → Support n) (M : ℕ)

-- Exposure from *all* first-wave neighbors
private abbrev crown (D:Finset ι)(Y:Support n)(s:Finset ι):= s∩ Ac.buds X D Y
private abbrev root (_D:Finset ι)(Y:Support n)(u:Finset ι):= (u.biUnion X) \ Y

private lemma wave {D s : Finset ι} {Y : Support n} (hs:s∈Ac.pouch X D Y):
    let B:=Ac.buds X D Y; let u:= crown X D Y s; let R:= root X D Y u
    s\u ∈Ac.pouch X (D\B) R:= by
  intro B u R
  rw [Ac.op]; obtain ⟨hd,h⟩:= (Ac.op _ _ _).mp hs
  have he(i)(hi:i∈s)(hz:i∈B):i∈u:=mem_inter.mpr ⟨hi,hz⟩
  constructor
  · intro i hi; obtain ⟨hs,hU⟩:=mem_sdiff.mp hi; exact mem_sdiff.mpr ⟨hd hs,fun hj=>hU (he _ hs hj)⟩
  intro k hk
  have hi := (mem_sdiff.mp hk).1
  obtain ⟨j,hj,hZ,H⟩:= h k hi
  induction H with
  | refl=> exact ((mem_sdiff.mp hk).2 (he _ hi ((Ac.alive ..).mpr ⟨hd hi,hZ⟩))).elim
  | @tail l k _ H ih=>
    have hl:l ∈s := H.1
    by_cases hz:l∈u
    · have hk':k∉B:=fun hc=>(mem_sdiff.mp hk).2 (he k hi hc)
      obtain ⟨x,hx,hx'⟩:=H.2.2
      refine ⟨k,hk,⟨x, mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨l,hz,hx⟩,fun hr=> hk' ((Ac.alive ..).mpr ⟨hd hi,x,hr,hx'⟩)⟩,hx'⟩,.refl⟩
    have h₃:l∈s\u:=mem_sdiff.mpr ⟨hl,hz⟩
    obtain ⟨m,hm,hM,hH⟩:= ih h₃ hl
    exact ⟨m,hm,hM, .tail hH ⟨h₃,hk,H.2.2⟩⟩

lemma expose (D : Finset ι)(Y : Support n)(f:ι→ℝ)(hf:∀ i,0≤f i):
    let B:=Ac.buds X D Y; Ac.film X D Y f ≤ ∑ u∈ B.powerset, (∏ i∈u,f i)*Ac.film X (D\B) (root X D Y u) f:= by
  intro B
  let rail(s:Finset ι):=crown X D Y s
  let p(s:Finset ι):=∏ i∈s,f i
  let C:=Ac.pouch X D Y
  unfold Ac.film; change C.sum p ≤ _
  rw [← Finset.sum_fiberwise_of_maps_to (g:=rail) (t:=B.powerset) (by intro _ _; exact Finset.mem_powerset.mpr (inter_subset_right))]
  apply sum_le_sum; intro u _
  let S:= C.filter (fun z=> rail z=u)
  let l(s:Finset ι):=s\u
  have he (s)(h:s∈S) : rail s=u:=(mem_filter.mp h).2
  have ht (s)(h:s∈S): u⊆s:= he s h ▸ inter_subset_left
  have hr (s)(h:s∈S): u ∪ l s = s:= by rw [union_sdiff_self_eq_union, Finset.union_eq_right.mpr (ht s h)]
  have hu:Set.InjOn l S:=fun a h b hb hh=> by rw [←hr _ h, hh,hr _ hb]
  have hy : S.image l ⊆ Ac.pouch X (D\B) (root X D Y u):=by
    intro t hh; rcases mem_image.mp hh with ⟨v,hv,rfl⟩
    unfold l; rw [← he _ hv]
    exact wave X (mem_filter.mp hv).1
  change S.sum p ≤ _
  calc
    _ = p u*(∑ v∈S.image l,p v):= by
      rw [mul_sum,sum_image hu]; apply sum_congr rfl; intro z hz; nth_rw 1 [←hr _ hz]; exact Finset.prod_union (disjoint_sdiff_self_right)
    _ ≤ _:= mul_le_mul_of_nonneg_left (sum_le_sum_of_subset_of_nonneg hy fun i _ _=> prod_nonneg fun j _=>hf _) (prod_nonneg fun j _=>hf _)

/-- V term in Ac.Hit geometry. -/
def sites (M:ℕ):ℝ:=((M+M+1:ℕ):ℝ)^4
lemma sites_one : 1 ≤ sites M:=by unfold sites; apply one_le_pow₀; exact_mod_cast (show 1≤M+M+1 by omega)
lemma sites_pos : 0 < sites M:= zero_lt_one.trans_le (sites_one M)
private lemma bill (X:Support n): (X.card:ℝ) ≤ coverNumber M X * sites M:= by unfold sites; exact_mod_cast Corona.pays X M

/-- V^{-1} margin on the fusing stage. No post-L constants needed, use on ANY
calendar parameter. -/
def cut (M:ℕ):ℝ:= (sites M)⁻¹/4
def keep (M:ℕ):ℝ:= 1-cut M
def spare (M:ℕ):ℝ:=cut M/2
lemma cut_pos : 0 < cut M:=div_pos (inv_pos.mpr (sites_pos _)) (by norm_num)
lemma keep_range : 3/4 ≤ keep M ∧ keep M ≤1:= by
  have h:=inv_anti₀ zero_lt_one (sites_one M); rw [inv_one] at h
  have he:=inv_nonneg.mpr (sites_pos M).le
  unfold keep cut; constructor<;> linarith
lemma spare_pos : 0<spare M:= div_pos (cut_pos M) (by norm_num)

/-- Improvement of Ac.forest for arbitrary γ in its original range,
 gaining a strictly positive cover exponent and volume-dependent cap margin.
 The save occurs even WITH the stronger output exponent. -/
private lemma pay (γ a:ℝ)(_hγ:0 ≤ γ)(h:sites M * γ ≤ 1)(S:Support n)(hs:S.Nonempty) :
    Real.exp ((a+spare M)*(coverNumber M S:ℝ)+(((S.card:ℝ)-1)*(keep M*γ))) ≤ keep M * Real.exp ((a+1)*(coverNumber M S:ℝ)) := by
  let z:=keep M; let c:ℝ:=coverNumber M S; let y:=sites M; let d:=cut M
  obtain ⟨h1,h2⟩:= keep_range M
  have hz:0≤ z:=by linarith only [h1]
  have hc:0≤ c:=Nat.cast_nonneg _
  have hy:0<y:=sites_pos _
  have hd:d>0:=cut_pos _; have ht:spare M=d/2:=rfl
  change (Real.exp ((a+spare M)*c+(((S.card:ℝ)-1)*(z*γ)))) ≤ z*Real.exp ((a+1)*c)
  have hh: z*γ ≤ z*y⁻¹ := by refine mul_le_mul_of_nonneg_left ?_ hz; simpa [one_div] using ((le_div_iff₀ hy).mpr (mul_comm γ y |>.trans_le h):γ≤1/y)
  have hcard : 0 ≤ (S.card:ℝ)-1:= sub_nonneg.mpr (by exact_mod_cast Finset.card_pos.mpr hs)
  have hcard': (S.card:ℝ)-1≤c*y-1:= by linarith only [bill M S]
  have he: (c*y-1)*(z*y⁻¹)=z*c-z*y⁻¹:=by field_simp
  have hU:(a+spare M)*c+(((S.card:ℝ)-1)*(z*γ)) ≤ -(z*y⁻¹)+(a+1)*c:= by
    have hA:=mul_le_mul_of_nonneg_left hh hcard
    have H := (mul_le_mul_of_nonneg_right hcard' (show 0≤z*y⁻¹ from mul_nonneg hz (inv_nonneg.mpr hy.le))).trans_eq he
    have hu:z+spare M ≤1:=by unfold z keep spare; linarith only [cut_pos M]
    nlinarith only [hA,H, mul_le_mul_of_nonneg_right hu hc]
  refine (Real.exp_le_exp.mpr hU).trans ?_
  rw [Real.exp_add]; apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [Real.exp_neg]
  have hv:1+z*y⁻¹ ≤ Real.exp (z*y⁻¹):=by simpa only [add_comm] using (Real.add_one_le_exp (z*y⁻¹))
  have hp:0<1+z*y⁻¹:= by positivity
  apply (inv_anti₀ hp hv).trans
  rw [inv_le_iff_one_le_mul₀ hp]
  -- (1+z/y)*z= z+z^2/y ; 1-z= .25/y
  have hy':y*y⁻¹=1:=mul_inv_cancel₀ hy.ne'
  have hz'' : 1-z=y⁻¹/4:=by unfold z keep cut y; ring
  have he' : y⁻¹≥ 0:=by positivity
  have h₃:z*z≥1/4:=by nlinarith only [h1]
  nlinarith only [hz'',mul_le_mul_of_nonneg_right h₃ he']

private lemma budgeted {f:ι→ℝ}{a γ:ℝ} (_ha:0≤a)(hf:∀ i,0≤f i)(hh:Ac.Hit X M f (a+1) γ) (hy:sites M*γ≤1)(hγ:0≤γ) : ∀ (D:Finset ι) (Y:Support n),
    Ac.film X D Y (fun i=> f i * Real.exp ((a+spare M)*coverNumber M (X i))) ≤ Real.exp (Y.card*(keep M*γ)):=by
  let e i:= f i * Real.exp ((a+spare M)*coverNumber M (X i))
  let g i:= f i * Real.exp ((a+1)*coverNumber M (X i))
  let z:= keep M*γ; have hz:0≤z:=by unfold z; have := (keep_range M).1; exact mul_nonneg (by linarith) hγ
  have he i:0≤ e i:=mul_nonneg (hf i) (Real.exp_pos _).le; have hg i:0≤g i:=mul_nonneg (hf i) (Real.exp_pos _).le
  have hp:0≤keep M:=le_trans (by norm_num) (keep_range M).1
  change ∀ D Y, Ac.film _ _ _ e≤_
  intro D; induction D using Finset.strongInduction with
  | H s ih=>
    intro Y
    let B:=Ac.buds X s Y
    apply (expose X s Y e he).trans
    by_cases h:B.Nonempty
    · have h₁ : s\B ⊂ s := sdiff_ssubset (Finset.filter_subset ..) h
      calc
        _ ≤ ∑ u∈B.powerset, ∏ i∈u,keep M*g i:= by
          apply sum_le_sum; intro u hU
          have hi(i)(hi:i∈u): X i |>.Nonempty:=by
            obtain ⟨x,-,h2⟩:=((Ac.alive _ _ _).mp ((mem_powerset.mp hU) hi)).2; exact ⟨x,h2⟩
          have hx : ((root X s Y u).card:ℝ) ≤ ∑ i∈u,(((X i).card:ℝ)-1):=by
            rw [show root X s Y u=u.biUnion (fun i=> ((X i) \ Y)) from ?_]
            · refine le_trans (b:= ∑ i∈u, ((((X i) \ Y).card:ℕ):ℝ)) (by exact_mod_cast Finset.card_biUnion_le) (sum_le_sum fun i he=>?_)
              obtain ⟨x,hx',hx⟩:=((Ac.alive _ _ _).mp ((mem_powerset.mp hU) he)).2
              have hZ : ((X i) \ Y).card+1 ≤ (X i).card:= Finset.card_lt_card (show (X i \ Y) ⊂ X i from LE.le.ssubset_of_ne (sdiff_subset) (fun e => (mem_sdiff.mp (e.symm ▸ hx)).2 hx'))
              have hn : ((((X i) \ Y).card:ℕ):ℝ)+1 ≤ ((X i).card:ℝ):=by exact_mod_cast hZ
              linarith
            ext x; simp only [root, mem_sdiff, mem_biUnion]; aesop
          calc
            _ ≤ (∏ i∈u,e i)*Real.exp ((∑ i∈u,((X i).card-1:ℝ))*z):=
                 mul_le_mul_of_nonneg_left ((ih _ h₁ _).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hx hz))) (prod_nonneg fun i _=>he _)
            _ ≤ ∏ i ∈ u,keep M*g i:= by
              rw [sum_mul,Real.exp_sum,← prod_mul_distrib]; refine prod_le_prod (fun i _=> mul_nonneg (he i) (Real.exp_pos _).le) (fun i hi' => ?_)
              have hh := mul_le_mul_of_nonneg_left (pay M γ a hγ hy (X i) (hi i hi')) (hf i)
              dsimp only [e,g,z]; simpa only [Real.exp_add,mul_comm,mul_left_comm,mul_assoc] using hh
        _ ≤ _:=by
          rw [← prod_one_add]; calc
            _ ≤ ∏ i∈B,Real.exp (keep M*g i):= prod_le_prod (fun i _=>add_nonneg zero_le_one (mul_nonneg hp (hg _))) (fun i _=>by simpa only [add_comm] using (Real.add_one_le_exp (keep M*g i)))
            _ ≤ _:=by
              rw [← Real.exp_sum,← mul_sum]; exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left (Ac.demand _ _ hh Y s) hp).trans_eq (by ring))
    rw [show Ac.buds X s Y=∅ from not_nonempty_iff_eq_empty.mp h]
    simp only [powerset_empty,sum_singleton,prod_empty,sdiff_empty, one_mul]
    have hx:root X s Y ∅=∅:=by simp [root]
    have hh: Ac.pouch X s ∅={∅}:= by
      refine eq_singleton_iff_unique_mem.mpr ⟨(Ac.op ..).mpr ⟨empty_subset _,fun _ h=>False.elim (notMem_empty _ h)⟩,fun x hx=>?_⟩
      by_contra h; obtain ⟨i,hi⟩:=nonempty_iff_ne_empty.mpr h; obtain ⟨j,-,⟨x,hxU,h₂⟩,hhT⟩:=((Ac.op ..).mp hx).2 i hi; exact notMem_empty _ hxU
    rw [Ac.film,hx,hh,sum_singleton,prod_empty]; exact Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hz)

/-- Factor tree packing common to both variants. -/
private lemma fromfilm {a u:ℝ}{f:ι→ℝ}(ha:0≤a)(hf:∀ i,0≤f i)(x:Site n)
    (H:∀ s:Finset ι,Ac.film X s {x} (fun i=>f i * Real.exp (a * coverNumber M (X i))) ≤ Real.exp u) :
    SumBudget (Ac.roots X M f a x) (Real.exp u-1):= by
  let W:=Ac.roots X M f a x
  refine Push.AbsoluteSums.budget_of_sum (f:=W) (fun i=>?_) (fun I=>?_)
  · unfold W Ac.roots; split; exact mul_nonneg (Real.exp_pos _).le (prod_nonneg fun i _=>hf _); rfl
  let s:=I.biUnion id; let C:= (Ac.pouch X s {x})
  let v i:=f i * Real.exp (a * coverNumber M (X i)); let z (l:Finset ι):=l.prod v
  let I':= I.filter (fun j=> Ac.Spark X j ∧ x∈ j.biUnion X)
  have he(j:Finset ι)(hj:j∈ I)(hc:¬ j∈ I'): W j=0:= if_neg fun hh=>hc (mem_filter.mpr ⟨hj, hh⟩)
  have ht: I' ⊆ C.erase ∅:=by
    intro l hl; obtain ⟨hi,he,hk⟩:= mem_filter.mp hl
    obtain ⟨i,hz,hx⟩:= mem_biUnion.mp hk
    exact mem_erase.mpr ⟨he.1.ne_empty,(Ac.op ..).mpr ⟨fun _ hu=> mem_biUnion.mpr ⟨l,hi,hu⟩,
      fun k hj=> ⟨i,hz,⟨x,mem_singleton_self _,hx⟩,he.2 _ hz _ hj⟩⟩⟩
  calc
    _ = I'.sum W:= (sum_subset (filter_subset ..) he).symm
    _ ≤ I'.sum z:= sum_le_sum fun j hj=> by
        unfold Ac.roots; rw [if_pos (mem_filter.mp hj).2]
        simp only [v,Finset.prod_mul_distrib, ← Real.exp_sum, ← mul_sum]; rw [mul_comm]; gcongr
        · exact prod_nonneg fun i _=>hf _
        exact_mod_cast (Ac.cover X M (mem_filter.mp hj).2.1)
    _ ≤ (C.erase ∅).sum z:= sum_le_sum_of_subset_of_nonneg ht fun i _ _=> prod_nonneg fun i _=> mul_nonneg (hf _) (Real.exp_pos _).le
    _ ≤ _:= by
      apply (le_sub_iff_add_le).2
      rw [show (1:ℝ)=z ∅ from by simp [z],sum_erase_add C z ((Ac.op ..).mpr ⟨empty_subset _,fun _ h=> False.elim (notMem_empty _ h)⟩)]
      exact H _

lemma sharp {a γ:ℝ}{f:ι→ℝ}(ha:0≤a)(hf:∀ i,0≤f i)(hh: Ac.Hit X M f (a+1) γ)(hp : sites M * γ ≤1)(hG:0 ≤ γ)(x:Site n) :
    SumBudget (Ac.roots X M f (a+spare M) x) (Real.exp (keep M*γ)-1):=by
  apply fromfilm X M (add_nonneg ha (spare_pos _).le) hf x; simpa using fun s:Finset ι=> budgeted X M ha hf hh hp hG s {x}

/-- Usual exponential tree bound spent at a specified positive exponent
reserve τ (no improved factor; cheaper constant choices when bought γ
already below the actual geometry). Useful for following prehistory fusions. -/
lemma against {a τ γ:ℝ}{f:ι→ℝ}(ha:0≤a)(hf:∀ i,0≤f i)(hh: Ac.Hit X M f (a+τ) γ)(hp : sites M * γ ≤τ)(hG:0 ≤ γ)(x:Site n) :
    SumBudget (Ac.roots X M f a x) (Real.exp γ-1):=by
  let e i:= f i * Real.exp (a * coverNumber M (X i))
  have he i : 0≤e i:=mul_nonneg (hf _) (Real.exp_pos _).le
  have hi (D : Finset ι): ∀ Y,Ac.film X D Y e ≤ Real.exp ((Y.card:ℝ)*γ):= by
    let g i:= f i * Real.exp ((a+τ)* coverNumber M (X i))
    induction D using Finset.strongInduction with
    | H D h =>
      intro Y
      apply (Ac.lookup _ _ _ e he).trans
      calc
        _ ≤ ∏ i∈Ac.buds X D Y, Real.exp (g i):= by
          apply prod_le_prod
          · intro i _; unfold Ac.film; exact add_nonneg zero_le_one (mul_nonneg (he _) (sum_nonneg fun j _=>prod_nonneg fun k _=>he _))
          intro i hi; have hd := ((Ac.alive X D Y).mp hi).1
          have hh:=h _ (erase_ssubset hd) (X i)
          apply le_trans _ (Real.add_one_le_exp _)
          rw [add_comm]; gcongr
          calc
            _ ≤ e i * Real.exp ((coverNumber M (X i):ℝ) * sites M*γ):= mul_le_mul_of_nonneg_left (hh.trans (Real.exp_monotone (mul_le_mul_of_nonneg_right (bill M _) hG))) (he i)
            _ ≤ g i:= by
              unfold e g; rw [mul_assoc,← Real.exp_add]
              apply mul_le_mul_of_nonneg_left _ (hf i); apply Real.exp_monotone
              have h₂ : (0:ℝ) ≤ coverNumber M (X i) := by positivity
              nlinarith only [mul_le_mul_of_nonneg_left hp h₂]
        _ = Real.exp (∑ i∈Ac.buds X D Y,g i):= (Real.exp_sum ..).symm
        _ ≤ _:=Real.exp_monotone (Ac.demand X M hh Y D)
  apply fromfilm X M ha hf x
  intro D; simpa only [Finset.card_singleton,Nat.cast_one,one_mul] using hi D {x}
end YM.Qlocal.StellarTree
