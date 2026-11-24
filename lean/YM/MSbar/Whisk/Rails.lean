import YM.MSbar.Whisk.Circuit
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Whisk
open Function Filter Finset Cacao
open scoped BigOperators Classical
variable {σ ι A:Type} [Fintype σ]
open Lattice MvPolynomial
local notation "P"=> Pot σ
variable {n:Side}{l : σ→ Site n}{W: Finset (Site n)} {Y Z:Finset (Site n)} {x y z:Site n}{ξ : View σ}
variable {m p q d:ℕ} {r a b t u v:ℝ}{f g:Pot σ}{T R: List σ} {k:σ→σ→ℝ}
noncomputable def Tokew (l:σ→ Site n)(a:ℝ)(p m:ℕ)(ξ:View σ)(f:Pot σ)(b:ℝ): Prop:=0≤ b∧∀ i:σ, Vault l {l i} a p m ξ ((pderiv i) f) b
noncomputable def juncture (k:σ→σ→ℝ)(f g : P): P:=∑ i:σ,∑ j:σ,k i j • ((pderiv i f)*(pderiv j g))
set_option quotPrecheck false
lemma reversal (k:σ→σ→ℝ)(f g:P): juncture k f g=juncture (fun i j=>k j i) g f:=by
   unfold juncture; rw [sum_comm]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=> congr_arg _ (mul_comm ..)
lemma replaces (k:σ→σ→ℝ)(i:σ)(f g:P): (pderiv i) (juncture k f g)=juncture k ((pderiv i) f) g+juncture k f ((pderiv i) g):=by
    unfold juncture; simp_rw [_root_.map_sum,Derivation.map_smul,← sum_add_distrib]
    apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl; intro j _; rw [pderiv_mul,smul_add,seasoning i c,seasoning i j]
lemma down (l:σ→Site n)(ξ:View σ)(f:P)(W:Finset (Site n))(p:ℕ)(a:ℝ)(m:ℕ) : lump l W a p (m+1) ξ f=∑ i:σ,lump l (insert (l i) W) a p m ξ ((pderiv i) f):=by
   unfold lump;rw [twilled]; refine sum_congr rfl fun i _=> stitch _ ?_; intro j he; change rate l _ _ _ _ _ _ = rate ..; unfold rate; rw [moss,read_next]
-- use both gradient and ground techniques
lemma jumble (ha:0≤ a)(hc:LoopNet l a p k b)(hp:Vault l W a p (m+1) ξ f t)(hq : Tokew l a p m ξ g u): Vault l W a p m ξ (juncture k f g) (2^m*(t*(b*u))):=by
    have ht:=hp.1; have he:=hq.1; have hH:=hc.hope
    refine ⟨by positivity,fun j hj=>?_⟩
    let s (i)(v:σ):=liftW a p (separation (l i) (l v))
    let L(i:σ)(k:ℕ):= lump l (insert (l i) W) a p k ξ ((pderiv i) f); have h₀(i k): 0≤ L i k:=lump.nonneg ..
    have hK(k)(he:k≤m): ∑ i:σ,L i k ≤ t:=by unfold L;rw [← down];exact hp.2 _ (Nat.add_le_add_right he _)
    have hT(i b) (he: b≤m): lump l {l i} a p b ξ ((pderiv i) g) ≤ u:= hq.2 i|>.2 _ he
    let R(i i'): P:= k i i' • ((pderiv i) f *(pderiv i') g)
    let q(i i') := Yarn j (fun A:List Bool=> |k i i'| *s i i'*L i (parts true A)*u)
    have hx(i i'): lump l W a p j ξ (R i i') ≤ q i i':=by
       have hh := wired l W ξ (Y:=insert (l i) W) (Z:={l i'}) (f:=(pderiv i) f) (g:=(pderiv i') g) (p:=p) (m:=j) ha (Subset.trans (Finset.subset_insert ..) subset_union_left) (mem_insert_self ..) (mem_singleton_self _)
       unfold R q; rw [lump.smul]; refine (mul_le_mul_of_nonneg_left hh (abs_nonneg _)).trans ?_; rw [← mul_assoc,← sheen]; apply shiny; intro i'' h
       let i0:= parts false i''; let v:= parts true i''; change _* (L i v *_)≤_
       have hx:i0 ≤ m:= (part_le ..).trans (h.trans_le hj)
       apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hT i' i0 hx) (h₀ i _)) (mul_nonneg (abs_nonneg _) (wpos ..|>.le))) (le_of_eq _); ring
    have hp(i): ∑ j:σ,q i j ≤Yarn j (fun A:List Bool=> L i (parts true A)*(b*u)):=by
       unfold q; rw [←scarves]; apply shiny; intro A hA; let y:=L i (parts true A); rw [← sum_mul,←sum_mul]; exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hc.glow i) (h₀ i _)) he).trans_eq (by ring)
    refine (lump.totals l W ξ _ _).trans ((sum_le_sum (fun i (_:i∈(Finset.univ:Finset σ))=>(lump.totals ..).trans ((sum_le_sum fun v _=> hx i v).trans (hp i)))).trans ?_)
    -- LHS ∑ i∥; inferred defin issue
    rw [←scarves]; refine (shiny (ι:=Bool) j (g:=fun _=>t*(b*u)) (fun i hi=> ?_)).trans ?_
    · rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right (hK _ ((part_le ..).trans (hi.trans_le hj))) (mul_nonneg hc.hope he)
    rw [total_books]; rw [Fintype.card_bool]; push_cast; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two hj) (mul_nonneg ht (mul_nonneg hc.hope he))
lemma union_bulk (ha:0≤a)(hc:LoopNet l a p k b)(hp: Tokew l a p (m+1) ξ f t)(hq: Tokew l a p (m+1) ξ g u): Tokew l a p m ξ (juncture k f g) ((2*2^m)*(t*(b*u))):=by
    have hh:= hc.hope; have hV:=hp.1; have hg:=hq.1
    refine ⟨by positivity,fun i=>?_⟩; have hy : Tokew l a p m ξ g u:=⟨hq.1,fun i=> Quote.widen (hq.2 i) le_rfl (by omega)⟩; have hk : Tokew l a p m ξ f t:=⟨hp.1,fun i=> Quote.widen (hp.2 i) le_rfl (by omega)⟩
    rw [replaces,reversal k f ((pderiv i) g)]; refine (Quote.widen (Quote.addN (jumble ha hc (hp.2 i) hy) (jumble ha hc.loom (hq.2 i) hk)) (le_of_eq (by ring)) le_rfl)
lemma power_hp (ha:0≤a)(hc:LoopNet l a p k b)(hp:Vault l W a p (m+2) ξ f t): Vault l W a p m ξ (stove k f) (b*t):=by
    have he:=hc.hope; have hh:= hp.1; refine ⟨mul_nonneg he hh,fun j hj=>?_⟩; rw [stokes]
    let L:(Finset (Site n)) →P →ℝ:= fun z f=> lump l z a p j ξ f
    let I(i:σ):= pderiv (R:=ℝ) i
    let z(i₀ j₀:σ) :=k i₀ j₀/2
    have hy(i j' :σ) : |z i j'|≤ b:= by unfold z; rw [abs_div,abs_of_pos (by norm_num:0<(2:ℝ)),div_le_iff₀ (by norm_num)]; linarith only [hc.single ha i j',he] -- order
    have hu(i j':σ) : L W (z i j' • (I i (I j' f)))≤b* L (insert (l i) (insert (l j') W)) (I i (I j' f)):=by
        unfold L; rw [lump.smul]; apply mul_le_mul (hy ..) ?_ (lump.nonneg ..) he; apply shiny; intro v _; unfold rate; refine mul_le_mul_of_nonneg_right (w_more (intr ?_) ha p) (abs_nonneg _); change zone l W v⊆zone l (insert (l i) (insert (l j') W)) v; unfold zone; gcongr; grind
    refine (lump.totals ..).trans ((sum_le_sum (fun i _=> (lump.totals ..).trans (sum_le_sum (fun j _=> hu i j)))).trans ?_)
    rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]; unfold L I; conv_rhs => skip
    apply mul_le_mul_of_nonneg_left _ he; have ht:=hp.2 (j+2) (by omega); rw [down] at ht; simp_rw [down _ ξ _ _ p a j] at ht; exact ht
lemma depthUp (ha:0≤a)(hc:LoopNet l a p k b)(hp:Tokew l a p (m+2) ξ f t): Tokew l a p m ξ (stove k f) (b*t):=⟨mul_nonneg hc.hope hp.1,fun i=>by rw [← lever]; exact power_hp ha hc (hp.2 i)⟩
end YM.MSbar.Whisk
