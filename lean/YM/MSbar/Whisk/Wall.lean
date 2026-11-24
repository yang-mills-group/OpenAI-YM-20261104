import YM.MSbar.Whisk.Song
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Whisk
open Function Filter Finset Cacao
open scoped BigOperators Classical
variable {σ ι A:Type} [Fintype σ]
open Lattice MvPolynomial
local notation "P"=> Pot σ
variable {n:Side}{l : σ→ Site n}{W: Finset (Site n)} {Y Z:Finset (Site n)} {x y z:Site n}{ξ : View σ}
variable {m p q d:ℕ} {r a b t u v B :ℝ}{f g:Pot σ}{T R: List σ} {k:σ→σ→ℝ}
lemma Dorian.wet (ha:0≤a)(hp:Dorian l x a B p k b)(i j:σ): |k j i| ≤ Eve B x (l i)*b:= (le_mul_of_one_le_right (abs_nonneg _) (w_start ha p _)).trans ((single_le_sum (f:=fun j=> |k j i| * liftW a p (separation (l j) (l i))) (s:=univ) (fun i _=>mul_nonneg (abs_nonneg _) (wpos ..|>.le)) (mem_univ j)).trans (hp.lower i))
lemma power_delta (ha:0≤a)(hh:0≤B)(hc:Dorian l x a B p k b)(hp:Vault l W (a+B) p (m+2) ξ f t)(hw:y∈W): Vault l W a p m ξ (stove k f) (Eve B x y*(b*t)):=by
    have he:=hc.positive; have ht:= hp.1; refine ⟨mul_nonneg (Real.exp_pos _|>.le) (mul_nonneg he ht),fun j hj=>?_⟩; rw [stokes]
    let L:(Finset (Site n)) → ℝ→ P →ℝ:= fun z a f=> lump l z a p j ξ f; let c:= (Eve B x y)* b; have hy :0≤c:=mul_nonneg (Real.exp_pos _|>.le) he
    let I(i:σ):= pderiv (R:=ℝ) i
    let z(i₀ j₀:σ) :=k i₀ j₀/2
    have hH(i j' :σ) : |z i j'|≤ c* Eve B y (l j'):= by unfold z; rw [abs_div,abs_of_pos (by norm_num:0<(2:ℝ)),div_le_iff₀ (by norm_num)]; refine (hc.wet ha j' i).trans ((mul_le_mul_of_nonneg_right (eve_t hh x y (l j')) he).trans ?_); rw [mul_right_comm (Eve B x y)]; exact le_mul_of_one_le_right (mul_nonneg hy (Real.exp_pos _).le) one_le_two
    have hu(i j':σ) : L W a (z i j' • (I i (I j' f)))≤ c* L (insert (l i) (insert (l j') W)) (a+B) (I i (I j' f)):=by
        unfold L; rw [lump.smul]; refine le_trans (b:= c* Eve B y (l j') *lump l (insert (l i) (insert (l j') W)) a p j ξ (I i (I j' f))) ?_ ?_
        · apply mul_le_mul (hH ..) ?_ (lump.nonneg ..) (mul_nonneg hy (Real.exp_pos _).le); apply shiny; intro v _; unfold rate; refine mul_le_mul_of_nonneg_right (w_more (intr ?_) ha p) (abs_nonneg _); change zone l W v⊆zone l (insert (l i) (insert (l j') W)) v; unfold zone; gcongr; grind
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (tokenL (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)) (Finset.mem_insert_of_mem (mem_insert_self ..)) hh) hy
    refine (lump.totals ..).trans ((sum_le_sum (fun i _=> (lump.totals ..).trans (sum_le_sum (fun j _=> hu i j)))).trans ?_)
    rw [Finset.sum_comm]; simp_rw [← Finset.mul_sum]; unfold L I; rw [← mul_assoc];
    apply mul_le_mul_of_nonneg_left _ hy; have ht:=hp.2 (j+2) (by omega); rw [down] at ht; simp_rw [down _ ξ _ _ p (a+B) j] at ht; exact ht
lemma bulk_delta (ha:0≤a)(hh:0≤B)(hc:Dorian l x a B p k b)(hp:Tokew l (a+B) p (m+2) ξ f t): Vigor l x a B p m ξ (stove k f) (b*t):=⟨mul_nonneg hc.positive hp.1,fun i=>by rw [← lever]; exact power_delta ha hh hc (hp.2 i) (mem_singleton_self _)⟩
lemma stab_delta (ha:0≤a)(hc:LoopNet l a p k b)(hp:Vigor l x a B p (m+2) ξ f t): Vigor l x a B p m ξ (stove k f) (b*t):=⟨mul_nonneg hc.hope hp.1,fun i=>by rw [← lever]; exact Quote.widen (power_hp ha hc (hp.2 i)) (le_of_eq (by ring)) le_rfl⟩
lemma Tokew.smoky (hp: Tokew l a p m ξ f t)(u:ℝ): Tokew l a p m ξ (u • f) (|u| *t):= ⟨mul_nonneg (abs_nonneg _) hp.1,fun i=>by rw [Derivation.map_smul];exact Quote.mulR (hp.2 _) _⟩
lemma Vigor.smoky (hp: Vigor l x a B p m ξ f t)(u:ℝ): Vigor l x a B p m ξ (u • f) (|u| *t):= ⟨mul_nonneg (abs_nonneg _) hp.1,fun i=>by rw [Derivation.map_smul]; exact Quote.widen (Quote.mulR (hp.2 _) _) (le_of_eq (by ring)) le_rfl⟩
lemma Tokew.kit (hp: Tokew l a p m ξ f t)(hg:Tokew l a p m ξ g u):Tokew l a p m ξ (f+g) (t+u):=⟨add_nonneg hp.1 hg.1,fun i=>by rw [map_add]; exact Quote.addN (hp.2 i) (hg.2 i)⟩
lemma Vigor.kit (hp: Vigor l x a B p m ξ f t)(hg:Vigor l x a B p m ξ g u): Vigor l x a B p m ξ (f+g) (t+u):=⟨add_nonneg hp.1 hg.1,fun i=>by rw [map_add,mul_add]; exact Quote.addN (hp.2 i) (hg.2 i)⟩
lemma Tokew.total (f:ι→Pot σ)(s:Finset ι)(t:ι→ℝ)(hp:∀ i∈s,Tokew l a p m ξ (f i) (t i)): Tokew l a p m ξ (∑ i∈s,f i) (∑ i∈s,t i):=⟨sum_nonneg fun i hi=> (hp i hi).1,fun i=>by rw [_root_.map_sum]; exact Quote.total _ _ _ fun j hj=> hp j hj|>.2 i⟩
lemma Vigor.total (f:ι→Pot σ)(s:Finset ι)(t:ι→ℝ)(hp:∀ i∈s,Vigor l x a B p m ξ (f i) (t i)): Vigor l x a B p m ξ (∑ i∈s,f i) (∑ i∈s,t i):=⟨sum_nonneg fun i hi=> (hp i hi).1,fun i=>by rw [_root_.map_sum,mul_sum]; exact Quote.total _ _ _ fun j hj=> hp j hj|>.2 i⟩
-- `heavy_cov` kernel sum orientation.Net reuse.
lemma LoopNet.low (ha: a≤ B)(h:LoopNet l B p k b): LoopNet l a p k b:=by
    have he(i j : Site n) : liftW a p (separation i j)≤liftW B p (separation i j):=by unfold liftW; gcongr
    exact ⟨h.hope,fun i=> (sum_le_sum fun j _=> mul_le_mul_of_nonneg_left (he (l i) (l j)) (abs_nonneg _)).trans (h.glow i),fun i=> (sum_le_sum fun j _=>mul_le_mul_of_nonneg_left (he (l j) (l i)) (abs_nonneg _)).trans (h.forward i)⟩
lemma Tokew.quiet (x:Site n)(hp: 0≤ a) (h:Vault l {x} a p (m+1) ξ f b): Tokew l a p m ξ f b:=by
    refine ⟨h.1,fun i=> ?_⟩; have ht:=Quote.spice h i; refine ⟨h.1,fun k he=> le_trans (shiny k ?_) (ht.2 _ he)⟩; intro L HL; unfold rate; apply mul_le_mul_of_nonneg_right _ (abs_nonneg _); apply w_more _ hp; apply intr; unfold zone; gcongr;grind
end YM.MSbar.Whisk
