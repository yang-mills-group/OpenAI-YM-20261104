import YM.MSbar.Tonic.PriceR
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Tonic
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge}{c f:Side}{S:StepData c f}
local notation "J"=> Positions (Primary c G)
local notation "X"=> Primary c G
local notation "Q"=> Config G f
variable (β t:ℝ)(U:Config G f)(M:Config G c)(v:S.Choices)
local notation "B₀"=> tribe S β t U v
local notation "Φ"=> wing S U v
variable (x:Positions (Primary c G))(L:List (Primary c G))(i j:Primary c G)(e:Bond c)
-- normalised response.Pl.Ψ. costs.
lemma dock : buoy (tribe S β t U v) x (L++[i])= -β*S.kernel.penalty *buoy (rowS G 1 t (rope i) (wing S U v (rope i))) x (L++[i]):=by
   let f(d):=rowS G 1 t d (wing S U v d); let p:=L++[i]; let L':=p.map (@bolt X); have hp(d:Bond c):ContDiffAt ℝ L'.length (f d) x:= (((stage_Row ..).comp (f:=fun z:J=>(z,(wing S U v d))) (contDiff_id.prodMk contDiff_const)).of_le le_top).contDiffAt; unfold buoy; rw [lines]; unfold plateV; rw [Lis.wed L'.length L' (-β*S.kernel.penalty) (fun x=>∑ d:Bond c, f d x) (ContDiffAt.sum fun i _=> hp i) le_rfl,Lis.tot L'.length L' univ f (fun i _=>hp i) le_rfl,sum_eq_single_of_mem (rope i) (mem_univ _)]; exact fun j _ hz=> rung t x j (Φ j) L i hz
lemma lonely : strap S β t v x [] U=1:=by unfold strap; change _/_=1; exact div_self (Real.exp_pos _).ne'
variable (A:Config G f)(z:S.Choices)
lemma joins (T:List X)(h: T.Sublist (L++[i])) : T⊆ L++[i]:=h.subset -- remove
lemma weave (m:ℕ)(hk:L.length=m)(h:∀ i∈ L, S.prediction A z (rope i)= S.prediction U v (rope i)) : strap S β t v x L U= strap S β t z x L A:=by
    induction m using Nat.strong_induction_on generalizing L with
    | h m ih=>
       rcases List.eq_nil_or_concat' L with ha|⟨L,b,rfl⟩
       · subst ha; rw [lonely,lonely]
       rw [List.length_append] at hk; rw [twig β t U v x, twig β t A z x]; apply stitch; intro x' ht; have hp : List.Sublist (takeout true x' L) L:=by
           have hx(L:List X)(x:List Bool): List.Sublist (takeout true x L) L:=by induction L generalizing x with|nil=> cases x <;> rfl|cons i L ih=> cases x with|nil=> simp [takeout]|cons b x=> rw [takeout]; split; exact (ih _).cons_cons _; exact (ih _).cons _
           exact hx ..
       refine congr_arg₂ (·*·) ?_ ?_; · exact ih _ (show (takeout true x' L).length < m by rw [sunset _ _ _ ht]; have h:= part_le true x'; simp only [List.length_cons,List.length_nil] at hk;omega) _ rfl (fun i hi=> h i (List.mem_append_left _ (hp.subset hi)))
       rw [dock,dock,wing,wing,h b (by simp)]
variable {n:ℕ}{K:ℝ}
def glow (u:KernelChoices)(p:ℕ)(β K:ℝ) (G:Gauge):= |β| *|u.penalty| *(K*shade G^p)
def sizeP (m:ℕ)(q:ℝ):= ((1+q)*2^m)^m
lemma glowB (T:KernelChoices) (G:Gauge)(he:0≤ K):0≤ glow T n β K G:=by have h:= shade_pos G; unfold glow; positivity
lemma price_u (h:PriceR G n K)(hp: |t| ≤1)(hl:L.length≤n)(hh:shade G*|t| *‖x‖≤1): |strap S β t v x L U| ≤ sizeP L.length (glow S.kernel n β K G) :=by
     let Q':=glow S.kernel n β K G; have hV :0 ≤ Q':=glowB β _ G h.pos
     suffices hx : ∀ k:ℕ,∀ L':List X,L'.length=k→k ≤ n →|strap S β t v x L' U| ≤ sizeP k Q' by exact hx _ L rfl hl
     intro k; induction k using Nat.strong_induction_on with
     | h j ih=>
        intro T he hT; cases j with
        | zero => rw [List.length_eq_zero_iff.mp he,sizeP,pow_zero,lonely,abs_one]
        | succ j=> obtain ⟨T,i,rfl⟩:∃ t' v', T=t' ++ [v']:= (List.eq_nil_or_concat' T).resolve_left (List.length_pos_iff.mp (he.symm ▸ Nat.zero_lt_succ j)) -- edit
                   have he:T.length=j:=by simpa using he
                   rw [twig β t U v x T i,he]; apply (polished _ _).trans; let K':= (1+Q')*2^(j+1); have hK:1 ≤ K':=one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right hV) (by exact one_le_pow₀ one_le_two); apply le_trans (b:=Yarn j (fun _:List Bool=> K'^j*(1+Q'))) (shiny _ ?_)
                   · rw [total_books]; simp only [Fintype.card_bool,Nat.cast_ofNat,sizeP]; change (2:ℝ)^j* _≤ K'^_; rw [pow_succ K' j]; exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (Nat.le_succ j)) (mul_nonneg (pow_nonneg (zero_le_one.trans hK) _) (show 0 ≤ 1+Q' from by positivity))).trans_eq (by change (2:ℝ)^(j+1)*(K'^j*_) = K'^j*K'; unfold K'; ring)
                   intro z hx; rw [abs_mul]; -- z shadow. t checks
                   let f:=takeout true z T; let g:=takeout false z T
                   have hz(b): (takeout b z T).length≤j:=(sunset _ _ _ (by omega)).trans_le (part_le ..|>.trans_eq hx)
                   let w:=f.length; have hx':=ih f.length (Nat.lt_succ_iff.mpr (hz true)) f rfl (by unfold f; have hv:=hz true; omega) -- output
                   refine mul_le_mul (hx'.trans ?_) ?_ (abs_nonneg _) (zero_le_one.trans (one_le_pow₀ hK))
                   · unfold sizeP; exact (pow_le_pow_left₀ (by positivity:0≤ (1+Q')*2^f.length) (show _≤K' from mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_two (show f.length ≤ j+1 from (hz true).trans (Nat.le_succ j))) (by positivity)) f.length).trans (pow_le_pow_right₀ hK (hz true))
                   rw [dock, abs_mul,abs_mul,abs_neg]; refine le_trans ?_ (le_add_of_nonneg_left zero_le_one); exact mul_le_mul_of_nonneg_left (rowPrice t x _ h hp hh (show g.length < n from lt_of_le_of_lt (hz false) hT) (rope i) _ i) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
end YM.MSbar.Tonic
