import YM.MSbar.Cypress.Cache
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Cypress
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice RG Tonic Aqua
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Lapaz
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal
variable {σ:Type} [Fintype σ]
local notation "V"=>PowerSeries ℝ
local notation "K"=>List σ
local notation "µ"=> PowerSeries.coeff
variable {F f h g:List σ→ℝ}{T W:List σ→PowerSeries ℝ}{p k i j:ℕ}{A ε:ℝ}
noncomputable def rayW (u:ℝ)(m:ℕ):=(1+ 2^m*(1+u))^(m+1)
noncomputable def compP (u:ℝ)(m p:ℕ):=rayW u m
lemma yarnB (f:List Bool→PowerSeries ℝ)(m p:ℕ)(h:∀ l:List Bool,l.length=m→Belt p (f l) ≤ A): Belt p (Yarn m f) ≤ 2^m*A:=by
    induction m generalizing f with
    | zero => exact (h [] rfl).trans (le_of_eq (by ring))
    | succ m ih=> rw [twilled]; refine (Belt_sumP ..).trans ((sum_le_sum (fun i _=> ih (fun j=> f (i::j)) (fun j hj=> h _ (by simp [hj])))).trans ?_); rw [sum_const,card_univ,nsmul_eq_mul]; simp;ring_nf; apply le_refl
variable (L:List σ)(H:Locks F f T W h g) (hx:0 ≤ A)
variable (hp : ∀ v:List σ,v⊆L→v.length≤ k→ v≠[] → Belt p (W v) ≤ A)
include H hx hp
noncomputable def cornP (u:ℝ)(m k:ℕ):= (1+2^k*u)^m
local notation "p!"=> cornP A
lemma Fstill (v:List σ)(hu:v⊆L)(ht:v.length≤ k) : Belt p (T v) ≤ (cornP A v.length k):=by
     by_cases hh:v=[]; · subst v; rw [H.p0,Belt_z]; rfl
     let i:=v.getLast hh; let R:=v.dropLast; have hz:v= R++ [i]:=(List.dropLast_append_getLast ..).symm
     have he : R.length+1=v.length:=by nth_rw 1 [hz]; simp -- occ
     have hK:1≤1+(2:ℝ)^k*A := le_add_of_nonneg_right (by positivity)
     let c:=cornP A R.length k; rw [hz,H.book]; refine (yarnB _ R.length p (A:=c*A) (fun u hi=>?_)).trans ?_
     · let y:=takeout false u R++ [i]; let x:=takeout true u R; have h₁:x.length ≤ R.length:=(sunset true u R hi).trans_le ((part_le ..).trans_eq hi); have h₂:y.length≤ v.length:=by have hz':(takeout false u R).length≤ R.length:=(sunset false u R hi).trans_le ((part_le ..).trans_eq hi); unfold y; rw [List.length_append]; change _ +1 ≤ _; omega
       have hu1:R++[i]⊆L:=hz ▸ hu -- suspicious dependant
       have hY:y⊆L:= List.Subset.trans (show y ⊆ R++[i] from (by unfold y; grind [Bout.narrow])) hu1; have hX : x⊆L := List.Subset.trans (List.Subset.trans (Bout.narrow ..) (show R⊆R++[i] from by simp)) hu1; have hx' : Belt p (T x)≤c:=(Fstill x hX (by omega)).trans (pow_le_pow_right₀ hK h₁)
       exact (Belt_product ..).trans (mul_le_mul hx' (hp y hY (h₂.trans ht) (by simp [y])) (Belt_pos ..) (show 0≤ c from zero_le_one.trans (one_le_pow₀ hK)))
     simp only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add]; unfold cornP; rw [pow_succ]
     have hP:(2:ℝ)^R.length*A ≤ 2^k*A:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (by omega)) hx; have hp:0≤c:= zero_le_one.trans (one_le_pow₀ hK); apply le_trans (le_of_eq _) (mul_le_mul_of_nonneg_left (hP.trans (le_add_of_nonneg_left zero_le_one)) hp); ring
termination_by v.length
decreasing_by change x.length < v.length; omega
noncomputable def scratch (u:ℝ)(k:ℕ)(ε:ℝ) (m:ℕ):=match m with|0=>0|r+1=> scratch u k ε r+2^k*(scratch u k ε r*u+cornP u k k* ε)
variable (hε: 0≤ ε)(hg:∀ v:List σ,v⊆L→v.length≤ k→v≠[]→ |g v|≤ ε)
include hε hg
lemma scratchy (m:ℕ) : 0 ≤ scratch A k ε m∧∀ v:List σ,v⊆L→v.length  ≤ k→ v.length ≤ m→ |h v|≤ scratch A k ε m := by
     induction m with
     | zero=> exact ⟨le_rfl,fun v hu hm hq=> by rw [List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hq), H.v0,abs_zero];rfl⟩
     | succ m ih=>
          let p':ℝ:= p! k k; have hK:1≤1+(2:ℝ)^k*A := le_add_of_nonneg_right (by positivity); have hh:0 ≤ p':=zero_le_one.trans (one_le_pow₀ hK); let y:=scratch A k ε m; let z:= y*A+p'*ε; have hy:0≤ y:=ih.1; have hz:0 ≤ z:=by unfold z; positivity
          rw [scratch]; have hp' : y≤ y+2^k*z:=le_add_of_nonneg_right (by positivity); refine ⟨hy.trans hp',fun v hv hm hs=>?_⟩
          by_cases he:v.length ≤ m; exact (ih.2 v hv hm he).trans hp'; obtain ⟨R,i,hk⟩: ∃ R:List σ,∃ i,v= R++[i]:=⟨v.dropLast,v.getLast (by rintro hz; simp only [hz,List.length_nil,zero_le,not_true_eq_false] at he), (List.dropLast_append_getLast ..).symm⟩
          have hr : R.length+1=v.length:=by rw [hk];simp
          rw [hk,H.mark]; refine (polished ..).trans ((shiny _ (g:=fun _=>z) (fun T' hh'=>?_)).trans ?_)
          · let v':=takeout true T' R; let R':=takeout false T' R++[i]; have hv:R++[i]⊆L:=hk ▸ hv; have he:v'.length ≤ R.length:=(sunset true T' R hh').trans_le ((part_le ..).trans_eq hh'); have ht: R'.length≤ v.length:=by have he':(takeout false T' R).length≤ R.length:=(sunset false T' R hh').trans_le ((part_le ..).trans_eq hh'); unfold R'; rw [List.length_append];change _+1 ≤ _; omega
            have hR:R'⊆L:= List.Subset.trans (by unfold R'; grind [Bout.narrow]) hv; have h₀:v'⊆ L:= List.Subset.trans (List.Subset.trans (Bout.narrow ..) (by simp)) hv; have h₁:R'≠[]:=by simp [R']; -- bounds
            let u:=T v'; have hU:Belt p u ≤ p':=(Fstill L H hx hp v' h₀ (by omega)).trans (pow_le_pow_right₀ hK (show v'.length ≤ k by omega)); have hT:= Belt_entry (W R') p 0 (Nat.zero_le _);
            exact (abs_add_le ..).trans (add_le_add ((abs_mul ..).trans_le (mul_le_mul (ih.2 v' h₀ (by omega) (by omega)) (hT.trans (hp R' hR (ht.trans hm) h₁)) (abs_nonneg _) hy)) ((abs_mul ..).trans_le (mul_le_mul ((Belt_entry u p 0 (Nat.zero_le p)).trans hU) (hg _ hR (ht.trans hm) h₁) (abs_nonneg _) hh)))
          rw [total_books,Fintype.card_bool,Nat.cast_ofNat]; exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two (show R.length ≤ k from by omega)) hz).trans (le_add_of_nonneg_left hy)
end YM.MSbar.Cypress
