import YM.MSbar.Wave.Merry
import YM.MSbar.Wave.Peer
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Wave
open Matrix MeasureTheory Filter Function Rolling Price Bakery Cacao Portal
open Gauge Lattice Wilson RG Tree Precision Exterior Push Push.Uniform
open scoped Topology Classical BigOperators ContDiff
variable {G:Gauge}{c:Side}{σ A:Type}[Fintype σ][DecidableEq σ]
open Set MvPolynomial
local notation "µ"=> PowerSeries.coeff
local notation "Γ" => (nhdsWithin (0:ℝ) (Set.Ioi 0))
local notation "X"=> View σ
variable (p:ℕ)
-- r-polynomial.
noncomputable def scaledT (p:ℕ) (F:PowerSeries (Pot σ))(z:ℝ × View σ) := ∑ i∈Finset.range (p+1), ∑ j∈Finset.range (i+2+1), z.1^(i+2-j)*eval z.2 (homogeneousComponent j (µ i F))
noncomputable def tariff (c:Side)(p:ℕ)(U:Clip)(R:PathData G)(F:Nesting G c) := F-PowerSeries.C (ink c U R)
lemma cool (c:Side)(p:ℕ)(U: Clip)(R: PathData G)(F:Nesting G c)(h: Expanse F 1 p) : Expanse (tariff c p U R F) 1 p:=by
   refine ⟨fun i hi=>?_⟩; unfold tariff; rw [map_sub,sub_eq_add_neg]; apply (totalDegree_add ..).trans; refine max_le (h.profile _ hi) ?_; rw [totalDegree_neg]; by_cases ht:i=0; subst i; simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_C, mul_zero,zero_add]; exact potsD ..; rw [PowerSeries.coeff_C_of_ne_zero ht]; simp
lemma scale_diff (p:ℕ)(F:PowerSeries (Pot σ)) : ContDiff ℝ ω (scaledT p F):=by unfold scaledT; exact ContDiff.sum fun i _=> ContDiff.sum fun j _=> (contDiff_fst.pow _).mul ((vent ..).comp contDiff_snd)
lemma scale_r (p:ℕ)(F:PowerSeries (Pot σ))(h: Expanse F 1 p)(x:X)(t:ℝ) : scaledT p F (t,t•x) = t^2*taste p (picture x F) t:=by
    unfold taste scaledT; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
    let v:=µ i F; let q:= Finset.range (i+2+1); have he:v.totalDegree ≤ i+2:=by simpa only [one_mul] using h.profile i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    rw [picture,PowerSeries.coeff_map,show µ i F=v from rfl]; conv_rhs=>rw [← buys (i+2) v he, _root_.map_sum, Finset.mul_sum,Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j hj=>?_); dsimp only; rw [hene ..]; -- y free
    have hh:= Finset.mem_range.mp hj
    rw [← mul_assoc,← pow_add,show i+2-j+j=i+2 from (by omega), pow_add]; ring
    exact t
variable (c':Clip)(R:PathData G)(F:PowerSeries (Pot (Primary c G)))
variable {S:ℝ → Config G c→ℝ}(ht:Trend S F R c' p)
local notation "Y"=> Positions (Primary c G)
local notation "φ₀"=> tariff c p c' R F
include ht
lemma tariff_data (x:Positions (Primary c G))(n:ℕ)(t:ℝ):taste n (picture x (tariff c p c' R F)) t=taste n (picture x F) t-height c c' R x:=by
   let F':= picture x F; let Q : PowerSeries ℝ:= PowerSeries.C (height c c' R x)
   have hx:picture x (tariff c p c' R F)= F'-Q:=by unfold picture tariff Q; rw [map_sub]; congr 1; rw [PowerSeries.map_C,inkUnder p F R c' ht x]
   rw [hx]; unfold taste; simp only [map_sub,mul_sub,Finset.sum_sub_distrib]; congr 1; rw [Finset.sum_range_succ']; simp [Q] -- blast?
variable {q q' : ℝ→Positions (Primary c G)}
lemma equivalence (hf:Price (fun _ (_:Unit)=>True) 0 (fun t _=>q t)) (hg:Price (fun _ (_:Unit)=>True) 0 (fun t _=> q' t))(h :∀ᶠ x in Γ,S x (postcard G c x (q x))= S x (postcard G c x (q' x))) :
     Grade (fun t=> taste p (picture (q t) (tariff c p c' R F)) t- taste p (picture (q' t) (tariff c p c' R F)) t) (p+1):=by
   let W:= φ₀; let f(Q:ℝ→Y)(t):= Real.log (S t (postcard G c t (Q t)))-taste p (picture (Q t) W) t
   have hp(Q)(h:Price (fun _ (_:Unit)=>True) 0 (fun t _=>Q t)):Grade (f Q) (p+1):=by
        obtain ⟨q,hq⟩:=h; have ht':∀ᶠ t in Γ,yard q t (Q t):=hq.mono fun x he=> by simpa only [pow_zero,one_mul,yard] using he () trivial
        refine (Price.inherits (V:=fun _ (_:Unit)=>True) (ht.tune q) (fun t _=> Q t) (ht'.mono fun x hh _ _=>hh)).egress (Eventually.of_forall (fun x _ _=>?_)); unfold f; rw [show taste p (picture (Q x) W) x=_ from tariff_data p c' R F ht (Q x) p x]; ring
   refine (Price.cut (hp _ hg) (hp _ hf)).egress (h.mono (fun x he _ _=>?_)); unfold f; rw [he]; unfold W; ring
end YM.MSbar.Wave
