import YM.MSbar.RawP.Whir
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.RawP
open Function Filter Whisk Lis Measuring Cacao Aqua Push Uniform Lattice RG
open Precision Gauge Midpoint Rolling Exterior Wilson Wave Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open AnalyticBridge.SectorAffine.Offset
variable {G:Gauge}{n:Side}{σ E ι:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Fintype σ]
open AnalyticBridge.SectorAffine Metric Pressure
variable {G:Gauge}{n:Side}
variable {p:ℕ}{a b C K r:ℝ}
local notation "W"=> Positions (Primary n G)
local notation "ℓ"=>Measuring.chart n G
variable {Z B:ℝ}{k:ℕ}{c:Clip}{R:PathData G} (s:Signed)(q:Face (Per n))(b':Site n)
variable {S:Set (Positions (Primary n G))}{x:Positions (Primary n G)}
def Wind (G:Gauge)(a Z:ℝ)(p:ℕ): Prop:=0 ≤ Z∧∀ n:Side, ∀ i:Slot,∀ s:Signed,∀ b:Site n,∀ x:Positions (Primary n G), ‖x‖≤1 → Allows p (fun x=> i.atSite (sparkP s x) b) x (Z*Real.exp (a*i.length))
variable (h:Wind G a Z p) (hs:‖x‖<1)
local notation "U"=> sparkP (n:=n) (G:=G) s
local notation "ψ"=>Measuring.chart n G
include h hs
open Work.G05
lemma atom_R (A:Atom G k) : Requests Set.univ (fun x:W=> A.unmasked (U x) b') (Measuring.chart n G) (affine s 0 b') (2*A.length+1) :=by
    intro i hi j hj hc; apply congr_arg A.poly; apply funext; intro y; apply supplyR s (A.leg y) b' _ hi _ hj; intro v hz; have hh:(A.leg y).length ≤ A.length:= Finset.single_le_sum (f:=fun i=>(A.leg i).length) (fun _ _=> Nat.zero_le _) (Finset.mem_univ _); apply hc; omega
lemma atom_H (A:Atom G k) : Allows p (fun x:W=> A.unmasked (U x) b') x ((2^p*Z)^k*A.budget a):= by
    let X(i:Fin k):=Real.exp (a*(A.leg i).length); let Y:= ∏ i, ((2:ℝ)^p* (Z*X i)); let b(i:Fin k)(d:G.ColorIndex)(x:W):= (A.leg i).atSite (U x) b' d
    have hX(i:Fin k)(d:G.ColorIndex) : Allows p (b i d) x (Z*X i):=by
        let L:= EuclideanSpace.proj (𝕜:=ℝ) d; have hh:‖L‖ ≤ 1:=by apply L.opNorm_le_bound zero_le_one; exact fun v=> (by rw [one_mul]; exact PiLp.norm_apply_le v d)
        have hh:= (h.2 _ (A.leg i) s b' x hs.le).linear L hh; rw [one_mul] at hh; exact hh
    have hp(i:Fin k→G.ColorIndex)(t:Finset (Fin k)): Allows p (fun x=>∏ j∈t,b j (i j) x) x (∏ j∈t, ((2:ℝ)^p*(Z*X j))):=by
        induction t using Finset.induction_on with
        | empty=> simp_rw [prod_empty]; exact allows_const _ (by rw [norm_one])
        | insert a t he ih=>
            simp_rw [prod_insert he]; have h':= (hX a (i a)).bilinear _ ih (ContinuousLinearMap.opNorm_mul_le ℝ ℝ); simp only [mul_one,ContinuousLinearMap.mul_apply'] at h'; exact h'
    let f(t:Fin k→G.ColorIndex)(x:W):= A.coeff t*∏ j,b j (t j) x; have hh(t:Fin k→G.ColorIndex): Allows p (f t) x (|A.coeff t| *Y):=(hp t univ).smul (A.coeff t)
    refine (allows_sum (s:=Finset.univ) (fun i _=>hh i)).mono (le_of_eq ?_); unfold Y X Atom.budget Atom.magnitude Atom.length; rw [← Finset.sum_mul]; simp_rw [prod_mul_distrib]; rw [prod_const,prod_const]; simp only [card_univ,Fintype.card_fin]; rw [← Real.exp_sum,← Finset.mul_sum,Nat.cast_sum]; ring
variable {A:ℕ→Atom G k} (hv: SumBudget (fun i=> (A i).budget (a+2*b*p)) C)(hb:0≤ b)
include hv hb
local notation "Q"=> (2^p*Z)^k
lemma cap (i:ℕ) : Q*(A i).budget a ≤ Q * (A i).budget (a+2*b*p) :=by have hh:=h.1; unfold Atom.budget Atom.magnitude; gcongr <;> first|positivity|simp <;> positivity
local notation "D"=> Real.exp (b*p)
lemma tents : let F(y:W):=∑' i,(A i).unmasked (U y) b'
              Through p F x (Q*C) ∧ Beacon (Measuring.chart n G) b p F (affine s 0 b') x (Q*C*Real.exp (b*p)):=by
    let t(i):=(A i).budget (a+2*b*p); let f(i)(x:W):= (A i).unmasked (U x) b'; let g:= affine s 0 b'; let B₀:= ball (0:W) 1
    have hx(z): z∈ B₀ ↔ ‖z‖<1:=by simp [B₀]
    have hX:=hx x|>.mpr hs; have hp:=hv.2.1.mul_left (Q); have h₀:0 ≤ Z:= h.1
    have hg(i:ℕ)(x:W)(hz:x∈B₀): Through p (f i) x (Q*t i):=Through.control ((atom_H s b' h ((hx x).mp hz) (A i)).mono (cap h hs hv hb i)); intro F; have hB: (∑' i,Q*t i)≤ Q*C:=by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hv.2.2 (by positivity)
    refine ⟨(topS isOpen_ball (convex_ball ..) hg hp x hX).mono hB,?_⟩
    let c(i):= Q*t i*D; have ht(i:ℕ): Beacon (Measuring.chart n G) b p (f i) g x (c i) := by
         refine ((atom_H s b' h hs (A i)).beacon (atom_R s b' h hs (A i)) Filter.univ_mem hb).mono (le_of_eq ?_); unfold c t Atom.budget; push_cast; rw [mul_assoc, mul_assoc, ←Real.exp_add, mul_assoc, mul_assoc,← Real.exp_add]; congr 3 <;> ring -- test
    refine Beacon.mono (cargo f (fun i=>Q*t i) c isOpen_ball (convex_ball ..) hg hX hp (hp.mul_right _) ht) ?_; unfold c; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hB (Real.exp_pos _|>.le)
end YM.MSbar.RawP
