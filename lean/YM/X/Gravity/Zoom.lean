import YM.X.Gravity.Blade
/-!
# κ variation graded on the actual probe coefficients. Probe-Taylor vs scaling tower. release of nonphysical point contacts.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Gravity
open Lattice Wilson Next.Rank Normal Interval PertExtension LatticePT Filter Set Function Metric MeasureTheory Asymptotics Reed Size Braid
open MvPolynomial Hinge Clove Haze Grow Shelf Ocean Fielding Crystal Perch LiftMark
open Stems hiding X
open scoped Topology ContDiff BigOperators Classical
variable {q: ℕ+}(hq:1<q.val){V:Type*}{k m n d l:ℕ}{G:Gauge}{R r:ℝ}
local notation "X"=>MvPolynomial.X
local notation "K"=>Book G
local notation "g"=>vapor G
variable (A: Okay G k)
lemma part_cost (f:Valves G)(h:g f≠k+1): inkB (stepP A) f=0:= by unfold inkB stepP; rw [Pi.single_eq_of_ne (show f.1≠k from by change f.fst+1≠_ at h;omega) _,map_zero,Complex.ofReal_zero]
lemma jet_torch (a:ℂ)(p:Book G): testP A (Perch.jets (vapor G) a p)=a^(k+1) • Perch.jets (vapor G) a (testP A p):= by
   let c := testP A; let P:= Perch.jets (vapor G) a; induction p using MvPolynomial.induction_on with
   | C x=>simp [Perch.jets,testP,torch]
   | add a b x y=> simp_rw [map_add,smul_add,x,y]
   | mul_X p i h=>
      have he(i:Valves G):c (P (X i)) = a^(k+1) • P (c (X i)):= by
         let f:= inkB (stepP A); have hx (j:Valves G): c (X j)= C (f j):= slit_X f j
         have hg (z:ℂ)(p:Book G): P (C z)=C z:= P.commutes z
         rw [hx,show P (X i)= C (a^g i)* X i from by simp [P,Perch.jets], hg _ p]; by_cases hp:g i=k+1
         · rw [C_mul',Derivation.map_smul,hx,hp]
         rw [C_mul',Derivation.map_smul,hx, show f i=0 from part_cost A i hp,map_zero,smul_zero,smul_zero]
      change c (P (p*X i)) = a^(k+1) • P (c (p* X i)); rw [map_mul, c.leibniz,c.leibniz]; rw [map_add, smul_add]; change P p* _ + P (X i)* c (P p) = _ • P (p*c (X i)) + _ • P (X i*c p); rw [map_mul,map_mul,he, show c (P p)= _ from h]; exact congr_arg₂ HAdd.hAdd (mul_smul_comm ..) (mul_smul_comm ..) -- h typed test
lemma pay_coeff (p:Book G)(h:IsWeightedHomogeneous (vapor G) p n)(i:Valves G→₀ℕ)(ht:coeff i (testP A p)≠0): n=k+1+ Finsupp.weight g i:= by
    let x:= coeff i (testP A p); let b:= Finsupp.weight g i
    have he:= congr_arg (coeff i) (jet_torch A ((2:ℝ):ℂ) p); rw [heel g _ _ h,Derivation.map_smul] at he; simp only [coeff_smul,smul_eq_mul,jets_coeff] at he
    have hv : (2:ℝ)^n=(2:ℝ)^(k+1+b):= Complex.ofReal_injective (by rw [Complex.ofReal_pow,Complex.ofReal_pow]; apply mul_right_cancel₀ ht; rw [pow_add,mul_assoc]; exact he)
    exact (StrictMono.injective (strictMono_nat_of_lt_succ (f:=fun i:ℕ=>(2:ℝ)^i) (fun i=> by rw [pow_succ]; linarith [show 0<(2:ℝ)^i from by positivity]))) hv
lemma post_zero (p:Book G)(h:IsWeightedHomogeneous g p n)(hp:n≤k):testP A p=0:= by ext i; rw [coeff_zero]; by_contra hi;have:=pay_coeff A p h i hi; omega
lemma post_degree (p:Book G)(h:IsWeightedHomogeneous g p n)(hp:k < n): IsWeightedHomogeneous (vapor G) (testP A p) (n - (k+1)):= fun {i} hi=> by have:= pay_coeff A p h i hi; omega
lemma post_leaf (p:Book G): leaf g l (testP A p)=testP A (leaf g (l+(k+1)) p):= by
    induction p using MvPolynomial.induction_on' with
    | add a b x y=> simp only [leaf] at *; simp_rw [map_add,x,y]
    | monomial i b=>
       let p:= (MvPolynomial.monomial i b:Book G); let n:= Finsupp.weight g i; have hp : IsWeightedHomogeneous (vapor G) p n:= isWeightedHomogeneous_monomial g i b rfl -- check
       change leaf g l (testP A p)=testP A (leaf _ (l+(k+1)) p); unfold leaf
       by_cases h:l+(k+1)=n;
       · rw [h,hp.weightedHomogeneousComponent_same]; exact (show IsWeightedHomogeneous g (testP A p) l from (show n-(k+1)=l by omega) ▸ (post_degree A p hp (by omega))).weightedHomogeneousComponent_same
       rw [hp.weightedHomogeneousComponent_ne _ h,map_zero]; by_cases hv:k<n; · exact (post_degree A p hp hv).weightedHomogeneousComponent_ne l (by omega)
       rw [post_zero A p hp (not_lt.mp hv), map_zero]
lemma step_arm (h:k<d): arm d (stepP A) = raised (Reed.phase A):= by
   rw [arm_point,Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr h)]; · rw [← lif, show stepP A k=A-rightCur k A from Pi.single_eq_same ..,show valP k (A-rightCur k A)=_ from map_sub (valP k) A _, poles];
   intro b _ hb; rw [show stepP A b=(0:Okay G b) from Pi.single_eq_of_ne hb _,←lif,map_zero]
lemma sound_arm (x:Long G)(d:ℕ)(p: Curly G):probeL x (trumpet (Okay G) (valP (G:=G)) d p)=snap (arm d x) p:=by rw [tone]; simp_rw [lif, arm_point]
lemma step_record (h:k<d)(p:Curly G): testP A (trumpet (Okay G) (valP (G:=G)) d p)= trumpet (Okay G) valP d (stroke (raised (phase A)) p):= by
   apply probe_ext; intro x; let v:= stepP A;
   have he:= candles x (stepP A) (trumpet (Okay G) (valP (G:=G)) d p) 0; rw [zero_smul,add_zero] at he; simp_rw [sound_arm,map_add,map_smul,step_arm A h] at he;
   rw [sound_arm]; exact he.unique (slit_line ..)
end YM.PositionX.Gravity
