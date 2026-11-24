import YM.FVA2.Press.Stagger
/-!
# Fits at survey channels on true MS full ray stencils
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Press.Integration
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Labels Source Source.Drops Bid Work XSpace
open MS MS.Koszul MS.Momentum MS.Landau MS.Plane MS.Plane.Wire MS.Tone MS.Cylinder Lab MS.Native MS.Native.Sew MS.Theater MS.Local.Physical MS.Lifting
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge} {k d:ℕ} {H:Hol G} (A:XSpace.Survey G H d)
local notation "E" => tilt A
local notation "T" => Local A
local notation "C" => G.Color
local notation "X" => Edge Cover
local notation "P" => QP
local notation "U" => G.ColorIndex
local notation "V" => Dot G Cover
local notation "Ω" => Branch G Axis
local notation "ζ" => Subtype.val (p:=fun x:X=>x∈ knots A)
variable (i:Axis)(u:G.ColorIndex)(t:QP)(g:tilt A→ℝ)
local notation "I" => Complex.I
local notation "K" => fderiv ℝ g 0
private lemma rayExpr (x:ℂ)(q:ℝ) (k:ℕ) : iteratedDeriv k (fun p:ℝ=>Complex.exp (x*p)) q=x^k*Complex.exp (x*q):= by
 induction k generalizing q with
 | zero=> simp
 | succ k ih=>
   rw [iteratedDeriv_succ,funext ih,deriv_const_mul_field]
   have he : HasDerivAt (fun p:ℝ=>Complex.exp (x*p)) (Complex.exp (x*q)*x) q:= by
      convert! ((Complex.ofRealCLM.hasDerivAt (x:=q)).const_mul x).cexp using 1; simp
   rw [he.deriv,pow_succ];ring
lemma bill_jet (u v:QP)(i:ℕ) : reading i (fun x:ℝ=> Tone.bill (x • u) v)= hitϑ i*((amount i * pairing u v ^ i:ℝ):ℂ):= by
 let a:= I*(pairing u v:ℂ)
 unfold Tone.bill; unfold reading
 rw [show (fun x:ℝ=> Complex.exp _) = _ from funext (?_ : ∀ x:ℝ, Complex.exp (I * (pairing (x • u) v:ℂ))=Complex.exp (a*x)), rayExpr a]
 · simp [a,hitϑ,amount, Complex.real_smul]; ring
 intro x; congr 1; rw [show pairing (x • u) v=x*pairing u v from ?_]; · push_cast; unfold a; ring
 unfold pairing; rw [mul_sum]; exact sum_congr rfl fun i _=> mul_assoc x (u i) (v i)
private lemma at_port (x:Ω)(t:QP) : run (art (fun i:T=>i.val) g) [(x,t)]= ∑ i:T, ∑ j:U, paywave (x,t) (knot ζ (i,j)) * ((K (priv (i,j)):ℝ):ℂ):= by
 let f := region.symm (MS.Cylinder.Taylor.ink priv g); have h: Uses (Set.univ:Set (T×U)) f.val:= Uses.entire _
   
 unfold Sew.art run; rw [study, deriv_lum _ _ (region.symm _) (show Uses ( (Finset.univ:Finset (T×U)):Set (T×U)) _ from ?_), Fintype.sum_prod_type]; simp_rw [shade_nil]; rfl
 simpa using h
local notation "x" => ((Landau.gauge i,u):Branch G Axis)
private def rightSet : Finset (Local A) := Finset.univ.filter (fun e=>e.val.2=i)
private lemma right_sum : run (art ζ g) [(x,t)]=∑ k∈ rightSet A i, bill t (beg i k.val.1)*((K (priv (k,u)):ℝ):ℂ):= by
 rw [at_port, rightSet,Finset.sum_filter]; refine Finset.sum_congr rfl fun k _=> ?_
 split
 next hj =>
    rw [Finset.sum_eq_single_of_mem u (Finset.mem_univ _)]
    · rw [show knot ζ (k,u)=(x,k.val.1) from ?_,Tone.pw]; · rfl
      unfold knot; simp only; rw [hj]; rfl
    intro j _ hN; suffices hv: paywave (x,t) (knot ζ (k,j))=0 by rw [hv,zero_mul]
    by_contra hp; exact hN (congr_arg (fun u:Branch G Axis=>u.2) (in_light _ _ hp).symm)
 next hj=>
    refine Finset.sum_eq_zero fun j _=> ?_; suffices hx: paywave (x,t) (knot ζ (k,j))=0 by rw [hx,zero_mul]
    by_contra hp; exact hj ( Option.some_injective _ (congr_arg (fun u:Branch G Axis =>u.1.1) (in_light _ _ hp).symm))
lemma fills (k:ℕ): coord A (scatterM t u i k)= ∑ j∈ rightSet A i,(amount k * mid_charge t i j.val.1 ^ k) • priv (j,u):= by
 funext j; by_cases h:j.val.2=i
 · rw [Finset.sum_apply,Finset.sum_eq_single_of_mem j (show j∈ rightSet A i from Finset.mem_filter.mpr ⟨mem_univ _,h⟩) ]; · change scatterM t u i k j.val = _; rw [scatterM,if_pos h,h,←show baseC u=cl G u from (by ext; simp [baseC, cl]),smul_smul]; simp [priv]
   intro a _ h; dsimp only [Pi.smul_apply]; rw [priv,Pi.single_eq_of_ne (Ne.symm h),smul_zero]
 rw [Finset.sum_apply,Finset.sum_eq_zero]; change scatterM t u i k j.val= _; rw [scatterM,if_neg h]
 intro a ha; dsimp only [Pi.smul_apply]; unfold priv; rw [Pi.single_eq_of_ne (show j ≠ a from fun e=> h (e.symm ▸ ((mem_filter.mp ha).2 : a.val.2=i))),smul_zero]
lemma found (k:ℕ): reading k (fun c:ℝ=> run (art ζ g) [(x,c • t)]) = hitϑ k * ↑(K (coord A (scatterM t u i k))):= by
 simp_rw [right_sum, mul_comm (Tone.bill _ _)]
 rw [Plane.read_sum ..]; rw [fills,_root_.map_sum,Complex.ofReal_sum,mul_sum]
 · apply Finset.sum_congr rfl; intro j hj
   rw [Plane.read_const,bill_jet,map_smul,smul_eq_mul]; unfold mid_charge; push_cast; ring
 intro j h; exact contDiff_const.mul (bankForm ..)
variable (t': Labels.Key G) (hh:t'.1<d-1)
def mounted := art (fun i:Local A=> i.val) (box A t')
include hh
lemma field_Fit : Fits (mounted A t') (Theater.orbit G (MvPolynomial.X t')) 1 (t'.1+2) false:= by
 rw [Theater.cusp]; apply Fits.rank1; intro a p; by_cases h: ∃ i, a.1=Landau.gauge i
 · obtain ⟨i,ha⟩:=h; rcases a with ⟨a,u⟩; change a=_ at ha; subst a; let g:=box A t'; rw [show MS.Landau.wfield (Landau.gauge i,u)=1 from rfl];
   refine ⟨ ?_,fun H=> by omega,fun k hk=>?_⟩; · unfold mounted; simp_rw [right_sum]; exact ContDiff.sum fun i _=> (bankForm ..).mul contDiff_const
   rw [mounted,found, mids (ht:=hh)]; swap; exact_mod_cast (by linarith: (k:ℤ) ≤ (t'.1+1:ℤ))
   split
   next h=>
      subst k; rw [if_pos (by omega)]; rfl
   next h=> rw [if_neg (by omega)];simp
 push Not at h; have he(t:P): run (art ζ (box A t')) [(a,t)]=0:= by
    rw [at_port]; apply sum_eq_zero; intro k _; apply sum_eq_zero; intro i _; suffices hv: paywave (a,t) (knot ζ (k,i))=0 by rw [hv,zero_mul]
    by_contra hp; exact h k.val.2 (congr_arg (fun u: Branch G Axis=>u.1) (in_light _ _ hp))
 unfold mounted; simp_rw [he]; rw [show Theater.lamp t' (a,p)=0 from ?_]; exact Rest.zero _
 rcases a with ⟨⟨_|i,_|_⟩,a⟩ <;> first| rfl| exact (h i rfl).elim
end YM.FVA2.Press.Integration
