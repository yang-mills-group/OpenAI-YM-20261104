import YM.FVAAlt2.Inject
import YM.FVAAlt2.RawEval

/-! Remaining bosonic integrals. A moments paid by the true finite-dimensional
Gaussian on the quotient. No mass away from zero, not even on scalar outputs. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVAAlt2.Bos
open Finset Function Filter MeasureTheory Lattice
open MS MS.Orbit MS.Orbit.LogReal MS.Orbit.Cog MS.Koszul MS.Book MS.Swirl MS.Puff MS.Puff.Actors MS.Puff.Mom
open PertExtension GaussianScore PertExtension.Series Pert.Orb SchemeRG11.Sway
open scoped ContDiff PowerSeries
set_option linter.unusedSectionVars false
variable {ι:Type}[Fintype ι] [DecidableEq ι]
local notation "E"=> Bos ι
local notation "𝑷"=>PowerSeries (Bos ι)
local notation "p"=> pNo ι

section derivatives
variable {J:Type}[DecidableEq J] (s: Finset J)(f:J→ι)
lemma grad_prod (i:ι) (X:J→E) : grad i (∏ j∈s,X j) = ∑ j∈s, (grad i (X j))*∏ k∈s.erase j,X k:= by
  induction s using Finset.induction_on with
  | empty=> rw [Finset.sum_empty,Finset.prod_empty, grad_one]
  | insert j s hj ih=>
    rw [Finset.prod_insert hj, grad_mul,Finset.sum_insert hj,Finset.erase_insert hj,ih, Finset.mul_sum]
    apply congr_arg₂ (·+·) rfl; refine Finset.sum_congr rfl fun k hk=>?_
    rw [Finset.erase_insert_of_ne ( fun (he:j=k)=> hj (he ▸ hk) ),Finset.prod_insert (fun h=> hj ((Finset.mem_erase.mp h).2)),mul_left_comm]
/-- linear closure of the set of field monomials -/
lemma whole_eq (G G':E→ₗ[ℂ] ℂ)(h : G 1=G' 1)(hp:∀ (s:Finset ℕ)(f:ℕ→ι), G (∏ j∈s,letter (f j))=G' (∏ j∈s,letter (f j))): G=G':= by
  ext1 x; refine (induction (fun x:E=> G x=G' x ∧ ∀ (s:Finset ℕ)(f:ℕ→ι), G (x*∏ j∈s,letter (f j))=G' (x*∏ j∈s,letter (f j))) ⟨ h,fun s f=>by rw [one_mul]; exact hp s f ⟩ ?_ ?_ ?_ x).1
  · rintro a b ⟨ha,he⟩ ⟨hb,hf⟩; exact ⟨by rw [map_add,map_add,ha,hb],fun s f=>by rw [add_mul,map_add,map_add,hf s f,he s f]⟩
  · rintro c a ⟨ha,hu⟩; refine ⟨by rw [map_smul,map_smul,ha],fun s f=>?_⟩; rw [smul_mul_assoc,map_smul,map_smul,hu s f]
  rintro i a ⟨ha,h⟩
  rw [mul_comm]; constructor; · simpa using h {0} (fun _=>i)
  intro s f; obtain ⟨k,hk⟩:=Infinite.exists_notMem_finset s
  let g:= Function.update f k i
  have ht : ∏ j∈insert k s,letter (g j)=letter i*∏ j∈s,letter (f j):= by
     rw [Finset.prod_insert hk,show g k=i from Function.update_self ..]; exact congr_arg _ (Finset.prod_congr rfl fun j hj=> congr_arg letter (Function.update_of_ne (fun (he:j=k)=>hk (he ▸ hj)) i f))
  rw [mul_assoc,← ht]; exact h _ _
end derivatives

variable {G:Gauge}{n:Side}(A:Module.Basis ι ℝ (Land G n))
local notation "D₀"=> Land G n
local notation "σ"=>landLaw G n
local notation "θ"=>white A
local notation "μ"=>chosen G n
local notation "κ"=>Radial.kernel (LAND (G:=G) (n:=n))

lemma WClear: Clear p θ:=fun _ _ _=>rfl
lemma WSym : Cog.Sym p θ:=by
  intro x y; rw [cross_false,one_mul]; unfold white; congr 2; symm; unfold GaussianScore.Law.wick
  -- use Rcov chrSym?
  let L:=σ; rw [← L.applies (A.coord y),← L.applies (A.coord x),L.solves,L.solves]; exact L.turns ..
abbrev μC (G:Gauge)(n:Side) : ℂ:= ↑(∫ x:Land G n,Radial.kernel LAND x∂(chosen G n))
lemma μ_nonzero (G:Gauge)(n:Side): μC G n≠0:= Complex.ofReal_ne_zero.mpr (Local.shade_pos _ (LAND_go (G:=G) (n:=n))).ne'
def value(x:Land G n): E→ₐ[ℂ] ℂ:=evalAt (fun i=> (A.coord i x:ℂ))
lemma value_letter(x:D₀)(i:ι): value A x (letter i)=(A.coord i x:ℂ):= by
   have he:= eval_letter (fun i=> (A.coord i x:ℂ)) 1 i; rw [mul_one, show evalL _ (1:E)=1 from map_one (value A x),mul_one] at he; exact he

lemma eval_budget (x:E):Tame (fun u:D₀=> value A u x):= by
  refine induction (fun x:E=> Tame (fun u:D₀=> value A u x)) ?_ ?_ ?_ ?_ x
  · simp_rw [map_one]; exact Tame.constant _
  · intro x y hx hy; simp_rw [map_add]; exact hx.add hy
  · intro r x hx; simp_rw [map_smul,smul_eq_mul]; exact Tame.mul (Tame.constant r) hx
  intro i x hx; simp_rw [map_mul,value_letter]; exact Tame.mul (Tame.ofReal (Tame.clm («E»:=Land G n) (F:=ℝ) ((A.coord i).toContinuousLinearMap))) hx

lemma wick_integrable (x:E): Integrable (fun u:D₀=> (↑(κ u):ℂ)*value A u x) μ:= by
  let W(u : D₀): PowerSeries ℂ:= PowerSeries.C (value A u x)
  have hw:Ready W:= by
    intro k; by_cases he:k=0; · simpa only [W,PowerSeries.coeff_C,if_pos he] using eval_budget A x
    simp_rw [W, PowerSeries.coeff_C, if_neg he]; exact Tame.constant (_:ℂ)
  have he:= Lam.cost_pay μ LAND_go hw 0; unfold Lam.Cost W at he; simpa only [PowerSeries.coeff_C,if_true] using he

def integralL(A:Module.Basis ι ℝ (Land G n)): Bos ι→ₗ[ℂ] ℂ:={
  toFun f:= (∫ x:Land G n, ((↑(Radial.kernel LAND x):ℂ)*value A x f) ∂(chosen G n))/μC G n
  map_add' f g:= by simp_rw [map_add,mul_add, MeasureTheory.integral_add (wick_integrable A f) (wick_integrable A g),add_div]
  map_smul' r f:= by simp_rw [map_smul,smul_eq_mul,mul_left_comm (↑(_:ℝ)) r, MeasureTheory.integral_const_mul,mul_div_assoc]; rfl }

def Ω (A:Module.Basis ι ℝ (Land G n)): E→ₗ[ℂ] ℂ:= (View (white A)).comp (FlatEven _).subtype
lemma one_bill : Ω A 1= integralL A 1:=by change View θ (1:E).val=(∫ x:D₀, _ ∂μ)/_; rw [Com.one_val, minView]; simp_rw [map_one,mul_one, integral_complex_ofReal]; exact (div_self (μ_nonzero G n)).symm

lemma letter_bill (i:ι)(f:E): Ω A (letter i*f)=∑ j:ι,(↑((σ).wick (A.coord i) (A.coord j)):ℂ) * Ω A (grad j f):= by
  change View θ (product p _ _) = _; rw [letter_val,ibpV i (WClear A) (WSym A) f.sym f.small]; refine sum_congr rfl fun j _=>?_ ; unfold Chill white; rw [←mul_assoc]; norm_num; left; rfl
lemma integralL_product{s:Finset ℕ}(f:ℕ→ι): integralL A (∏ j∈s,letter (f j))=((σ).average μ (Law.product (A.coord ∘ f) s):ℂ):= by
   change (∫ x:D₀, (↑(κ x):ℂ)*value A x (∏ j∈s,letter (f j)) ∂μ)/_=_; unfold Law.average; push_cast; congr 1
   · rw [←integral_complex_ofReal]; simp_rw [LANDkernel,map_prod,value_letter,Pi.mul_apply, Law.product,Complex.ofReal_mul,Complex.ofReal_prod]; apply integral_congr_ae; exact Eventually.of_forall fun x=>mul_comm ..
   unfold μC; simp_rw [LANDkernel]

theorem wick_real: Ω A=integralL A:= by
 apply whole_eq _ _ (one_bill _)
 -- product recur
 intro s f
 induction s using Finset.strongInduction with | _ s H=>
   obtain rfl|⟨i,hi⟩:=s.eq_empty_or_nonempty
   · simpa using one_bill A
   let t:=s.erase i; have hh: ∏ j∈s,letter (f j)=letter (f i)* ∏ j∈t,letter (f j):= (Finset.mul_prod_erase s (letter ∘ f) hi).symm
   rw [integralL_product,hh,letter_bill]
   let r:=fun j:ι=> (↑((σ).wick (A.coord (f i)) (A.coord j)):ℂ)
   let P(j):=∏ k∈ t.erase j,letter (f k)
   have hZ: Law.product (A.coord ∘ f) s=(fun x=> Law.product (A.coord ∘ f) t x * A.coord (f i) x):= by
      unfold Law.product; funext x; rw [mul_comm]; exact Eq.symm (Finset.mul_prod_erase _ (fun i:ℕ=> A.coord (f i) x) hi)
   letI hu: Measure.IsAddLeftInvariant μ:= (chosen_haar G n).toIsAddLeftInvariant
   letI hu: Measure.IsAddRightInvariant μ:= IsAddLeftInvariant.isAddRightInvariant
   rw [hZ,PertExtension.GaussianScore.Law.recursion,Complex.ofReal_sum]
   simp_rw [grad_prod,map_sum, Finset.mul_sum]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun j hj=>?_; rw [Finset.sum_eq_single_of_mem (f j) (Finset.mem_univ _)]
   · rw [grad_letter,if_pos rfl,one_mul,H (t.erase j) (Finset.ssubset_of_subset_of_ssubset (erase_subset ..) (erase_ssubset hi)), integralL_product, mul_comm,Complex.ofReal_mul]; rfl
   intro k hk ht; rw [grad_letter, if_neg ht,zero_mul,map_zero,mul_zero]

end YM.FVAAlt2.Bos
