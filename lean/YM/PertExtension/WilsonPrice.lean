import YM.PertExtension.RuleNode

/-! Combining the top diagonal matrix columns on the joint inverse square.
Explicit engineering and mesh prefactor, independent of reality convergence.
 -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.PertExtension.LatticePT.Price
open Function Filter Set Wilson Lattice RG MeasureTheory Orb GaussianScore Gauge MvPolynomial Finset Next.Rank Next.Rank.Normal
open Chart Series Series.Tested Source Bid Labels Heat Heat.Top Slope Mixed Leading Node Screens
open scoped ContDiff Topology Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge}{I:Type*}[Fintype I](v:I→Word G)

def packet:=pot Finset.univ (smear ∘ v)
def degree:=∑ i:I,(v i).d

theorem combined (ε:ℝ): (∑ t: Task v,pricedBare v t ε)=(↑(ε^(4*Fintype.card I) * ε⁻¹^(degree v) : ℝ):ℂ) • packet v := by
    classical
    have hC u j :(u:Word G).cost j ε=(ε^4 * ε⁻¹^u.d)*topBasis u.S u.H u.sound u.chosen u.axis j:=by rw [Word.cost,division_def,inv_pow]
    let cx (i : I):ℝ:=ε^4 * ε⁻¹^(v i).d
    unfold pricedBare pot
    let FF (i : I)(j:(v i).F.Index): poly (I×Atom G):=post i ((↑((v i).cost j ε : ℝ):ℂ) • bareFactor (v i) j)
    change (∑ t:∀ i:I,(v i).F.Index, ∏ i:I,FF i (t i)) = _
    rw [← Fintype.prod_sum FF, show ε^(4*Fintype.card I)*ε⁻¹^degree v=∏ i∈Finset.univ,cx i from by unfold degree cx; rw [prod_mul_distrib,prod_pow_eq_pow_sum,prod_pow_eq_pow_sum];congr 2; simp [nsmul_eq_mul,mul_comm]]
    calc
      _ = ∏ i:I, (↑(cx i):ℂ) • (post i ((Leading.smear ∘ v) i)) := by
        dsimp only [FF];refine Finset.prod_congr rfl fun i hi=>?_ ; unfold Leading.smear Vertex.combination;change (∑ j:(v i).F.Index, post i ((↑(_:ℝ):ℂ) • bareFactor (v i) j))= _ • post i (∑ j, _) -- placeholder leads metavariables fix
        rw [map_sum, Finset.smul_sum];refine Finset.sum_congr rfl fun j _=>?_
        unfold bareFactor;rw [map_smul,hC,Complex.ofReal_mul,mul_smul,map_smul]
      _ = _ := by simp only [Complex.ofReal_prod, ← C_mul',prod_mul_distrib,map_prod, packet, pot, mul_assoc]

variable (q:ℕ+) (m : ℕ)
def KK (s:I→Cover) := jointFinite (G:=G) (wrap (side q m) ∘ s) (side_even ..)
def orig (o:Native q m):Cover := fun i=>(o i).val
lemma casts (o : Native q m) : wrap (side q m) (orig q m o)=o:=by ext i; change (↑(((o i).val : ℕ): ℤ) : Per (side q m)) = _;rw [Int.cast_natCast];exact ZMod.natCast_zmod_val _

def ticket (o:Cover)(x:I→Cover):= (magnify q m^(degree v)) * (blend (KK q m (fun i=>o+x i)) 0 (packet v)).re
lemma centered (x:I→Native q m)(o:Native q m): KK (G:=G) q m (fun i=>lift o+(lift ∘ x) i)=jointFinite (G:=G) (fun i=>x i+o) (side_even q m) := by
    unfold KK; rw [show wrap (side q m) ∘ (fun i=>lift o+(lift ∘ x) i)=(fun i=>x i+o) from funext (fun i=> by simp only [Function.comp_apply,map_add (wrap _),wrap_lift];exact add_comm ..)];done
lemma sum_identity (x:I→Native q m)(o:Native q m):
    (∑ t:Task v, diagonalWith (tray G) (restrictedO (placements v q m o x t)) (number v t+0)) = epsilon q m^(4*Fintype.card I) * (ticket v q m (lift o) (lift ∘ x)) :=by
    unfold placements
    simp_rw [diagonal_leading (h:=side_even q m)]
    rw [← Complex.re_sum,← map_sum,combined]
    set μ : ℝ := epsilon q m
    rw [map_smul,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,mul_assoc]
    rw [ticket,centered]; congr 2; · unfold μ epsilon;rw [inv_inv];done


lemma diag_read (Ψ: (I→E4)→ℝ): polynomialTop v q m Ψ 0 =
     epsilon q m ^ (4*Fintype.card I) * (∑ x:I→Native q m,∑ o∈origins q m, price q m Ψ x * (ticket v q m (orig q m o) (lift ∘ x))) := by
    simp_rw [polynomialTop,Finset.mul_sum]
    apply Finset.sum_congr rfl fun x _=> Finset.sum_congr rfl fun o _=>?_
    rw [← Finset.mul_sum, sum_identity]
    unfold ticket KK; have he i : wrap (side q m) (lift o + (lift ∘ x) i) = wrap (side q m) (orig q m o+(lift ∘ x) i) :=by rw [map_add,map_add,wrap_lift,casts]
    rw [show wrap (side q m) ∘ (fun i=>lift o+(lift ∘ x) i)=_ from funext he]; dsimp only [Function.comp_def]; ring

end YM.PertExtension.LatticePT.Price
