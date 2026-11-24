import YM.Integration.WilsonVacuumPreResetFiniteAffineIncome
import YM.Integration.WilsonVacuumPreResetMeasuredWindingSlope
import YM.Next.RANK.Instructions

/-! The complete original finite vacuum and folded cover are compared inside one real Wilson step. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetGraftedField
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Shore FormalBulk08.Lava FormalBulk08.Wine
open FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa FormalBulk08.Wick
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open Next.Rank Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators

variable {G:Gauge} {n f:Side} (S:StepData n f) (F:Forest S.ratio)
variable (H:Hull (Pine G S F) (wire G n))(B:wire G n→ℝ)
local notation "v" => Pine G S F

def field (a:wire G f):MvPolynomial v ℝ:=
  ∑i:v,MvPolynomial.C ((Flat.dropRoot G S F)ᵀ a i) *
    (MvPolynomial.X i+MvPolynomial.C (traceP B (H.drift i)))

private theorem at_field (x:v→ℝ)(a:wire G f):
    MvPolynomial.eval x (field S F H B a)=Reef.offer G F (fun i=>x i+traceP B (H.drift i)) a:=by
  rw [field,map_sum,Reef.offer_as]
  apply Finset.sum_congr rfl
  intro i _
  simp

private theorem read_sub {U T:Type*}(q:T→MvPolynomial U ℝ)(x:U→ℝ)(p:MvPolynomial T ℝ):
    MvPolynomial.eval x (MvPolynomial.aeval q p)=MvPolynomial.eval (fun i=>MvPolynomial.eval x (q i)) p:=by
  induction p using MvPolynomial.induction_on with
  | C a=>simp
  | add p r hp hr=>simp only [map_add,hp,hr]
  | mul_X p i hp=>simp only [map_mul,MvPolynomial.aeval_X,MvPolynomial.eval_X,hp]

private theorem complex_sub {U T:Type*}(q:T→MvPolynomial U ℝ)(p:MvPolynomial T ℝ):
    MvPolynomial.map Complex.ofRealHom (MvPolynomial.aeval q p)=
      MvPolynomial.aeval (fun i=>MvPolynomial.map Complex.ofRealHom (q i)) (MvPolynomial.map Complex.ofRealHom p):=by
  induction p using MvPolynomial.induction_on with
  | C a=>simp
  | add p r hp hr=>simp only [map_add,hp,hr]
  | mul_X p i hp=>simp only [map_mul,MvPolynomial.aeval_X,MvPolynomial.map_X,hp]

/-- On the same shifted Gaussian the signed incoming polynomial is the
printed fine angular coefficient, pulled back by its actual affine field. -/
theorem coefficient (O:ChartRatio G)(law:LocalRatio O)(tag:S.Choices)(D:Pap (wire G f))(e:ℕ):
    WilsonVacuumPreResetFiniteLogBudget.polynomial B (Orb.toInk H (WilsonVacuumPreResetFiniteTilt.lifted F D)) e=
      MvPolynomial.aeval (fun i=>MvPolynomial.map Complex.ofRealHom (field S F H B i)) (MvPolynomial.map Complex.ofRealHom (coeff e D)):=by
  rw [←complex_sub]
  apply congrArg (MvPolynomial.map Complex.ofRealHom)
  apply MvPolynomial.funext
  intro x
  rw [read_sub]
  simp_rw [at_field]
  let z:=fun i=>x i+traceP B (H.drift i)
  have moved:=WilsonVacuumPreResetFiniteTilt.moved F tag O 0 D
  rw [sub_zero] at moved
  have pay:MvPolynomial.eval (Sum.elim z B) (coeff e (WilsonVacuumPreResetFiniteTilt.lifted F D))=
      MvPolynomial.eval (Reef.offer G F z) (coeff e D):=by
    rw [←moved,map_sub,map_sub,WilsonConditionalTaylorWheelReef.primitive S F O law tag D z B e,
      WilsonConditionalTaylorWheelReef.primitive S F O law tag 0 z B e,map_zero,map_zero]
    ring
  have inv:=congrArg (PowerSeries.coeff e) (WilsonVacuumPreResetIndependentMarginal.direction H x B (WilsonVacuumPreResetFiniteTilt.lifted F D))
  simp only [glimpse_coeff,WilsonVacuumPreResetIndependentMarginal.observe,coeff_map] at inv
  exact inv.trans pay

/-- Compact substitution price for a polynomial with arbitrarily many spatial
coordinates, in its native coefficient-mass norm. -/
private theorem substitution {U T:Type*} (q:T→MvPolynomial U ℂ)(A:ℝ)(one:1≤A)(each:∀i,Rise.coin (q i)≤A)
    (p:MvPolynomial T ℂ):
    Rise.coin (MvPolynomial.aeval q p)≤Rise.coin p*A^p.totalDegree:=by
  let t:MvPolynomial T ℂ→ₐ[ℂ] MvPolynomial U ℂ:=MvPolynomial.aeval q
  refine LiftMark.lin_tile t.toLinearMap _ fun i hi=>?_
  obtain ⟨k,hk⟩:=Common.letter i
  let len:=i.sum fun _ d=>d
  have lo:len≤p.totalDegree:=MvPolynomial.le_totalDegree hi
  have fields: Rise.coin (t (Normal.glyphs k Finset.univ)) ≤ A^(Finset.univ:Finset (Fin len)).card:=by
    rw [Normal.glyphs,map_prod]
    refine (Rise.purchased _ zero_le_one ..).trans ?_
    rw [←Finset.prod_const]
    exact Finset.prod_le_prod (fun i _=>Rise.sign _ _ zero_le_one) fun i _=>by simpa [t] using each (k i)
  rw [hk]
  exact fields.trans (pow_le_pow_right₀ one (by simpa using lo))

/-- Fixed-order bill for the old fine angular error. The allowed foreground
noise is unbounded in the original Schur measure. -/
theorem price (O:ChartRatio G)(law:LocalRatio O)(tag:S.Choices)(D:Pap (wire G f))(e:ℕ)
    (m:ℝ)(pos:0≤ m)(measure:∀i,|traceP B (H.drift i)|≤ m):
    let A:=1+Fintype.card v*(1+m)
    Rise.coin (WilsonVacuumPreResetFiniteLogBudget.polynomial B (Orb.toInk H (WilsonVacuumPreResetFiniteTilt.lifted F D)) e) ≤
      Rise.coin (MvPolynomial.map Complex.ofRealHom (coeff e D))*A^(MvPolynomial.map Complex.ofRealHom (coeff e D)).totalDegree:=by
  intro A
  rw [coefficient S F H B O law tag]
  have ha:1≤A:=by dsimp [A];exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  apply substitution _ A ha
  intro a
  rw [field,map_sum]
  apply (Rise.collect _ zero_le_one ..).trans
  calc
    _≤∑_i:v,(1+m):=by
      apply Finset.sum_le_sum
      intro i _
      rw [map_mul,map_add,MvPolynomial.map_C,MvPolynomial.map_X,MvPolynomial.map_C]
      apply (Rise.funds _ zero_le_one ..).trans
      have flag:‖(Complex.ofRealHom ((Flat.dropRoot G S F)ᵀ a i))‖≤1:=by
        change ‖((1:Matrix (wire G f) (wire G f) ℝ) i.val a:ℂ)‖≤1
        rw [Matrix.one_apply];split <;> simp
      have source:Rise.coin (MvPolynomial.X i+MvPolynomial.C (Complex.ofRealHom (traceP B (H.drift i))))≤1+m:=by
        apply (Rise.taller _ zero_le_one ..).trans
        simpa [Rise.coin,Complex.norm_real,Real.norm_eq_abs] using add_le_add_left (measure i) 1
      have active:Rise.coin (MvPolynomial.C (Complex.ofRealHom ((Flat.dropRoot G S F)ᵀ a i)):MvPolynomial v ℂ)≤1:=by simpa [Rise.coin] using flag
      exact (mul_le_mul active source (Rise.sign _ _ zero_le_one) zero_le_one).trans_eq (one_mul _)
    _≤A:=by dsimp [A];simp [nsmul_eq_mul];linarith

end YM.Integration.WilsonVacuumPreResetGraftedField
end
