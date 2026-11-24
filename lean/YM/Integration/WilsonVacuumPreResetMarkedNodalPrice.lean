import YM.Integration.WilsonVacuumPreResetMarkedCofactors

/-! The native finite connected marked coefficient after its true affine
projection and kinetic reversion, with every incoming proper-face bill. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetMarkedNodalPrice
open Function Filter Finset Lattice Wilson RG Precision Laurent
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Winding
open WilsonVacuumPreResetFiniteHeatIntake WilsonVacuumPreResetFiniteHeatWindow
open WilsonVacuumPreResetMarkedProducts WilsonVacuumPreResetMarkedOrdinaryBound
open scoped Classical BigOperators
variable {ι:Type}[DecidableEq ι]

private theorem projected {U W V:Type}[Fintype U][NormedAddCommGroup V][NormedSpace ℝ V]
    (M:Matrix U W ℝ)(F:Gen V U)(r:ℕ)(A:ℝ)(pos:0≤A)
    (one:∀u w,|M u w|≤1)(row:∀x,‖F r x‖≤A)(x):
    ‖fade M F r x‖≤(Fintype.card U:ℝ)^r*A:=by
  obtain ⟨L,hL,read⟩:=exists_dual_vector'' ℝ (fade M F r x)
  have inside(y):|cloaks L.toLinearMap F r y|≤A:=by
    calc
      _≤‖F r y‖:=by
        change |L (F r y)|≤‖F r y‖
        simpa only [Real.norm_eq_abs,one_mul] using
          (L.le_opNorm (F r y)).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
      _≤A:=row y
  have budget:=application M (cloaks L.toLinearMap F) r 1 A zero_le_one pos one inside x
  have same:L (fade M F r x)=fade M (cloaks L.toLinearMap F) r x:=
    congrFun (congrFun (cloak_fade L.toLinearMap M F) r) x
  rw [←same,show L (fade M F r x)=‖fade M F r x‖ from read,abs_of_nonneg (norm_nonneg _),
    mul_one] at budget
  exact budget

def power (e l r s:ℕ):ℕ:=20*3^(l+3*e)*s+r+1

theorem selected (G:Gauge)(D:ι→ℕ)(I:Finset ι)(k:ι→ℕ)(e r:ℕ):∃M:ℝ,0≤M ∧
    ∀C:Arch G,∀p:ScrollV e C,∀A:ℝ,0≤A →
    (∀i≤e,∀v≤horizon e (r+2*mass k I),∀x,|casePW p.wheel C.R p.cone p.W' i v x|≤A) →
    ∀V:PChart G (p.n*C.P.L),(∀i≤e,∀v≤horizon e (r+2*mass k I),∀x,|V i v x|≤1) →
    ∀t:ℝ,|t|≤1 →∀(K:family G D)(a:ι→ℝ),(∀j,0<a j)→
    (∀J⊆I,J.Nonempty→Bounded e (horizon e (r+2*mass k I)) ((K J).1 (p.n*C.P.L)) (weights a J))→
    ∀c:Cost,∀i≤e,∀x,‖mist p.wheel p.shadow p.H (p.T p.n) C.R (p.W'+t•V) K c k I i r x‖≤
      rimJ c i r*(M*(fee p A (r+2*mass k I))^(power e (mass k I) r I.card)*weights a I):=by
  let l:=mass k I
  let q:=20*3^(l+3*e)*I.card
  obtain ⟨M,Mpos,paid⟩:=WilsonVacuumPreResetMarkedCofactors.original G D I e l r
  refine ⟨M,Mpos,?_⟩
  intro C p A apos old V small t unit K a hot bands c i hi x
  let B:=fee p A (r+2*l)
  obtain ⟨base,width,many,_,_,_⟩:=inputs p A (r+2*l) apos old V small t unit
  have b:1≤B:=by dsimp only [B];linarith
  have hB:=zero_le_one.trans b
  let X:=inHeat p.wheel p.shadow p.H (p.T p.n) C.R (p.W'+t•V) K I
  let Y:=M*B^q*weights a I
  have ypos:0≤Y:=mul_nonneg (mul_nonneg Mpos (pow_nonneg hB _)) (positive a (fun j=>(hot j).le) I)
  have table:=paid C p A apos old V small t unit K a hot bands
  have single(j:ℕ)(hj:j≤e)(y):‖finalZ X l j r y‖≤B*Y:=by
    simp only [finalZ,Finset.sum_apply]
    apply (norm_sum_le ..).trans
    calc
      _≤∑w∈range (1+l+3*j),Y:=Finset.sum_le_sum fun w hw=>table w
          (by have nn:=mem_range.mp hw;omega) j hj r le_rfl y
      _=((1+l+3*j:ℕ):ℝ)*Y:=by simp
      _≤B*Y:=mul_le_mul_of_nonneg_right ((by exact_mod_cast
        (show 1+l+3*j≤horizon e (r+2*l)+2 by unfold horizon;omega):
          ((1+l+3*j:ℕ):ℝ)≤((horizon e (r+2*l)+2:ℕ):ℝ)).trans width) ypos
  have pull(j:ℕ)(hj:j≤e):
      ‖fade plug (finalZ X l j) r x‖≤M*B^(power e l r I.card)*weights a I:=by
    have slots(u:Joint G (p.n*C.P.L) p.n)(v:Woods G p.n):|plug u v|≤1:=by
      simp only [plug,Matrix.transpose_apply,rightFlag,Matrix.of_apply]
      split <;> norm_num
    apply (projected plug _ r (B*Y) (mul_nonneg hB ypos) slots (single j hj) x).trans
    calc
      _≤B^r*(B*Y):=mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) many _) (mul_nonneg hB ypos)
      _=M*B^(power e l r I.card)*weights a I:=by dsimp only [Y,power,q];rw [pow_succ,pow_add];ring
  let f(j:ℕ):=PowerSeries.coeff (i-j) (c^j*(c⁻¹)^r)
  let out:=M*B^(power e l r I.card)*weights a I
  simp only [mist,Blue.mix,Finset.sum_apply,Pi.smul_apply]
  change ‖∑j∈range (i+1),f j • fade plug (finalZ X l j) r x‖≤rimJ c i r*out
  apply (norm_sum_le ..).trans
  unfold rimJ
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (pull j ((Nat.lt_succ_iff.mp (mem_range.mp hj)).trans hi)) (norm_nonneg _)

end YM.Integration.WilsonVacuumPreResetMarkedNodalPrice
end
