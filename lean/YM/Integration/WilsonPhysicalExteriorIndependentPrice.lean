import YM.Integration.WilsonPhysicalExteriorSourceInverse
import YM.Integration.WilsonPhysicalExteriorIndependentWord

/-! A sharp finite-order cash price on the whole independently
transported Wilson detector word, including every marked length.
The real polynomial register is chosen before all the clocks. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorIndependentPrice
open Function Finset Matrix PowerSeries Lattice
open MS MS.Land MS.Menus MS.Rake FVAAlt2 Lobby
open WilsonPhysicalExteriorSourceInverse WilsonPhysicalExteriorIndependentWord
open WilsonPhysicalExteriorTransportedFields WilsonPhysicalExteriorRegisteredRows
open scoped BigOperators Classical
variable {G:Gauge}{B:MS.Local.Physical.Deck G}{W:Type} [Fintype W]
local notation "PS" => PowerSeries ℂ
variable (Q:Prescription B)

def clock (v:W→ℝ) (y z:ℝ) : W×Fin 3→ℝ:=fun a=>(![v a.1,y,z]:Fin 3→ℝ) a.2
def length (x:W×Fin 3→ℝ) : ℝ:=1+∑ i,|x i|
private theorem one (x:W×Fin 3→ℝ) : 1≤length x := by
  have h:0≤∑i,|x i|:=sum_nonneg fun _ _=>abs_nonneg _
  dsimp [length];linarith
def labels (d:W→ℕ) (b:(i:W)→Plaid B (d i)) : W→Label B:=fun i=>⟨d i,b i⟩
def stored (d:W→ℕ) (b:(i:W)→Plaid B (d i)) (a:Array B d) : PowerSeries (MvPolynomial (W×Fin 3) ℝ) :=
  ∏i:W,PowerSeries.map (MvPolynomial.rename (Prod.mk i)).toRingHom
    (tariff Q (d i) (Land.read (b i)) (a i))
private def atLogs (x:W×Fin 3→ℝ) : MvPolynomial (W×Fin 3) ℝ→+*ℂ:=Complex.ofRealHom.comp (MvPolynomial.eval x)

theorem polynomial (d:W→ℕ) (b:(i:W)→Plaid B (d i)) (a:Array B d) (v:W→ℝ) (y z:ℝ) :
    PowerSeries.map (atLogs (clock v y z)) (stored Q d b a)=rate Q (labels d b) v y z a := by
  rw [stored,map_prod,rate]
  apply prod_congr rfl;intro i _
  apply PowerSeries.ext;intro k
  have hom : (MvPolynomial.eval (clock v y z)).comp (MvPolynomial.rename (Prod.mk i)).toRingHom =
      MvPolynomial.eval (![v i,y,z]:Fin 3→ℝ) := by
    apply MvPolynomial.ringHom_ext <;> intro r <;> simp [clock]
  rw [PowerSeries.coeff_map,PowerSeries.coeff_map]
  calc
    _=((MvPolynomial.eval (![v i,y,z]:Fin 3→ℝ)
        (coeff k (tariff Q (d i) (Land.read (b i)) (a i))):ℝ):ℂ) :=
      congrArg (fun r:ℝ=>(r:ℂ)) (DFunLike.congr_fun hom _)
    _=_:=(WilsonPhysicalExteriorSourceInverse.coefficient Q
      ((labels d b) i) (a i) k (![v i,y,z]:Fin 3→ℝ)).symm

private theorem bounded (P:MvPolynomial (W×Fin 3) ℝ) :
    ∃ A:ℝ,0≤A ∧ ∃d:ℕ,∀x:W×Fin 3→ℝ,|(MvPolynomial.eval x) P|≤A*(length x)^d := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨|a|,abs_nonneg _,0,by simp⟩
  | add p q hp hq =>
    obtain ⟨A,a,e,u⟩:=hp;obtain ⟨B,b,f,v⟩:=hq
    refine ⟨A+B,add_nonneg a b,max e f,fun x=>?_⟩
    rw [map_add,add_mul]
    exact (abs_add_le ..).trans (add_le_add
      ((u x).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one x) (le_max_left e f)) a))
      ((v x).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one x) (le_max_right e f)) b)))
  | mul_X p i hp =>
    obtain ⟨A,a,e,u⟩:=hp
    have bound (x:W×Fin 3→ℝ) : |x i|≤length x := by
      have h:=single_le_sum (fun j (_:j∈(univ:Finset (W×Fin 3)))=>abs_nonneg (x j)) (mem_univ i)
      unfold length;linarith
    refine ⟨A,a,e+1,fun x=>?_⟩
    rw [map_mul,MvPolynomial.eval_X,abs_mul,pow_succ,←mul_assoc]
    exact mul_le_mul (u x) (bound x) (abs_nonneg _) (mul_nonneg a (pow_nonneg (by linarith [one x]) _))

/-- The single coefficient bound is uniform over all source and target
fields in their declared independent grade budgets and all orders ≤L. -/
theorem paid (d:W→ℕ) (L:ℕ) :
    ∃ A:ℝ,0≤A ∧ ∃m:ℕ,∀ b:(i:W)→Plaid B (d i),∀ a:Array B d,∀ k≤L,
      ∀ v:W→ℝ,∀ y z:ℝ,
      ‖PowerSeries.coeff k (rate Q (labels d b) v y z a)‖≤A*(length (clock v y z))^m := by
  let I:=((i:W)→Plaid B (d i)) × (Array B d × Fin (L+1))
  let P (j:I):=PowerSeries.coeff j.2.2.val (stored Q d j.1 j.2.1)
  choose A pos m h using fun j:I=>bounded (P j)
  refine ⟨∑j,A j,sum_nonneg fun j _=>pos j,∑j,m j,?_⟩
  intro b a k hk v y z
  let j:I:=⟨b,a,⟨k,by omega⟩⟩;let x:=clock v y z
  have hA:A j≤∑i,A i:=single_le_sum (fun i _=>pos i) (mem_univ j)
  have he:m j≤∑i,m i:=single_le_sum (fun i _=>Nat.zero_le (m i)) (mem_univ j)
  rw [←polynomial Q d b a v y z,PowerSeries.coeff_map]
  change ‖((MvPolynomial.eval x (P j):ℝ):ℂ)‖≤_
  rw [Complex.norm_real,Real.norm_eq_abs]
  exact (h j x).trans (mul_le_mul hA (pow_le_pow_right₀ (one x) he)
    (pow_nonneg (by linarith [one x]) _) (sum_nonneg fun i _=>pos i))

end YM.Integration.WilsonPhysicalExteriorIndependentPrice
end
