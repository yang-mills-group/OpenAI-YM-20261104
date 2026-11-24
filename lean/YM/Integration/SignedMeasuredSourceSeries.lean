import YM.Integration.SignedMarkedChartGerm
import YM.WilsonCoeffUV.Marked.Paths.Buds

/-! The genuine measured current at each arbitrary independent hypervertex is the native absolutely summable source in every polynomial functional. This commutes its physical unmasked input with Fourier coefficients, fixed physical coordinates, and finite Wick probes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedMeasuredSourceSeries
open Function Filter Finset Lattice Laurent Wilson RG Precision Exterior Tree Bloch Matrix PowerSeries
open FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Soil Stationary
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

def response {α β : Type} [Fintype α] [Fintype β] (Z : α→ Ink β) (n : ℕ) (L : POL β→ₗ[ℝ] ℝ) (j m : ℕ) (x : Fin m→α) : ℝ :=
  L (coeff n ((MvPolynomial.aeval Z (∏i:Fin m,MvPolynomial.X (x i) : POL α))*X^j))

/-- The actual finite functional has one tested monomial for each physical field degree and Taylor grade. -/
theorem value {α β : Type} [Fintype α] [Fintype β] {k : ℕ} (T : Pal ℝ α) (h : shellK k T) (Z : α→ Ink β)
    (n : ℕ) (L : POL β→ₗ[ℝ] ℝ) : L (coeff n (train Z (flash T)))=
      ∑j∈range (n+1),∑m∈range (k+j+1),∑x:Fin m→α,response Z n L j m x • T j m x := by
  let E : POL α→ₐ[ℝ] Ink β := MvPolynomial.aeval Z
  let A (j : ℕ) : POL α→ₗ[ℝ]ℝ :=
    { toFun := fun B=>L (coeff n (E B * X^j))
      map_add' := fun x y=>by rw [map_add,add_mul,map_add,map_add]
      map_smul' := fun c x=>by
        change L (coeff n (E (c • x) * X^j))=c • L (coeff n (E x * X^j))
        rw [map_smul,smul_mul_assoc,PowerSeries.coeff_smul,map_smul] }
  rw [train,edit_coeff _ _ _ (Nat.lt_succ_self n),map_sum,map_sum]
  apply sum_congr rfl;intro j _
  rw [WilsonCoeffUV.Blue.flash,coeff_mk]
  change A j (totalR (T j))=_
  have hs : still (T j) (k+j+1) := fun m hm=>h j m hm
  rw [visible hs,map_sum]
  apply sum_congr rfl;intro m _
  rw [paint,palm_form,map_sum]
  exact sum_congr rfl fun x _=>by rw [map_smul,smul_eq_mul,smul_eq_mul];exact mul_comm ..

/-- A finite collection of physical Taylor coefficients after the native change of coordinates admits any linear polynomial functional without an a priori restriction on its field argument. -/
theorem clock {I α β : Type} [Fintype α] [Fintype β] {k : ℕ} {P : I→ Pal ℝ α} {Q : Pal ℝ α}
    (hp : ∀c,shellK k (P c)) (hq : shellK k Q) (he : ∀i j x,HasSum (fun c=>P c i j x) (Q i j x))
    (Z : α→ Ink β) (n : ℕ) (L : POL β→ₗ[ℝ]ℝ) : HasSum (fun c=>L (coeff n (train Z (flash (P c))))) (L (coeff n (train Z (flash Q)))) := by
  rw [value Q hq]
  simp_rw [fun c=>value (P c) (hp c) Z n L]
  exact hasSum_sum fun j _=>hasSum_sum fun m _=>hasSum_sum fun x _=>(he j m x).const_smul _

variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio)
    (M : Matrix (Woods G f) (Woods G c) ℝ) (ρ : fieldDir G c 1→ AxisChart G F)
variable {I V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {r k : ℕ}

def probe := (retool (shore S F M ρ)).comp (loom (camSlice G S F M))

theorem genuine : probe S F M ρ=train (fun i=>probe S F M ρ (path i)) := by
  apply rail
  · simp [probe,retool,loom,reroll_X]
  · intro q
    change retool (shore S F M ρ) (loom (camSlice G S F M) (realS q))=realS q
    rw [loom_real]
    exact train_real _ _

/-- At arbitrary finite stage the truly funded original path address series converges to the *specified* polynomial coefficient after the actual coordinate changes. Its only bill is the original exponential card and its true curvature valence. -/
theorem bought (T : I→ Comet G V r) {u budget : ℝ} (hu : 0<u) (price : SumBudget (fun i=>integerP (T i) u) budget)
    (hs : ∀i,shadeStar (T i)) (e : ℕ) (hr : r≤k+e) (E : V→L[ℝ]ℝ) (n : ℕ) (L : POL (Active G F⊕Woods G c)→ₗ[ℝ]ℝ) :
    HasSum (fun i=>L (coeff n (probe S F M ρ (flash (ply E.toLinearMap ((volumeR (T i) e).1 f))))))
        (L (coeff n (probe S F M ρ (flash (ply E.toLinearMap ((bolus T e).1 f)))))) := by
  let Z := fun a=>probe S F M ρ (path a)
  rw [genuine S F M ρ]
  apply clock (k:=k)
  · intro i;exact ply_shell _ ((aug_auth (T i) (hs i) hr).span f)
  · exact ply_shell _ ((stars hu price hr hs).span f)
  · intro i j x;exact E.hasSum (elevated hu price e f i j x)

/-- Every actual Wilson path field in the elected address sum retains its genuine configuration and stored power. The whole sum of its measured finite jets is the preselected native coefficient, uniformly as a statement in the independent tester E, order n and every linear numerical probe L. -/
theorem measured (T : I→ Comet G V r) {u budget : ℝ} (hu : 0<u) (price : SumBudget (fun i=>integerP (T i) u) budget)
    (hs : ∀i,shadeStar (T i)) (e b t : ℕ) (hr : r≤k+e) (ht : b+e=r+t)
    (hM : M=reveal G S F*((reveal G S F).transpose*M)) (hρ : ContDiffAt ℝ ω ρ 0) (h0 : ρ 0=0)
    (E : V→L[ℝ]ℝ) (n : ℕ) (L : POL (Active G F⊕Woods G c)→ₗ[ℝ]ℝ) :
    HasSum (fun i=>L (coeff (b+n) ((X:Ink (Active G F⊕Woods G c))^t * jet (fun x:Sloc S F G=>
      (dip (T i) E).unmasked (Work.F03.live F (SignedMarkedChartGerm.chart S F ρ x)) 0))))
      (L (coeff n (probe S F M ρ (flash (ply E.toLinearMap ((bolus T e).1 f)))))) := by
  apply (bought S F M ρ T hu price hs e hr E n L).congr_fun
  intro i
  rw [←SignedMarkedChartGerm.cleared S F M ρ (T i) E e b t ht hM hρ h0,coeff_X_pow_mul',if_pos (Nat.le_add_right b n),Nat.add_sub_cancel_left]
  rfl

end YM.Integration.SignedMeasuredSourceSeries
