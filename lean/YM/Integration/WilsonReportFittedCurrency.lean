import YM.Integration.WilsonReportRegularMoments
import YM.Integration.WilsonPhysicalCutoffCurrency

/-! Convert the authentic paid finite-section estimates at the deeper
reporting berth to the externally prescribed physical coupling, on the
same run and with its exact graded fine labels. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportFittedCurrency
open Function Filter Finset Set MeasureTheory Lattice Wilson RG Source Marker Multi Extraction Table
open Next.Rank Next.Rank.Spindle OPE OPE.Orbits RG12 RG17 RG17.Panoramic SharpGram
open MergeProof MergeProof.Ribbons.ManyCopies.Patrol PhysicalNext.Repeat.Legato Pert.Asymptotics
open scoped Topology Classical BigOperators
variable {G : Gauge} {R : Run G} {f : Extraction.Order} {S : Table R.family.book} {F : Spec.Final R.family f S}

def factor (n a D q : ℕ) : ℝ := (1+(n:ℝ))^D * 2^(a*D) * 2^q

private theorem scalar {β g z A : ℝ} (n a D q : ℕ) (A0 : 0≤A) (zp : 0<z)
    (size : A ≤ (1+(n:ℝ))*β^a) (fee : β*z^2≤2) (β0 : 0≤β) (near : z≤2*g) :
    A^D*z^(q+2*(a*D)) ≤ factor n a D q*g^q := by
  calc
    _ ≤ ((1+(n:ℝ))*β^a)^D*z^(q+2*(a*D)) := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ A0 size _) (pow_nonneg zp.le _)
    _ = (1+(n:ℝ))^D*(β*z^2)^(a*D)*z^q := by
      rw [mul_pow,pow_add,←pow_mul,pow_mul z 2 (a*D),mul_pow]
      ring
    _ ≤ (1+(n:ℝ))^D*2^(a*D)*(2*g)^q := mul_le_mul
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg β0 (sq_nonneg z)) fee _) (by positivity))
      (pow_le_pow_left₀ zp.le near _) (pow_nonneg zp.le _) (by positivity)
    _ = _ := by rw [mul_pow]; dsimp only [factor]; ring

theorem at_fields (hG : G.Simple) (L : Layout F) (E : OPE.Services R.family f S)
    {n k N p t h : ℕ} (d : Fin n → ℕ) (w : (j : Fin n) → R.family.label (d j))
    {r g : ℝ} (gp : 0<g)
    (fit : 1/2≤R.family.path.levels.clock.hatBeta (L.level r)*g^2)
    (deep : L.level r≤k) (cut : k≤N) (grades : ∀j,R.family.ref (d j)≤L.level r)
    (zoom : R.family.S.a (L.level r)/R.family.S.a k ≤ R.family.path.levels.clock.hatBeta k^t)
    (massPrice : ∀j,mass R.family (d j) (L.shift (d j) r (w j))≤R.family.path.levels.clock.hatBeta (L.level r)^h)
    (D q : ℕ) :
    let C := R.family; let a := t*((∑j,d j)+1)+h
    (1+∑j,Spindle.paid C (d j) k N p (atRef L (d j) r (N,p) (w j)))^D *
      (regulatorRun C N p k)^(q+2*(a*D)) ≤ factor n a D q*g^q := by
  let C := R.family
  let a := t*((∑j,d j)+1)+h
  let b₀ := C.path.levels.clock.hatBeta (L.level r)
  let b := C.path.levels.clock.hatBeta k
  let z := regulatorRun C N p k
  let τ := C.path.β N p k
  let cost (j : Fin n) := Spindle.paid C (d j) k N p (atRef L (d j) r (N,p) (w j))
  have bp : 1≤b := (C.path.levels.fits.delayed k).le
  have b₀p : 1≤b₀ := (C.path.levels.fits.delayed _).le
  have bn := zero_le_one.trans bp
  have mono : b₀≤b := WilsonStartup.Timing.hat_mono C.path.levels (Gauge.slopeConstant_pos hG).le deep
  have lower : b/2≤τ := (R.makes.wilson.represents N p k cut).band.1
  have τp : 0<τ := by linarith only [bp,lower]
  have zp : 0<z := RG16.Literal.g_pos R.makes cut
  have eq : τ*z^2=1 := by
    change τ*(Real.sqrt τ)⁻¹^2=1
    rw [inv_pow,Real.sq_sqrt τp.le,mul_inv_cancel₀ τp.ne']
  have fee : b*z^2≤2 := by nlinarith only [eq,mul_le_mul_of_nonneg_right lower (sq_nonneg z)]
  have near : z≤2*g := by
    have bottom := (mul_le_mul_of_nonneg_right mono (sq_nonneg z)).trans fee
    change 1/2≤b₀*g^2 at fit
    have squares : z^2≤(2*g)^2 := (le_of_mul_le_mul_left (a:=b₀) (by nlinarith only [bottom,fit])
      (zero_lt_one.trans_le b₀p))
    exact (sq_le_sq₀ zp.le (mul_nonneg (by norm_num) gp.le)).mp squares
  have budgets (j : Fin n) : cost j≤b^a := by
    have jd := Finset.single_le_sum (f:=d) (fun _ _=>Nat.zero_le _) (mem_univ j)
    have order : t*(d j+1)+h≤a := Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.add_le_add_right jd _)) _
    have actual := WilsonReportRegularMoments.transported (N:=N) (p:=p) L E r (w j) (grades j) deep cut zoom
    apply actual.trans
    calc
      _ ≤ b^(t*(d j+1))*b^h := mul_le_mul_of_nonneg_left ((massPrice j).trans (pow_le_pow_left₀
        (zero_le_one.trans b₀p) mono _)) (pow_nonneg bn _)
      _ ≤ _ := (pow_add ..).symm.le.trans (pow_le_pow_right₀ bp order)
  have total : (∑j,cost j)≤(n:ℝ)*b^a :=
    (Finset.sum_le_sum (s:=univ) (fun j _=>budgets j)).trans_eq (by simp)
  have A0 : 0≤1+∑j,cost j := by
    have pos (j : Fin n) : 0≤cost j := Spindle.paid_pos C .. 
    linarith only [sum_nonneg (s:=univ) (fun j _=>pos j)]
  apply scalar n a D q A0 zp _ fee bn near
  nlinarith only [total,one_le_pow₀ (n:=a) bp]

end YM.Integration.WilsonReportFittedCurrency
end

