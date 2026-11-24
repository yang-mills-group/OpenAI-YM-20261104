import YM.Integration.WilsonPhysicalExteriorNativeLog

/-! Reannouncement of individual finite Wilson fields at independently
chosen lengths, before applying the far detector. The normalized original
WilsonPoint and the common bare coupling substitution never change.
Untransported subtraction arguments produce a signed sum of one-fee
differences on this very regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorSlotReference
open Finset Real Lattice Labels Source Precision
open MS MS.Land MS.Menus MS.Rake MS.Logarithm
open RegulatorIR RegulatorIR.FVAAlt2 FVAAlt2 FVAAlt2.Lobby FVAAlt2.Billing
open PowerSeries (C)
open scoped Topology BigOperators Classical

variable {G:Gauge}{V:Frames G}{H:Hol G}{B:MS.Local.Physical.Deck G}{n:Side}
variable {W:Type} [LinearOrder W] [Fintype W]
variable (D:ChartRatio G)(R:Registry V H)(Q:Prescription B)(p:W→Label B)
local notation "PS" => PowerSeries ℂ

def engineering (eps:W→ℝ) (p:W→Label B) : ℂ := ∏ i, ((eps i:ℂ)⁻¹)^(p i).h

def original (y:ℝ) (v:W→ℝ) (x:W→Site n) : PS :=
  ∑ q:(i:W)→ Glyph B (p i).h, (∏ i,bore p Q (v i) i (q i)) *
    redo Q.team y (WilsonPoint D R n x (fun i=>owner (q i)))

def report (y:ℝ) (v eps:W→ℝ) (x:W→Site n) : PS :=
  ∑ q:(i:W)→ Glyph B (p i).h, (∏ i,changePrice Q (v i) p (eps i) i (q i)) *
    redo Q.team y ((C (engineering eps (fun i=>owner (q i))))*
      WilsonPoint D R n x (fun i=>owner (q i)))

private theorem fee_power (z:ℂ) (hz:z≠0) (a b:ℕ) :
    z^((a:ℤ)-(b:ℤ)) * (z⁻¹)^a=(z⁻¹)^b := by
  rw [zpow_sub₀ hz,zpow_natCast,zpow_natCast,inv_pow,inv_pow]
  field_simp

theorem factored (y:ℝ) (v eps:W→ℝ) (x:W→Site n) (ok:∀i,eps i≠0) :
    report D R Q p y v eps x=C (engineering eps p)*original D R Q p y v x := by
  rw [report,original,Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _=>?_
  let u:W→Label B:=fun i=>owner (q i)
  have redo_const (s:ℂ) (f:PS) : redo Q.team y (C s*f)=C s*redo Q.team y f := by
    rw [←PowerSeries.smul_eq_C_mul,map_smul,PowerSeries.smul_eq_C_mul]
  rw [redo_const]
  let A:PS:=∏ i,C ((eps i:ℂ)^(((u i).h:ℤ)-((p i).h:ℤ)))
  have cancel:A*C (engineering eps u)=C (engineering eps p) := by
    unfold A engineering
    rw [map_prod,map_prod,←Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _=>?_
    rw [←map_mul,fee_power _ (Complex.ofReal_ne_zero.mpr (ok i))]
  simp only [changePrice,Finset.prod_mul_distrib]
  change A*_*(C (engineering eps u)*_)=C (engineering eps p)*_
  rw [←cancel]
  ring

theorem common (y e:ℝ) (x:W→Site n) :
    report D R Q p y (fun _=>y) (fun _=>e) x=newEra D R Q y p x e := by
  unfold report newEra
  refine sum_congr rfl fun q _=>?_
  unfold Paid engineering wt
  rw [Finset.prod_pow_eq_pow_sum]

def ratio (eps:W→ℝ) (e:ℝ) (p:W→Label B) : ℂ := ∏i,((e:ℂ)/(eps i:ℂ))^(p i).h

omit [LinearOrder W] in
private theorem ratio_cost (eps:W→ℝ) (e:ℝ) (he:e≠0) :
    ratio eps e p * ((e:ℂ)⁻¹)^wt p = engineering eps p := by
  rw [ratio,engineering,wt,←Finset.prod_pow_eq_pow_sum,←Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _=>?_
  rw [←mul_pow]
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr he]

theorem aligned (y e:ℝ) (eps:W→ℝ) (x:W→Site n) (he:e≠0) (ok:∀i,eps i≠0) :
    report D R Q p y (fun _=>y) eps x=C (ratio eps e p)*newEra D R Q y p x e := by
  rw [factored D R Q p y _ eps x ok,tot_cost D R Q y p x e he,←mul_assoc,←map_mul,ratio_cost p eps e he]
  rfl

def replacement (y:ℝ) (v:W→ℝ) (x:W→Site n) : PS :=
  ∑ q:(i:W)→ Glyph B (p i).h, (∑i, (bore p Q (v i) i (q i)-bore p Q y i (q i)) *
    (∏ l ∈ Finset.univ.filter (fun l:W=>l < i),bore p Q y l (q l)) *
    (∏ l ∈ Finset.univ.filter (fun l:W=>i < l),bore p Q (v l) l (q l))) *
    redo Q.team y (WilsonPoint D R n x (fun i=>owner (q i)))

private theorem telescope (a b:W→PS) : (∏i,a i)-(∏i,b i)=∑i,
    (a i-b i)*(∏ l ∈ Finset.univ.filter (fun l:W=>l < i),b l)*
      (∏ l ∈ Finset.univ.filter (fun l:W=>i < l),a l) := by
  have hx:=Finset.prod_sub_ordered Finset.univ a (fun i=>a i-b i)
  simp only [sub_sub_cancel] at hx
  exact sub_eq_iff_eq_add.mpr (by rw [hx]; abel)

theorem changed (y e:ℝ) (v eps:W→ℝ) (x:W→Site n) (he:e≠0) (ok:∀i,eps i≠0) :
    report D R Q p y v eps x-C (ratio eps e p)*newEra D R Q y p x e=
    C (engineering eps p)*replacement D R Q p y v x := by
  rw [←aligned D R Q p y e eps x he ok,factored D R Q p y v eps x ok,
    factored D R Q p y (fun _=>y) eps x ok,←mul_sub]
  congr 1
  unfold original replacement
  rw [←Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _=>?_
  rw [←sub_mul,telescope]

theorem clocks (u θ:ℝ) (s:W→ℝ) (x:W→Site n) :
    report D R Q p (u-θ) (fun i=>(u+s i)-(θ+s i)) (fun i=>exp (-(θ+s i))) x =
      C (ratio (fun i=>exp (-(θ+s i))) (exp (-θ)) p)*newEra D R Q (u-θ) p x (exp (-θ)) := by
  simp only [add_sub_add_right_eq_sub]
  exact aligned D R Q p (u-θ) _ _ x (exp_ne_zero _) (fun _=>exp_ne_zero _)

end YM.Integration.WilsonPhysicalExteriorSlotReference
