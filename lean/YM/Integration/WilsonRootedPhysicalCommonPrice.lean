import YM.Integration.WilsonRootedPhysicalTaylorPeriod
import YM.Integration.WilsonVacuumPreResetCurvatureReserve

/-! The exact five stage coefficients in the original housed Wilson wallet. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedPhysicalCommonPrice

open Function Filter Finset Set Lattice Wilson RG RG.Shoot Pressure
open Push Push.AbsoluteSums Push.AbsoluteSums.Animals Gas Ursell Trees Shoot Precision SectorMeasure Oriented
open AnalyticBridge VerifiedReset Collection Quotes PhysicalNext PhysicalNext.Repeat Legato
open ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.Blaze Blaze.March Captain
open Opera Height Beam Song Geo Greenbelt Next.Scheduling Extra.Iteration UVNext
open PriceCompiler Org Input Supply Pressure.Testing Time Roost Match Refrain WilsonStartup
open RG01Estimate RG01Estimate.CensusStep WilsonLimitConstruction.FundedCensusVacuum
open WilsonRootedPhysicalPathCover
open scoped Topology BigOperators Classical

def rent (G:Gauge)(p:BudgetPoint)(T:RG.Stage)(b:ℝ):Fin 5 → ℝ:=
  let v:=2*T.width/3
  let h i:=anchoredFee (headline p) i
  let high (k:ℕ)(c:ℝ):=turnFee p * (h (octave k) * (|factor| * (turnFee p * (highFee G k p v * c))))
  ![turnFee p,turnFee p*(h lowCount * (|factor| * b * (turnFee p * (lowFee G p v * lowerSize T.clip T.paths)))),
      high 3 T.paths,high 4 T.paths,high 2 1]

def load (p:BudgetPoint)(y Λ w:ℝ):Fin 5 → ℝ:=
  ![y^w,p.threshold^2,(2*y)*p.threshold^3,(2*y)*p.threshold^4,p.threshold^2*Λ]

def price (G:Gauge)(T:RG.Stage)(b:ℝ):ℝ:=
  ∑i,|rent G (regularPoint (Time.probe T)) T b i|

lemma postage {G:Gauge}{p q:BudgetPoint}(h:Meadow.cousin p q)(T:RG.Stage)(b:ℝ):
    rent G p T b = rent G q T b:=by
  obtain ⟨a,l,s,v⟩:=Meadow.postage (G:=G) (σ:=2*T.width/3) p q h
  funext i
  fin_cases i <;> simp [rent,a,l,s,v]

variable {G:Gauge}(R:Run G)

/-- No threshold, kinetic factor or old loop from the physical wallet was removed. -/
lemma billed (m:ℕ) :
    let a:=R.alloy.B.a
    let k:=a.params m
    let p:=regularPoint (a.budget m)
    let j:=a.clock.J (m+1)
    let i:=a.clock.J m
    let y:=a.clock.hatBeta (m+1)
    let b:=Pane.cloak R.rolls j
    WilsonRootedPhysicalLocalPeriod.wallet R m=
      ∑l,rent G (regularPoint (Time.probe k)) k b l*load p y (a.clock.loopCap m) (R.kit.expense j i).wanting l:=by
  intro a k p j i y b
  have h:Meadow.cousin p (regularPoint (Time.probe k)):=⟨rfl,rfl,rfl⟩
  rw [←postage h k b]
  simp only [WilsonRootedPhysicalLocalPeriod.wallet,rent,load,Fin.sum_univ_succ,
    Matrix.cons_val_zero,Matrix.cons_val_succ]
  dsimp [a,k,p,i,j,y,b]
  ring

/-- The original cutoff and theta range already give the coarse loop allowance. -/
lemma loop (a:Levels G)(m:ℕ)(hx:4≤a.clock.hatBeta m) : a.clock.loopCap m≤a.clock.hatBeta m:=by
  let x:=a.clock.hatBeta m
  have xx:0≤x:=by dsimp [x]; linarith
  have root:0<Real.sqrt x := Real.sqrt_pos.mpr (by dsimp [x]; linarith)
  have mon:1≤a.clock.monitor m:=Real.one_le_exp (sq_nonneg _)
  have hj:1≤(a.clock.J m:ℝ):=by exact_mod_cast (show 1≤a.clock.J m from (a.clock.adm m).trans' (by decide))
  have θ:a.clock.theta (a.clock.J m)≤1:=(a.fits.thetaRange m).2.trans (inv_le_one_of_one_le₀ hj)
  have cap:a.clock.monitor m ^ a.clock.theta (a.clock.J m) ≤ a.clock.monitor m:= by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le mon θ
  have t:(Real.sqrt x)⁻¹ * a.clock.monitor m ≤ 1 := (a.budget m).threshold_le
  have hm:a.clock.monitor m≤Real.sqrt x:=by
    rw [inv_mul_eq_div,div_le_iff₀ root,one_mul] at t
    exact t
  have hr:2≤Real.sqrt x:=by apply (Real.le_sqrt (by norm_num) xx).mpr; norm_num; exact hx
  change 2*(a.clock.monitor m)^a.clock.theta (a.clock.J m)≤x
  calc _ ≤ 2*Real.sqrt x := mul_le_mul_of_nonneg_left (cap.trans hm) (by norm_num)
       _ ≤ Real.sqrt x*Real.sqrt x:= mul_le_mul_of_nonneg_right hr root.le
       _ = x:=Real.mul_self_sqrt xx

/-- The fine temperature, path, and original threshold share a single date-wise bound. -/
lemma entries (p:BudgetPoint){x y Λ w:ℝ} (hx:4≤x)(hy:1≤y)(next:y≤2*x)(hΛ:0≤Λ)(upper:Λ≤x)
    (want:w≤0) (i:Fin 5):|load p y Λ w i| ≤ 4*x:=by
  have ht k:0≤p.threshold^k:=pow_nonneg p.threshold_pos.le k
  have hpow (k:ℕ):p.threshold^k≤1:= pow_le_one₀ p.threshold_pos.le p.threshold_le
  have hnext:0≤2*y:=by linarith
  have hw:y^w ≤ 1:=by simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hy want
  have one:1≤4*x:=by linarith
  fin_cases i
  · simpa [load,abs_of_nonneg (Real.rpow_nonneg (by linarith : 0≤y) w)] using hw.trans one
  · simpa [load,abs_of_nonneg (ht 2)] using (hpow 2).trans one
  · have h:2*y*p.threshold^3≤4*x:=by nlinarith only [mul_le_mul_of_nonneg_left (hpow 3) hnext,next]
    simpa [load,abs_of_nonneg (mul_nonneg hnext (ht 3))] using h
  · have h:2*y*p.threshold^4≤4*x:=by nlinarith only [mul_le_mul_of_nonneg_left (hpow 4) hnext,next]
    simpa [load,abs_of_nonneg (mul_nonneg hnext (ht 4))] using h
  · have h:p.threshold^2*Λ≤4*x:=by nlinarith only [mul_le_mul_of_nonneg_right (hpow 2) hΛ,upper,hx]
    simpa [load,abs_of_nonneg (mul_nonneg (ht 2) hΛ)] using h

theorem original (m:ℕ):
    let a:=R.alloy.B.a
    let x:=a.clock.hatBeta m
    let y:=a.clock.hatBeta (m+1)
    let j:=a.clock.J (m+1)
    let i:=a.clock.J m
    4≤x→y≤2*x→ (R.kit.expense j i).wanting≤0→price G (a.params m) (Pane.cloak R.rolls j)≤x→
    WilsonRootedPhysicalLocalPeriod.wallet R m≤7*x^2:=by
  intro a x y j i hx hy w hs
  let k:=a.params m
  let p:=regularPoint (a.budget m)
  let b:=Pane.cloak R.rolls j
  let f:=load p y (a.clock.loopCap m) (R.kit.expense j i).wanting
  let c:=rent G (regularPoint (Time.probe k)) k b
  have mon:0≤a.clock.monitor m := (Real.exp_pos _).le
  have cap:0≤a.clock.loopCap m:=mul_nonneg (by norm_num) (Real.rpow_nonneg mon _)
  have each (l:Fin 5):|f l|≤4*x:=entries p hx (a.fits.delayed (m+1)).le hy cap (loop a m hx) w l
  calc WilsonRootedPhysicalLocalPeriod.wallet R m = ∑l,c l*f l := billed R m
       _ ≤ ∑ l, |c l| * (4*x) := Finset.sum_le_sum (fun l _=>(le_abs_self _).trans (by rw [abs_mul];exact mul_le_mul_of_nonneg_left (each l) (abs_nonneg _)))
       _ = price G k b*(4*x) := (Finset.sum_mul ..).symm
       _ ≤ x*(4*x):=mul_le_mul_of_nonneg_right hs (by linarith)
       _ ≤ 7*x^2:=by nlinarith only [sq_nonneg x]

end YM.Integration.WilsonRootedPhysicalCommonPrice
