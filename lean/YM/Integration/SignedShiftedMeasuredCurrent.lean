import YM.Integration.SignedMeasuredSourceBudget
import YM.WilsonCoeffUV.Horizon.OrbitShift
import YM.Next.RANK.Anglo

/-! Moving the chosen root retains the actual original torus Wilson configuration in each native bank. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.SignedShiftedMeasuredCurrent
open Function Filter Finset Lattice Laurent Wilson RG Precision Exterior Tree Bloch Matrix PowerSeries
open FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary
open WilsonCoeffUV.Bank.Mosaic.Near
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {c f : Side} (S : StepData c f) (F : Forest S.ratio) (M : Matrix (Woods G f) (Woods G c) ℝ) (ρ : fieldDir G c 1→ AxisChart G F)
variable {ι I : Type} [DecidableEq ι] {D : ι→ℕ} {J : Finset ι} {k r : ℕ}

def shift (o : Cover) := spear (jog (wrap f o) : Equiv.Perm (Woods G f))

/-- Literal translation of the original field leg at every periodic site and configuration. -/
theorem meter_at (T : Atom G r) (o:Cover) (v:Lawn (Woods G f)) : meter T (0:Site f) (shift o*ᵥv)=meter T (wrap f o) v := by
  unfold meter shift
  rw [mantle_input,mantle_reads,mantle_input]
  unfold Atom.unmasked
  exact congrArg T.poly (funext fun i=>Next.Rank.Alarm.l_shift (T.leg i) (wrap f o) (mantle v))

private theorem starts (T : Atom G r) (a : Site f) : (X:Ink (Woods G f))^r*Blue.flash (sprig (meter T a) r)=jet (meter T a) := by
  apply moves;intro n hn
  have hn' := (rays_jet ((meter_hot T a).contDiffAt (x:=0)).analyticAt r).mp (meter_shell T a) n hn
  rw [jet_apply]
  have hz : rye (meter T a) n=0 := funext fun u=>by rw [rye,hn'];simp
  rw [hz,map_zero]

theorem sprig_at (T : Atom G r) (o:Cover) : loom (shift (G:=G) (f:=f) o) (Blue.flash (sprig (meter T (0:Site f)) r))=Blue.flash (sprig (meter T (wrap f o)) r) := by
  apply mul_left_cancel₀ (a:=(X:Ink (Woods G f))^r) (pow_ne_zero _ X_ne_zero)
  rw [starts,show (X:Ink (Woods G f))^r=loom (shift o) (X^r) by simp [loom],←map_mul,starts,loom_jet _ _ (meter_hot ..).contDiffAt]
  exact congrArg jet (funext (meter_at T o))

omit [DecidableEq ι] in
/-- Arbitrary native root and independent multivariate test. The inherited shift is realized at `wrap f o` on the genuine arbitrary torus. -/
theorem cleared (P:Comet G (Pen D J) r) (a:Case D) (o:Cover) (e b t:ℕ) (ht:b+e=r+t) (hk:r≤k+e) (hp:shadeStar P)
    (hM : M=reveal G S F*((reveal G S F).transpose*M)) (hρ:ContDiffAt ℝ ω ρ 0) (h0:ρ 0=0) :
    (X:Ink (Active G F⊕Woods G c))^b* SignedMeasuredSourceSeries.probe S F M ρ (readO a (shifted (volumeR P e) o) f)=
    X^t*jet (fun u:Sloc S F G=>(dip P (touch a J)).unmasked (Work.F03.live F (SignedMarkedChartGerm.chart S F ρ u)) (wrap f o)) := by
  let T:=dip P (touch a J)
  have hs : readO a (volumeR P e) f=(X:Ink (Woods G f))^e*Blue.flash (sprig (meter T (0:Site f)) r) := by
    change flash (ply (touch a J).toLinearMap ((volumeR P e).1 f))=_
    rw [volume_probe];ext1 i;rw [coeff_X_pow_mul'];unfold Blue.flash;simp only [coeff_mk];split_ifs <;> simp [T,totalR]
  rw [transportPage _ (aug_auth P hp hk),hs,map_mul,map_pow]
  change X^b*SignedMeasuredSourceSeries.probe S F M ρ ((loom (shift o) X)^e * loom (shift o) (Blue.flash (sprig (meter T (0:Site f)) r)))=_
  rw [sprig_at]
  have hX: SignedMeasuredSourceSeries.probe S F M ρ (loom (shift o) X)=X := by simp [SignedMeasuredSourceSeries.probe,retool,loom,reroll_X]
  have ht' := SignedMarkedChartGerm.atom S F M ρ T (wrap f o) hM hρ h0
  rw [map_mul,map_pow,hX,←mul_assoc,←pow_add,ht,pow_add,mul_assoc]
  rw [mul_left_comm (X^r),show X^r*SignedMeasuredSourceSeries.probe S F M ρ _=_ from ht']

private theorem shifted_train (o:Cover) : (SignedMeasuredSourceSeries.probe S F M ρ).comp (loom (shift o))=
    train (fun i=>SignedMeasuredSourceSeries.probe S F M ρ (loom (shift o) (path i))) := by
  apply rail
  · simp [SignedMeasuredSourceSeries.probe,loom,retool,reroll_X]
  · intro q
    change SignedMeasuredSourceSeries.probe S F M ρ (loom (shift o) (realS q))=realS q
    rw [loom_real,SignedMeasuredSourceSeries.genuine,train_real]

omit [DecidableEq ι] in
/-- The actual single rooted source paid before all tests is summed through arbitrary numerical measurements of its entire native polynomial. -/
theorem measured (T : I→ Comet G (Pen D J) r) {u budget : ℝ} (hu:0<u) (bill:SumBudget (fun i=>integerP (T i) u) budget)
    (hs:∀i,shadeStar (T i)) (e b t : ℕ) (hk:r≤k+e) (ht:b+e=r+t) (hM:M=reveal G S F*((reveal G S F).transpose*M))
    (hρ:ContDiffAt ℝ ω ρ 0) (h0:ρ 0=0) (a:Case D) (o:Cover) (n:ℕ) (L:POL (Active G F⊕Woods G c)→ₗ[ℝ]ℝ) :
    HasSum (fun i=>L (coeff (b+n) ((X:Ink (Active G F⊕Woods G c))^t*jet (fun z:Sloc S F G=>
      (dip (T i) (touch a J)).unmasked (Work.F03.live F (SignedMarkedChartGerm.chart S F ρ z)) (wrap f o)))))
      (L (coeff n (SignedMeasuredSourceSeries.probe S F M ρ (readO a (shifted (bolus T e) o) f)))) := by
  let δ := (SignedMeasuredSourceSeries.probe S F M ρ).comp (loom (shift o))
  have h : HasSum (fun i=>L (coeff n (δ (readO a (volumeR (T i) e) f)))) (L (coeff n (δ (readO a (bolus T e) f)))) := by
    rw [show δ=train _ from shifted_train S F M ρ o]
    apply SignedMeasuredSourceSeries.clock (k:=k)
    · exact fun i=>ply_shell _ ((aug_auth (T i) (hs i) hk).span f)
    · exact ply_shell _ ((stars hu bill hk hs).span f)
    · exact fun i j x=>(touch a J).hasSum (elevated hu bill e f i j x)
  rw [transportPage _ (stars hu bill hk hs)]
  apply h.congr_fun;intro i
  rw [←cleared S F M ρ (T i) a o e b t ht hk (hs i) hM hρ h0,coeff_X_pow_mul',if_pos (Nat.le_add_right b n),Nat.add_sub_cancel_left,transportPage _ (aug_auth (T i) (hs i) hk)]
  rfl

end YM.Integration.SignedShiftedMeasuredCurrent
