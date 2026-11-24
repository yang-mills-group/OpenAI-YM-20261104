import YM.Integration.WilsonPhysicalExteriorMSQuadrature
import YM.Integration.WilsonPhysicalExteriorCompactWindow

/-! In an exterior coordinate the genuine first ultraviolet spacing is
divided by T. Both the physical side and the independently prescribed IR
side satisfy the historical mesh conditions at that precise clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorQuadratureClock
open Function Filter Set Finset Real Metric MeasureTheory Lattice RG RG16 MS MS.Tide MS.Orbit MS.Dial MS.Fleet MS.Land MS.Rake MS.Vista
open XSpace XSpace.Cirrus XSpace.Structure1 FVA2 FVA2.Register
open WilsonPhysicalExteriorMeshStops WilsonPhysicalExteriorActualSides WilsonPhysicalExteriorFirstCutScale
open WilsonPhysicalExteriorMSQuadrature
open scoped Topology BigOperators Classical
variable {G:Gauge} (R:PhysicalNext.Repeat.Legato.Run G)
local notation "Λ" => RG16.Lambda R.family.path.levels
local notation "C₀" => R.family
local notation "σ" => R.family.S.scale
def sideIndex (c:ℝ) (physical:Bool) (z:ℕ×ℕ):ℕ :=
  if physical then actual R (ultraviolet C₀ c z.1) z.2 else WilsonPhysicalExteriorPrescribedSide.count (Λ z.1)

def period (c:ℝ) (physical:Bool) (z:ℕ×ℕ):XSpace.Period where
  side := dimT walkway (sideIndex R c physical z)
  even := by rw [fullC];omega
  large := by rw [fullC];omega

def age (c c':ℝ) (exterior:Bool) (j:ℕ): ℝ :=
  WilsonPhysicalExteriorActualSides.time R c j+if exterior then σ j-σ (far C₀ c' j) else 0

def grid (c c':ℝ) (exterior physical:Bool) (z:ℕ×ℕ):Mesh:=
  ⟨period R c physical z,exp (-age R c c' exterior z.1),exp_pos _⟩

theorem actual_period (c:ℝ) (z:ℕ×ℕ) : (period R c true z).side=R.family.side (ultraviolet C₀ c z.1) z.2 :=
  PNat.eq (side_value R _ _)

theorem outer_spacing (c c':ℝ) (physical:Bool) (z:ℕ×ℕ) :
    (grid R c c' true physical z).spacing=exp (-(WilsonPhysicalExteriorActualSides.time R c z.1))/ratio R c' z.1 := by
  change exp (-(WilsonPhysicalExteriorActualSides.time R c z.1+(σ z.1-σ (far C₀ c' z.1))))=_
  rw [neg_add_rev,exp_add,exp_neg,ratio,div_eq_inv_mul]

private theorem scale_bound (hG:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ m))
    {c c':ℝ} (h₁:1<c') (h₂:c'<c) (exterior:Bool) :
    ∀ᶠ j:ℕ in atTop,WilsonPhysicalExteriorActualSides.time R c j≤age R c c' exterior j ∧ age R c c' exterior j≤4*(Λ j)^c := by
  filter_upwards [time_at_most R hG slow (h₁.trans h₂).le,far_window C₀ hG slow c'] with j ht hf
  have hf₀:= (OPE.scale_mono R.family.S).monotone hf.1
  have hpow:=rpow_le_rpow_of_exponent_le (show 1≤Λ j from by linarith [Literal.lambda_up C₀ j]) h₂.le
  have pos:0≤(Λ j)^c:=rpow_nonneg (Literal.lambda_pos C₀ j).le _
  cases exterior <;> simp only [age,Bool.false_eq_true,if_false,if_true] <;> constructor <;> linarith [hf.2.2]

private theorem size_bound (c:ℝ) (lo:ℕ→ℕ) (physical:Bool) :
    ∀ᶠ z in channel R c lo,exp ((Λ z.1)^2)≤((period R c physical z).side.val:ℝ) := by
  have late:∀ᶠ z in channel R c lo,floor R c lo z.1≤z.2:=mem_inf_of_right (by simp)
  filter_upwards [late] with z hz
  have h:=Nat.le_ceil (exp ((Λ z.1)^2))
  change exp ((Λ z.1)^2)≤(WilsonPhysicalExteriorPrescribedSide.count (Λ z.1):ℝ) at h
  apply h.trans;apply Nat.cast_le.mpr
  cases physical
  · change _≤(dimT walkway (WilsonPhysicalExteriorPrescribedSide.count (Λ z.1))).val
    rw [fullC];omega
  · rw [actual_period]
    have hm:= (le_max_right _ _).trans hz
    have hl:= (R.family.S.period_strict.id_le z.2).trans
      (Nat.le_mul_of_pos_right _ (R.family.S.denominator (ultraviolet C₀ c z.1)).pos)
    change 4*(WilsonPhysicalExteriorPrescribedSide.count (Λ z.1)+1)≤z.2 at hm
    exact (by omega : WilsonPhysicalExteriorPrescribedSide.count (Λ z.1)≤z.2).trans hl

theorem front (hG:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ m))
    {c c':ℝ} (h₁:1<c') (h₂:c'<c) (h₃:c<2) (lo:ℕ→ℕ) (exterior physical:Bool) :
    Tendsto (grid R c c' exterior physical) (channel R c lo) Front := by
  let L:=channel R c lo
  have first:=taking R c lo
  have range:=scale_bound R hG slow h₁ h₂ exterior
  have age_up:Tendsto (age R c c' exterior) atTop atTop:=
    tendsto_atTop_mono' atTop (range.mono (fun _ h=>h.1)) (time_up R hG (by linarith : 0<c))
  have sure:=age_up.comp first
  refine goesFront ⟨?_,?_⟩
  · exact tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp sure)
  intro k
  have X:=((tendsto_rpow_atTop (by linarith :0<2-c)).comp (Literal.lambda_leads C₀ hG)).eventually_ge_atTop (4*((k:ℝ)+1))
  apply tendsto_atTop_mono' L _ (tendsto_exp_atTop.comp sure)
  filter_upwards [first.eventually range,first.eventually X,size_bound R c lo physical] with z hr hx hp
  let v:=age R c c' exterior z.1
  have h:((k:ℝ)+1)*v≤(Λ z.1)^2 := calc
    _≤((k:ℝ)+1)*(4*(Λ z.1)^c):=mul_le_mul_of_nonneg_left hr.2 (by positivity)
    _≤(Λ z.1)^(2-c)*(Λ z.1)^c:=by rw [←mul_assoc,mul_comm ((k:ℝ)+1)];exact mul_le_mul_of_nonneg_right hx (rpow_nonneg (Literal.lambda_pos C₀ z.1).le _)
    _=_:=by rw [←rpow_add (Literal.lambda_pos C₀ z.1),sub_add_cancel];norm_num
  change exp v≤(exp (-v))^k*((period R c physical z).side.val:ℝ)
  rw [←exp_nat_mul]
  apply (mul_le_mul_of_nonneg_left hp (exp_pos _).le).trans' ?_
  rw [←exp_add];exact exp_le_exp.mpr (by linarith only [h])

/-- A single cutoff before all scales and normalized tests. The independent
filed continuum field appears on BOTH sides of the signed quadrature. -/
theorem measured {hG:G.Simple} (N:WilsonPrescription G)
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {S:Land.Prescription (Press.portDeck G)} {dial:Bool} (issued:Main.Match N hG M S dial)
    {n d:ℕ} (p:Tags G d n) (k:ℕ) (K:Set (Points n)) (hc:IsCompact K) (sep:K⊆conf n)
    (slow:∀m,((R.family.S.block m).val:ℝ)≤log (Λ m)) {c c':ℝ} (h₁:1<c') (h₂:c'<c) (h₃:c<2)
    (lo:ℕ→ℕ) (h:ℕ) (budget q:ℝ) :
    ∀ᶠ j:ℕ in atTop,∀exterior physical:Bool,∀per≥floor R c lo j,
      ∀f:Test n,tsupport f⊆K→∀b:ℝ,TestBudget.Bound f b→∀ν:ℝ,1+|ν|≤exp (budget*Λ j)→
      (ratio R c' j)^h*‖quadrature (grid R c c' exterior physical (j,per)) f
        (fun x=>Dframe.meteor ν M d x k p)-FVA2.Reg.CoverTest.Rates ν M d k n f p‖≤b*exp (-q*Λ j) := by
  obtain ⟨A,hA,e,purchase⟩:=independent N issued p k K hc sep
  have g (a s:Bool):=all_later R (c:=c) (lo:=lo) ((front R hG slow h₁ h₂ h₃ lo a s).eventually purchase)
  have sup:=Filter.eventually_all.mpr fun a:Bool=>Filter.eventually_all.mpr (g a)
  have bill:=at_fixed R hG (h₁.trans h₂) h₂ slow 0 A (q+budget*(e:ℝ)) hA.le 0 h
  have geo:=Filter.eventually_all.mpr fun a:Bool=>scale_bound R hG slow h₁ h₂ a
  filter_upwards [sup,bill,geo] with j hj hh hg a s per hp f supp b hf ν hν
  have tiny:=hj a s per hp f supp b hf ν
  let v:=age R c c' a j
  have hs:(grid R c c' a s (j,per)).spacing^mildG ≤ exp (-mildG*WilsonPhysicalExteriorActualSides.time R c j):=by
    change (exp (-v))^mildG ≤ _
    rw [←exp_mul];apply exp_le_exp.mpr
    have h : 0 < MS.Tide.mildG := MS.Tide.mild_p
    nlinarith only [mul_le_mul_of_nonneg_left (hg a).1 h.le]
  have he: (1+|ν|)^e≤exp ((budget*(e:ℝ))*Λ j):=by
    rw [show budget*(e:ℝ)*Λ j=(e:ℝ)*(budget*Λ j) by ring,exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) hν e
  simp only [pow_zero,mul_one] at hh
  have hb:=TestBudget.bound_nonneg f hf
  have non: 0≤(grid R c c' a s (j,per)).spacing^mildG:=Real.rpow_nonneg (grid R c c' a s (j,per)).positive.le _
  have ht:0≤(ratio R c' j)^h:=pow_nonneg (exp_pos _).le _
  calc
    _≤(ratio R c' j)^h*(b*(A*(1+|ν|)^e*(grid R c c' a s (j,per)).spacing^mildG)):=mul_le_mul_of_nonneg_left tiny ht
    _≤(ratio R c' j)^h*(b*(A*exp (budget*(e:ℝ)*Λ j)*exp (-mildG*WilsonPhysicalExteriorActualSides.time R c j))):=by gcongr
    _=b*(exp (budget*(e:ℝ)*Λ j)*((ratio R c' j)^h*(A*exp (-mildG*WilsonPhysicalExteriorActualSides.time R c j)))):=by ring
    _≤b*(exp (budget*(e:ℝ)*Λ j)*exp (-(q+budget*(e:ℝ))*Λ j)):=by gcongr
    _=_:=by rw [←exp_add];congr 2;ring

end YM.Integration.WilsonPhysicalExteriorQuadratureClock
end
