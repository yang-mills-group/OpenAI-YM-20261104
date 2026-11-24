import YM.Integration.WilsonPhysicalExteriorUniformCut

/-! The actual first-cut finite MS estimates on a compact inner shape and a
separately dilated compact exterior shape. Every marked occurrence is
placed on the original integer Wilson mesh by the original MS floor map. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorCompactWindow
open Filter Real Lattice RG RG16 PhysicalNext.Repeat.Legato
open MS MS.Dial MS.Menus MS.Land MS.Rake MS.Tide MS.Fleet MS.Tone
open FVA2 Register WilsonPhysicalExteriorMeshStops WilsonPhysicalExteriorFirstCut
open scoped Topology Classical

variable {G:Gauge} (R:Run G)
local notation "C₀" => R.family
local notation "Λ₀" => RG16.Lambda R.family.path.levels
local notation "s₀" => R.family.S.scale
local notation "B₀" => Press.portDeck G
local notation "M₀" => MS_Data G (Position.OpenAxis.Plot B₀)
private abbrev clock (c:ℝ) := WilsonPhysicalExteriorActualSides.time R c
private abbrev T (c':ℝ) := WilsonPhysicalExteriorFirstCutScale.ratio R c'

theorem recedes (hG:G.Simple) (slow:∀m:ℕ,((R.family.S.block m).val:ℝ)≤log (Λ₀ m))
    {c':ℝ} (h:1<c') : Tendsto (T R c') atTop atTop := by
  apply tendsto_exp_atTop.comp
  apply tendsto_atTop_mono' atTop _ (Literal.lambda_leads C₀ hG)
  have up:=((tendsto_rpow_atTop (sub_pos.mpr h)).comp (Literal.lambda_leads C₀ hG)).eventually_ge_atTop 2
  filter_upwards [up,far_window C₀ hG slow c'] with j hj ht
  have hp:=Literal.lambda_pos C₀ j
  have hl:=Literal.lambda_up C₀ j
  have prod:(Λ₀ j)^(c'-1)*(Λ₀ j)=(Λ₀ j)^c' := by
    nth_rw 2 [←rpow_one (Λ₀ j)]
    rw [←rpow_add hp,sub_add_cancel]
  change 2≤(Λ₀ j)^(c'-1) at hj
  have big:=mul_le_mul_of_nonneg_right hj hp.le
  rw [prod] at big
  have little:log (log (Λ₀ j))≤Λ₀ j :=
    (log_le_self (log_nonneg (by linarith))).trans (log_le_self hp.le)
  change Λ₀ j ≤ s₀ j-s₀ (far C₀ c' j)
  linarith only [big,little,ht.2.1]

def zoom (r:ℝ) (e:Bool) (x:QP) : QP := if e then r • x else x
def positions {n:ℕ} (c c':ℝ) (out:Fin n→Bool) (x:Fin n→QP) (i:Fin n) (j:ℕ) : Cover :=
  Dial.assign 0 (exp (clock R c j) • zoom (T R c' j) (out i) (x i))

private theorem rounding (E:ℝ) (x:QP) :
    ‖Tone.embed (Dial.assign 0 (E•x))-E•x‖≤1 := by simpa using Dial.Screen_price 0 (E•x)

private theorem round_upper {E:ℝ} (he:0≤E) (x:QP) :
    ‖Tone.embed (Dial.assign 0 (E•x))‖≤1+E*‖x‖ := by
  have hr:=norm_add_le (Tone.embed (Dial.assign 0 (E•x))-E•x) (E•x)
  rw [sub_add_cancel,norm_smul_of_nonneg he] at hr
  exact hr.trans (add_le_add (rounding E x) le_rfl)

private theorem round_lower {E δ:ℝ} (he:0≤E) (hδ:0<δ) (size:4≤E*δ)
    (x y:QP) (sep:δ≤‖x-y‖) :
    E≤(2/δ)*‖Tone.embed (Dial.assign 0 (E•x))-Tone.embed (Dial.assign 0 (E•y))‖ := by
  let X:=Tone.embed (Dial.assign 0 (E•x))
  let Y:=Tone.embed (Dial.assign 0 (E•y))
  have hh:=dist_triangle4 (E•x) X Y (E•y)
  simp only [dist_eq_norm] at hh
  rw [←smul_sub,norm_smul_of_nonneg he,norm_sub_rev (E•x) X] at hh
  have h₁:‖X-E•x‖≤1:=rounding E x
  have h₂:‖Y-E•y‖≤1:=rounding E y
  have hc:=mul_le_mul_of_nonneg_left sep he
  calc
    E≤(2*‖X-Y‖)/δ := (le_div_iff₀ hδ).mpr (by linarith only [hh,h₁,h₂,hc,size])
    _=_:=by ring

private theorem cross {r A δ:ℝ} (hr:0≤r) (big:A+δ≤r*δ)
    (x y:QP) (far:δ≤‖x‖) (bound:‖y‖≤A) : δ≤‖r•x-y‖ := by
  have tri:=norm_add_le (r•x-y) y
  rw [sub_add_cancel,norm_smul_of_nonneg hr] at tri
  linarith only [big,bound,tri,mul_le_mul_of_nonneg_left far hr]

theorem measured {n:ℕ} {I:Type} [Nonempty I] {hG:G.Simple} (M:M₀) (Q:Prescription B₀)
    (rows:WilsonPhysicalExteriorFirstCutPrice.Rows R M Q)
    (D:Fin n→Label B₀) (c c':ℝ) (out:Fin n→Bool) (x:I→Fin n→QP)
    (slow:∀m:ℕ,((R.family.S.block m).val:ℝ)≤log (Λ₀ m))
    (h₁:1<c') (h₂:c'<c) (h₃:c<2) (lo:ℕ→ℕ) (A δ:ℝ) (ha:0<A) (hδ:0<δ)
    (bounded:∀z i,‖x z i‖≤A) (radial:∀z i,out i=true → δ≤‖x z i‖)
    (apart:∀z i l,i≠l → out i=out l → δ≤‖x z i-x z l‖)
    (μ q:ℝ) (k h:ℕ) :
    ∀ᶠ j:ℕ in atTop,∀ z:I,∀ side:Bool,∀ p≥WilsonPhysicalExteriorActualSides.floor R c lo j,
      let err:=fun u:ℝ=>(T R c' j)^h*‖signed R M Q D c (positions R c c' out (x z)) side k u (j,p)‖
      err μ≤exp (-q*Λ₀ j) ∧ err (μ+R.family.S.scale j)≤exp (-q*Λ₀ j) := by
  apply WilsonPhysicalExteriorUniformCut.eventual R M Q rows D c c'
    (fun z=>positions R c c' out (x z)) slow h₁ h₂ h₃ lo (1+A) (2/δ) (by positivity) (by positivity) 2 _ μ q k h
  have up:=recedes R hG slow h₁
  have fine:=tendsto_exp_atTop.comp
    (WilsonPhysicalExteriorActualSides.time_up R hG (lt_trans zero_lt_one (h₁.trans h₂)))
  filter_upwards [up.eventually_ge_atTop 1,up.eventually_ge_atTop ((A+δ)/δ),
    fine.eventually_ge_atTop (4/δ),far_window C₀ hG slow c'] with j ht hb hprice hfar z
  let E:=exp (clock R c j)
  let r:=T R c' j
  have er:0≤r:=zero_le_one.trans ht
  have ep:0≤E:=(exp_pos _).le
  have bb:A+δ≤r*δ:=(div_le_iff₀ hδ).mp hb
  have ff:4≤E*δ:=(div_le_iff₀ hδ).mp hprice
  have re:r≤E:=exp_le_exp.mpr (hfar.2.2.trans ((rpow_le_rpow_of_exponent_le
    (by linarith only [Literal.lambda_up C₀ j]) h₂.le).trans (WilsonPhysicalExteriorActualSides.time_at_least R c j)))
  have e₁:1≤E:=ht.trans re
  constructor
  · intro i
    have spatial:‖zoom r (out i) (x z i)‖≤r*A := by
      cases hi:out i
      · exact (bounded z i).trans (le_mul_of_one_le_left ha.le ht)
      · simpa only [zoom,if_true,norm_smul_of_nonneg er] using mul_le_mul_of_nonneg_left (bounded z i) er
    calc
      _≤1+E*‖zoom r (out i) (x z i)‖:=round_upper ep _
      _≤1+E*(E*A):=add_le_add le_rfl (mul_le_mul_of_nonneg_left (spatial.trans (mul_le_mul_of_nonneg_right re ha.le)) ep)
      _≤(1+A)*E^2:=by nlinarith only [one_le_pow₀ (n:=2) e₁]
  · intro i l il
    apply round_lower ep hδ ff
    cases hi:out i <;> cases hl:out l
    · exact apart z i l il (hi.trans hl.symm)
    · change δ≤‖x z i-r•x z l‖
      rw [norm_sub_rev];exact cross er bb _ _ (radial z l hl) (bounded z i)
    · exact cross er bb _ _ (radial z i hi) (bounded z l)
    · change δ≤‖r•x z i-r•x z l‖
      rw [←smul_sub,norm_smul_of_nonneg er]
      exact (apart z i l il (hi.trans hl.symm)).trans (le_mul_of_one_le_left (norm_nonneg _) ht)

end YM.Integration.WilsonPhysicalExteriorCompactWindow
end
