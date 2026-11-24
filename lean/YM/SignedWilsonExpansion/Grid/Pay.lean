import YM.SignedWilsonExpansion.Grid.Curtain
namespace YM.SignedWilsonExpansion.Overlap.Curtain
/-! Price at shell t=0 of logarithmic mark scale derivative. No integrations
by parts at zero/puncture needed to eliminate weights derivatives. A finite
linear form in explicit `basis₀` Gaussian moments once a function identity is
differentiated *twice*. -/
set_option autoImplicit false
noncomputable section
open Function Set Filter MeasureTheory Finset
open MS MS.Menus MS.Local.Physical MS.Land MS.Book MS.Landau MS.Landau.Detect MS.Koszul MS.Plane MS.Plane.Flux MS.High MS.Plane.Domain MS.Plane.Wire MS.Pearl MS.Outlook MS.Emit MS.Heat MS.Rake
open MS.Garment MS.Motif MS.Halo MS.Arts MS.Tone MS.City
open FVA2 FVA2.Lambda Area Walk Bubble TreeLine TreeView HighRank HighScale MarkRows AxisChoice
open Gaussian Radial
open scoped Classical Topology ContDiff BigOperators
local notation "Z" => Momentum.sq
local notation "F" => FourP
local notation "A" => Axis
local notation "μ" => covMeasure Axis
local notation "h₀" => amp 0
local notation "φ" => fun (X:ℝ)=> Real.exp (-X)
local notation "g" => deriv (amp 0)
local notation "j" => deriv (deriv (amp 0))
lemma calm (X:ℝ): HasDerivAt φ (-φ X) X:= by convert! ( ( hasDerivAt_id' X ).neg.exp ) using 1; simp
lemma glow (X:ℝ): HasDerivAt h₀ (g X) X:= ( ( TorchE.smooth_amp (t:=0) ).differentiable (by simp) X ).hasDerivAt
lemma along_c (X:ℝ): g X*X^2+h₀ X*( 2*X )=X*φ X/2 := by
    have hf:= ( ( glow X ).fun_mul ( ( hasDerivAt_id' X ).pow 2 ) ); have hZ:= ( ( ( hasDerivAt_id' X ).const_add 1 ).fun_mul ( calm X ) ).const_sub 1|>.div_const 2
    simp only [Pi.pow_apply] at hf; rw [ show (fun x:ℝ=> amp 0 x * x^2)=(fun x=> (1-(1+x)*φ x)/2 ) from funext capital ] at hf; obtain h:=hf.unique hZ; beta_reduce at h
    linear_combination h
lemma along_s (X:ℝ): j X*X^2+4*X*g X+2*h₀ X=( 1-X )*φ X/2:= by
    have hc : ContDiff ℝ ∞ g:= by apply ContDiff.deriv'; simpa using ( TorchE.smooth_amp (t:=0) )
    let x:=hasDerivAt_id' X; have h : HasDerivAt g ( j X ) X := ( hc.differentiable (by simp) X ).hasDerivAt
    have hv:= ( h.fun_mul (x.pow 2) ).fun_add (( glow X ).fun_mul ( x.const_mul 2 )); have ht:= ( x.fun_mul ( calm X ) ).div_const 2
    simp only [Pi.pow_apply] at hv; rw [ show (fun x:ℝ=> g x*x^2+ amp 0 x*(2*x))=( fun x=> x*φ x/2) from funext along_c ] at hv; obtain hu:= hv.unique ht; beta_reduce at hu
    linear_combination hu
-- direct algebra preventing singular rate formula exterior at X=0
private lemma bigNote (X:ℝ) :
   2*φ X * claim h₀ X=20/3*X^3*(φ X)^2 -40/3*X^2*(φ X)^2 -58*X^2*(φ X)^3+ 328/3*X*(φ X)^2-116*X*(φ X)^3 -154/3*φ X+328/3*(φ X)^2-58*(φ X)^3 := by
    -- separate alpha0 h² and linear weights.
    have ht : 2*φ X*claim h₀ X=-8/3*φ X * (87*(h₀ X*X^2)^2 +5*( X^2*( (1-X)*φ X/2 ) )+5*( (g X*X^2+h₀ X*(2*X))*X ) -5*(h₀ X*X^2) ) := by
       -- coefficient? h''X4+4*gX3+2*hX2 ; weighted leaves (+5gX3+5hX²) add 5*(+2h)-5h yes
       rw [ ← along_s ]; unfold claim; ring
    rw [ ht ]
    rw [ capital X, along_c X ]; ring
-- weighted radial price
open Lathe (γ)
local notation "κ" => (fun _: Axis=>(0:ℕ))
-- Avoid HAB unresolved private Lean name `Pin`.
def dayQ (p:F) :ℝ := 20/3*rock κ 1 3 p + (-40/3)*rock κ 1 2 p + (-58)*rock κ 2 2 p+328/3*rock κ 1 1 p + (-116)*rock κ 2 1 p +(-154/3)*rock κ 0 0 p+328/3*rock κ 1 0 p+(-58)*rock κ 2 0 p
variable {G:Gauge}
lemma counted (p:F): feeQ G 0 p= ↑( G.casimir*dayQ p ):= by
    apply congr_arg ((↑):ℝ→ℂ); let X:= Z p
    have hZ: Shells.hot 0 X=φ X:= by simp [Shells.hot]; -- maybe parser
    have ht(t:ℝ): γ t p= Real.exp (-(1+t)*X):= rfl
    have he₂: γ 2 p=(φ X)^3:= by rw [ht, show -(1+2:ℝ)*X= -X + -X + -X from (by ring), Real.exp_add,Real.exp_add]; ring
    have he₁: γ 1 p=(φ X)^2:= by rw [ht, show -(1+1:ℝ)*X= -X + -X from by ring, Real.exp_add]; ring
    have he₀: γ 0 p=φ X:= by rw [ht]; ring_nf
    have he: dayQ p=2*φ X*claim h₀ X:= by unfold dayQ rock; rw [bigNote X, he₂,he₁,he₀]; simp only [γ_norm]; unfold X; ring
    rw [← show X=Z p from rfl,hZ,he]; ring
lemma income (t:ℝ)(n:ℕ): (∫ p:F, rock κ t n p ∂μ)= tide κ t n:= rfl
lemma stored : (∫ p:F,dayQ p∂μ)= -16*b₀:= by
    -- turnkey moment linear form
    let c (t:ℝ) (a:ℝ) (n:ℕ) (p:F):= t*rock κ a n p
    have hv (t:ℝ)(a:ℝ)(n:ℕ)(ha:0≤a): Integrable (c t a n) μ:= ( gram ha κ n ).const_mul _
    let x:= c (20/3) 1 3; let y:= c (-40/3) 1 2; let z:=c (-58) 2 2; let u:= c (328/3) 1 1; let k:=c (-116) 2 1; let r:=c (-154/3) 0 0; let q:=c (328/3) 1 0; let f:= c (-58) 2 0
    have hx:Integrable x μ:=hv _ _ _ (by norm_num); have hy:Integrable y μ:=hv _ _ _ (by norm_num); have hz:Integrable z μ:=hv _ _ _ (by norm_num); have hu:Integrable u μ:=hv _ _ _ (by norm_num); have hk:Integrable k μ:=hv _ _ _ (by norm_num); have hr: Integrable r μ:=hv _ _ _ (by norm_num); have hq: Integrable q μ:=hv _ _ _ (by norm_num); have hf:Integrable f μ:=hv _ _ _ (by norm_num)
    have hL: Integrable (x+y+z+u) μ:=(( hx.add hy ).add hz).add hu
    change (∫ p,(x+y+z+u+k+r+q+f) p∂μ)=_; rw [ integral_add' ((( hL.add hk ).add hr).add hq) hf, integral_add' (( hL.add hk ).add hr ) hq, integral_add' (hL.add hk) hr, integral_add' hL hk, integral_add' (( hx.add hy ).add hz) hu, integral_add' (hx.add hy) hz, integral_add' hx hy ]
    unfold x y z u k r q f c; simp (disch:=norm_num) only [ integral_const_mul, income ]; rw [Gaussian.jump (n:=2) (by norm_num : 0≤(1:ℝ)), Gaussian.jump (n:=1) (by norm_num : 0≤(1:ℝ)), Gaussian.jump (n:=1) (by norm_num : 0≤(2:ℝ)), Gaussian.jump (n:=0) (by norm_num : 0≤(1:ℝ)),Gaussian.jump (n:=0) (by norm_num : 0≤(2:ℝ)) ]; simp (disch:=norm_num) only [basis₀,Szero]; ring
variable {B:Land.Booked (Press.portDeck G)}(M: MS_Data G B)(η:G.Simple) (a:G.ColorIndex)(t:ℝ)
include η
lemma paycheck : assayAct a (trigger M (t,0))= ↑((-16*b₀)* G.casimir):= by
   rw [ trigger,crossAct M η a (t,0) ]; change (∫ p:F, atBoth p G 0∂μ)= _; rw [rewarded M η a 0]; simp_rw [ counted, Complex.ofReal_mul ]; rw [ integral_const_mul, integral_complex_ofReal,stored ]; push_cast; ring
end
end YM.SignedWilsonExpansion.Overlap.Curtain
