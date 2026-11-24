import YM.FVA2.Lambda.Fields
/-!
# exact moment tables for jets of q integrals (∂a negative heat; integrate all terms rational)

 Recursion checked even. b₀ named local 1/(16π²). Distinguish manuscript b0.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Lambda.BranchR
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Heat MS.Heat.Signal MS.High MS.Tone MS.Tone.Frame MS.Color MS.Native
open MS.Book MS.Book.Convolve MS.Dock MS.Emit MS.Pearl
open MS.City MS.Plane.Flux
open Area Shells Pages
open Lathe Gaussian
open Complex (I)
open scoped Topology ContDiff BigOperators Classical InnerProductSpace ENNReal NNReal
variable {G:Gauge}{a:ℝ}
local notation "Z"=> Momentum.sq (A:=Axis)

abbrev αx:Axis→ℕ:=fun _=>0
abbrev αe:Axis→ℕ:=Gaussian.shift αx 0
abbrev αf:Axis→ℕ:=Gaussian.shift αx 1
abbrev αh:Axis→ℕ:=Gaussian.shift αf 0
open Lathe (prism)
abbrev spark (F:QP→ℝ→ℝ)(u:QP×ℝ):ℝ:= γ u.2 u.1 * u.2/2 * F u.1 u.2
lemma square_e (x:QP): ar αe x=(x 0)^2:= by rw [αe, Gaussian.crop, γ_norm]; simp
lemma square_f (x:QP): ar αf x=(x 1)^2:= by rw [αf,Gaussian.crop, γ_norm]; simp
lemma square_h (x:QP): ar αh x=(x 1)^2*(x 0)^2:= by rw [αh,Gaussian.crop,square_f ]

def petal (a:ℝ):ℝ:= b₀*(a*(23*a^2-4*a+23)/(1+a)^6)
lemma petalQ : Try (spark jewel) petal := by
    have h(a:ℝ)(ha:0≤a): tide αh a 2 * (10*a^3)+tide αf a 2 * (-5*a^2)+tide αh a 1 * (-20*a^2)+tide αh a 0 * (2*a)+tide αe a 1 * (-4*a)+tide αf a 1 * (3*a)+tide αx a 2 * (4*a)=b₀*(a*(23*a^2-4*a+23)/(1+a)^6):= by
        simp_rw [ jump ha _ 1, jump ha _ 0, tideV ha αf 0, tideV ha αx 0, tideV ha αx 1, basis₀ ha, wings αf 0,wings αx 0,wings αx 1,Szero ]; norm_num [shift, αf, αx, Axis ]; field_simp; ring
    have he : spark jewel=(fun (x:QP×ℝ)=> rock αh x.2 2 x.1* (10*x.2^3)+rock αf x.2 2 x.1* (-5*x.2^2)+rock αh x.2 1 x.1* (-20*x.2^2)+rock αh x.2 0 x.1* (2*x.2)+rock αe x.2 1 x.1* (-4*x.2)+rock αf x.2 1 x.1* (3*x.2)+rock αx x.2 2 x.1* (4*x.2)):= by funext x; unfold spark Lathe.jewel Lathe.prism rock; rw [square_f, square_h, square_e, γ_norm (q:=x.1) ]; ring
    rw [ he ]; refine Try.cost ?_ (fun a ha=>h a ha)
    exact ( on_f αh 2 (fun a:ℝ=>10*a^3) (by fun_prop) )|>.add (on_f αf 2 (fun a:ℝ=>-5*a^2) (by fun_prop) )|>.add (on_f αh 1 (fun a:ℝ=>-20*a^2) (by fun_prop) )|>.add (on_f αh 0 (fun a:ℝ=>2*a) (by fun_prop) )|>.add (on_f αe 1 (fun a:ℝ=>-4*a) (by fun_prop) )|>.add (on_f αf 1 (fun a:ℝ=>3*a) (by fun_prop) )|>.add (on_f αx 2 (fun a:ℝ=>4*a) (by fun_prop) )
def petalC (a:ℝ):ℝ:= b₀*(9*a/(2*(1+a)^4))
lemma petalCQ : Try (spark (fun q _=> Lathe.pulse q)) petalC := by
    have h(a:ℝ)(ha:0≤a): tide αx a 2 * (a)+tide αe a 1 * (-a)=b₀*(9*a/(2*(1+a)^4)):= by
        simp_rw [ jump ha _ 1, jump ha _ 0, tideV ha αx 0,basis₀ ha, wings αx 0,Szero]; norm_num [αx]; field_simp; ring
    have he : spark (fun q _=> Lathe.pulse q)=(fun (x:QP×ℝ)=> rock αx x.2 2 x.1* (x.2)+rock αe x.2 1 x.1* (-x.2)):= by funext x; unfold spark Lathe.pulse rock; rw [ square_e, γ_norm (q:=x.1)]; ring
    rw [ he ]; refine Try.cost ?_ (fun a ha=>h a ha)
    exact ( on_f αx 2 (fun a:ℝ=>a) (by fun_prop) )|>.add (on_f αe 1 (fun a:ℝ=>-a) (by fun_prop) )
end YM.FVA2.Lambda.BranchR
