import YM.RGComparison.Core16.Stem.Birth
/-!
# Calculating true launch posterior stencil coefficients

Full tensor convention geometry Ω positive; OFFSET in this use NONE. Input at coupling-sensitive
normalized reference of parent level g. This bridges same-phase unmasked RG point after integration,
not at Pole of continuum output! Need registration Γ_4 stage clocks. Math proof on actual regulator.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Lumen.Fk
open Function Filter Set Lattice RG Tree Wilson MeasureTheory Pressure Metric Push.Uniform Forge
open PertExtension PertExtension.Series Tested Radial Therm Precision
open Planet
open scoped Topology ContDiff BigOperators Classical InnerProductSpace Matrix.Norms.Frobenius
variable {G:Gauge}{S:Side} {ι k L T A D:Type} [Fintype ι][Fintype k][Fintype T][Fintype D][Fintype L]
variable {X:Shelf G A D} (P: Planet X S ι k T) (Z:ChartRatio G)
local notation "μ"=> Chart.tangent G ι
local notation "λ#"=> skillet G ι

def vacant : Stuff G ι Empty:=fun j=> j.elim

def birth := harvest P Z vacant (fun _=>1)
def valuation (p: Stuff G ι L) (ψ :(L→G.Color)→ℝ) := divide (harvest P Z p ψ) (birth P Z)
def read (Z:ChartRatio G) (p:Stuff G ι L) (ψ:(L→G.Color)→ℝ)(a:ℕ)(i:ℕ):= valuation P Z p ψ (a+i)
variable {P Z} (H:P.Steady)(hZ:LocalRatio Z)
include H hZ
omit H hZ [Fintype T] [Fintype D] in
private lemma founding (x:ℝ×(ι→G.Color)): normTerm (cap Z vacant (fun _=>1)) (rise P) 0 x= Chart.jacobian Z (0: ι → G.Color) * Radial.kernel (rise P) x:= by
    have h:(Finset.antidiagonal 0 : Finset (ℕ×ℕ))={((0,0):ℕ×ℕ)}:= by ext ⟨x,y⟩; simp only [Finset.mem_antidiagonal,Finset.mem_singleton,Prod.mk.injEq];omega
    simp [normTerm,integrandSeries,Zone.mul,h,expsum,Zone.TaylorPow,cap]
lemma basis_fee : 0<birth P Z 0:=by
    let y:=Chart.jacobian Z (0:ι→ G.Color); have hz : 0<y := Finset.prod_pos fun i _=> (show 0< Chart.fee Z 0 from lt_max_of_lt_left (by rw [hZ.anchored,mul_one]; exact hZ.scale))
    have hp:= affordability (K:=cap Z (ι:=ι) vacant (fun _=>1)) μ (rise P) 0 1 (Fk.sturdy H) ((cap_hot hZ _ (ψ:=fun _ : Empty→ G.Color=>1) contDiffAt_const).of_le le_top) (prepared H)
    simp_rw [founding] at hp
    unfold birth harvest; rw [stamp_moment]; simp_rw [founding,integral_const_mul]; apply mul_pos hz; apply integral_exp_pos; exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hz.ne') _).mp hp

variable {f:Melody G ι}{p:Stuff G ι L}{ψ:(L→G.Color)→ℝ}{N:ℕ}{c:ℝ}
    (hF:Visible X ψ f p N c)(hψ:ContDiffAt ℝ ω ψ 0)
include hF hψ
lemma formula : Aspiration (fun g=>P.expect g (f g)) (valuation P Z p ψ):=by
    have hp: Visible X (fun _:Empty→G.Color=>1) (1:Melody G ι) vacant 0 1:=⟨fun _ _=> Envelope.const (1:ℝ),fun _ _ _=>(abs_one (α:=ℝ)).le,∅,by simp,fun j=> Empty.elim j,fun _ _ _ _ _=>rfl⟩
    let V:= phaseAmt P univ 1; let A:=phaseAmt P univ f
    have hf:Aspiration (A/V) (valuation P Z p ψ):=(aspirant H hZ hF hψ).quotient (aspirant H hZ hp contDiffAt_const) (basis_fee H hZ|>.ne')
    intro k; obtain ⟨b,hb,ht⟩:= hf k
    refine ⟨b,hb,?_⟩; filter_upwards [Tested.eventually_pos,ht] with g hg he
    rw [Pi.sub_apply,show P.expect g (f g) = (A/V) g from ?_]; exact he
    -- no premise interior g needed for proportional identity at this param!
    unfold A V phaseAmt Planet.expect Planet.pot; simp only [Pi.div_apply,Pi.one_apply,mul_one,setIntegral_univ, mul_div_mul_left _ _ (Real.exp_pos (-1)).ne']; rw [mul_div_mul_left _ _ (by positivity)]
end YM.RGComparison.Core16.Lumen.Fk
