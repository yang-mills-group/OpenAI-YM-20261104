import YM.Integration.WilsonOlderFreshSoftSocketRestored

/-! The complete finite real measured Figure to normalized q invoice, restored and summed after hearing the genuine old scalar. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketTotal
open Function Finset Lattice Laurent Wilson RG Precision Tree Exterior Bloch Matrix PowerSeries
open PhysicalNext.Repeat.Legato FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Motion WilsonCoeffUV.Embroider WilsonCoeffUV.Soil Stationary WilsonCoeffUV.Cosmos WilsonCoeffUV.Bank.Mosaic.Near
open OriginalMarkedSourceComet IndependentSourcePathFamily
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

open WilsonThermometerDeclaredSeeds (Choice entry)
open WilsonThermometerPositionTunedSlope (Columns)
open WilsonOlderFreshSoftSocketMeasuredCash (packet seats ticket)
open WilsonOlderFreshSoftSocketFaces (raw fill)
open WilsonOlderFreshSoftSocketRestored (degree stopped coin)
open WilsonOlderFreshSoftSocketKinetic (kinetic)
open WilsonOlderFreshHybridClock (flat)
open WilsonReceivedCanonicalVerseRegister (start)
open WilsonReceivedCanonicalVersePortfolio (Selection weight)
open WilsonReportingAbsoluteInletForecastBooks (value)
open WilsonOriginalStarSceneWords (pole)
open WilsonReceivedFixedDigitHistory WilsonCoeffUV.Winding ActualRunPhysicalPages Pert.Asymptotics
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G)(d:I→ℕ){D:I→ℕ}
local notation "L_" => R.family.path.levels
local notation "O_" => R.metals.O

def listen (p:ℕ)(θ:ℝ):Era G ℝ→ₗ[ℝ]ℝ where
  toFun E:=flat E p θ
  map_add' E F:=by
    change (∑i∈range (p+1),θ^i*(E.2 i 0 Fin.elim0+F.2 i 0 Fin.elim0))=_
    simp only [mul_add,sum_add_distrib]
    rfl
  map_smul' z E:=by
    change (∑i∈range (p+1),θ^i*(z*E.2 i 0 Fin.elim0))=z*(∑i∈range (p+1),θ^i*E.2 i 0 Fin.elim0)
    rw [mul_sum]
    exact sum_congr rfl fun i _=>by ring

omit [Fintype I] in
theorem priced (N per K:ℕ)(w:(i:I)→R.family.label (d i))(S:Finset I)(q:Selection R d S):
    ticket R d S w N per K q=weight R d N per K w S q*
      ((regulatorRun R.family N per K:ℂ)^(degree R d S (fill R d S q)))⁻¹:=by
  classical
  have h:degree R d S (fill R d S q)=∑i:S,pole R d (entry R d i (q i)):=by
    rw [degree,←Finset.sum_coe_sort S]
    apply sum_congr rfl
    intro i _
    change pole R d (entry R d (i:I) (fill R d S q i))=_
    rw [show fill R d S q i=q i from dif_pos i.property]
  rw [ticket,WilsonReceivedCanonicalVersePortfolio.weight,prod_mul_distrib,h]
  congr 1
  simp only [_root_.zpow_neg,_root_.zpow_natCast,Finset.prod_inv_distrib,Finset.prod_pow_eq_pow_sum]

variable (κ:(i:I)→Knob (D i))(pt:I→Chamber)(N per K c v:ℕ)(cells:Digits R.family.path.levels I)
variable (S:Finset I)(w:(i:I)→R.family.label (d i))(y:I → Cover)(f:Pen D S→L[ℝ]ℝ)
local notation "g_" => regulatorRun R.family N per K

def figure (p:ℕ)(θ:ℝ):ℂ:=∑b:Columns R (fun i:S=>d i),packet R d S w N per K b*
    (flat (stopped R d N K c v cells y S f (WilsonOlderFreshSoftFigures.stencil R D d (seats R d S b) κ pt)) p θ:ℂ)
def normalized (p:ℕ)(θ:ℝ):ℂ:=∑q:Selection R d S,weight R d N per K w S q*
    (flat (stopped R d N K c v cells y S f (start R d κ pt (fill R d S q))) p θ:ℂ)
def cost (p:ℕ)(θ:ℝ)(q:Selection R d S):ℝ:=
  let h:=degree R d S (fill R d S q)
  let A:=kinetic R.family.path.levels R.metals.O N K v
  let Z:Era G ℝ:=stopped R d N K c v cells y S f (start R d κ pt (fill R d S q))
  (g_^h)⁻¹*(θ^(p+1)*((h:ℝ)+2)*(WilsonReportingAbsoluteInletForecastBooks.mass p A)^h+
    |(θ*value p A θ)^h-g_^h|)*WilsonReportingAbsoluteInletForecastBooks.mass p (coin Z)

theorem settled (simple:G.Simple)(ratio:LocalRatio O_)(vc:v≤c)(ck:c≤K)(live:K≤N)(p:ℕ)(θ:ℝ):
    figure R d κ pt N per K c v cells S w y f p θ=
      ∑q:Selection R d S,ticket R d S w N per K q*(flat (stopped R d N K c v cells y S f (raw R d κ pt (fill R d S q))) p θ:ℂ):=by
  classical
  have test (L:ℂ→L[ℝ]ℝ)(z:ℂ)(r:ℝ):L (z*(r:ℂ))=L z*r:=by
    rw [mul_comm z,←Complex.real_smul,L.map_smul,smul_eq_mul,mul_comm]
  have scene (L:ℂ→L[ℝ]ℝ):
      L (figure R d κ pt N per K c v cells S w y f p θ)=
        L (∑q:Selection R d S,ticket R d S w N per K q*(flat (stopped R d N K c v cells y S f (raw R d κ pt (fill R d S q))) p θ:ℂ)):=by
    rw [figure]
    simp only [map_sum,test]
    have h:=congrArg (listen (G:=G) p θ) (WilsonOlderFreshSoftSocketHeard.original
      R d κ pt simple ratio L N per K c v cells S w vc ck live y f)
    simp only [map_sum,map_smul,smul_eq_mul] at h
    exact h
  exact Complex.ext (scene Complex.reCLM) (scene Complex.imCLM)

theorem original (simple:G.Simple)(ratio:LocalRatio O_)(vc:v≤c)(ck:c≤K)(live:K≤N)(p:ℕ)
    (kept:∀q:Selection R d S,degree R d S (fill R d S q)≤p){θ:ℝ}(θ0:0≤θ)(θ1:θ≤1):
    ‖figure R d κ pt N per K c v cells S w y f p θ-normalized R d κ pt N per K c v cells S w y f p θ‖≤
      ∑q:Selection R d S,‖weight R d N per K w S q‖*cost R d κ pt N per K c v cells S y f p θ q:=by
  classical
  rw [settled R d κ pt N per K c v cells S w y f simple ratio vc ck live,normalized,←Finset.sum_sub_distrib]
  apply (norm_sum_le ..).trans
  apply Finset.sum_le_sum
  intro q _
  let h:=degree R d S (fill R d S q)
  let U:=stopped R d N K c v cells y S f (raw R d κ pt (fill R d S q))
  let Z:Era G ℝ:=stopped R d N K c v cells y S f (start R d κ pt (fill R d S q))
  let a:=weight R d N per K w S q
  rw [priced,←Complex.ofReal_pow]
  change ‖a*((g_^h:ℝ):ℂ)⁻¹*(flat U p θ:ℂ)-a*(flat Z p θ:ℂ)‖≤_
  rw [show a*((g_^h:ℝ):ℂ)⁻¹*(flat U p θ:ℂ)-a*(flat Z p θ:ℂ)=
      a*((((g_^h)⁻¹*flat U p θ-flat Z p θ:ℝ):ℂ)) by push_cast;ring]
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (WilsonOlderFreshSoftSocketRestored.original R d κ pt simple ratio N per K c v cells S vc ck live y f
      (fill R d S q) p (kept q) θ0 θ1) (norm_nonneg a)

end YM.Integration.WilsonOlderFreshSoftSocketTotal
end
