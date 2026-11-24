import YM.Integration.FVA1Physical.Wilson.SparseObservable
import YM.Integration.FVA1Physical.Sources.Round2.StencilWickRows
import YM.Integration.FVA1Physical.Round2.StencilExteriorTests

/-! Outside a physical set of superalgebraically small mass, the original
mixed stencil is evaluated by the normalized gauge average of its own canonical
Taylor rows. The estimate is uniform in all placements, including coincident
and widely separated marks, and uses the full interacting physical probability. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.FVA1Physical.Wilson
open Filter Set Finset MeasureTheory Lattice RG YM.Wilson Pressure
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open OPE.Therm Qlocal.Schedule MSbar.Heath MSbar.Heath.Cottage MSbar.Heath.Stock
open YM.Integration.FVA1Physical.Round2.Curvature Next.Fluctuations
open MSbar Push.Uniform
open scoped Classical BigOperators Topology
variable {G : Gauge} {I : Type} [Fintype I] (J : I → Lamp G)

def stencilEdges {n:Side} (o:I→Site n) : Finset (Edge (Site n)) := Finset.univ.image (legs J o)

private abbrev AllSlots := ↥(Finset.univ : Finset (Slice J))

private def resolvedLinks {n:Side} (o:I→Site n) (g:ℝ) (U:Config G n) (l : Wire G (AllSlots J)) : ℝ :=
  (g⁻¹ • logWithin G (U (legs J o l.1.val))) l.2

def sparseTaylor {n:Side} (o:I→Site n) (g:ℝ) (part:Bool) (p:ℕ) (U:Config G n) : ℝ :=
  ∑ k∈Finset.range (p+1), g^k * MvPolynomial.eval (resolvedLinks J o g U) (lampRow J part Finset.univ k)

theorem sparseTaylor_meas {n:Side} (o:I→Site n) (g:ℝ) (part:Bool) (p:ℕ) :
    Measurable (sparseTaylor J o g part p) := by
  have m : Measurable (resolvedLinks J o g) := by
    apply measurable_pi_lambda;intro l
    have co : Continuous (fun a : G.Color => a l.2) := by fun_prop
    exact co.measurable.comp (((logWithin_meas G).comp (measurable_pi_apply (legs J o l.1.val))).const_smul g⁻¹)
  exact Finset.measurable_sum _ fun k _=>measurable_const.mul ((MvPolynomial.continuous_eval _).measurable.comp m)

/-- One analytic computation applies on the selected sparse chart before choosing the lattice. -/
theorem sparse_stencil_chart (part:Bool) (p:ℕ) : ∃ δ C:ℝ, 0<δ ∧ 0≤C ∧ ∀ {n:Side} (o:I→Site n)
    (g τ:ℝ), 0<g → 0≤τ → τ<δ → ∀ U∈edgeWindow (G:=G) (stencilEdges J o) τ,
    |look part (tally J o U) - sparseTaylor J o g part p U| ≤ C*τ^(p+1) := by
  obtain ⟨L,r,pos,rad,localLog⟩:=log_chart_cost G
  obtain ⟨d,A,dp,ap,price⟩:=lampRows_remainder J part Finset.univ p
  let h:=(LocalH.geom_patch G).choose
  have hp:0<h:=(LocalH.geom_patch G).choose_spec.1
  refine ⟨min r (min (h/L) (d/L)),A*L^(p+1),lt_min rad (lt_min (div_pos hp pos) (div_pos dp pos)),mul_nonneg ap (pow_nonneg pos.le _),?_⟩
  intro n o g τ gp tn small U inside
  have cuts:=lt_min_iff.mp small
  have ht:L*τ<h:=by have t:=(lt_div_iff₀ pos).mp (lt_min_iff.mp cuts.2).1;linarith only [t]
  have dt:L*τ≤d:=by have t:=(lt_div_iff₀ pos).mp (lt_min_iff.mp cuts.2).2;linarith only [t]
  let v:=resolvedLinks J o g U
  have logs (k:Slice J) : G.lieExp (logWithin G (U (legs J o k)))=U (legs J o k) ∧
      ‖logWithin G (U (legs J o k))‖≤L*τ := by
    have edge:legs J o k∈stencilEdges J o:=Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have chord:=inside _ edge
    obtain ⟨eq,size⟩:=localLog _ (chord.le.trans cuts.1.le)
    have sz:=size.trans (mul_le_mul_of_nonneg_left chord.le pos.le)
    have ha:U (legs J o k)∈exponentialPatch G:=⟨_,by simpa only [Metric.mem_ball,dist_zero_right] using sz.trans_lt ht,eq⟩
    rw [logWithin,Set.piecewise_eq_of_mem _ _ _ ha]
    exact ⟨eq,sz⟩
  have vector_eq : g • Lumen.vector v = fun i:AllSlots J=>logWithin G (U (legs J o i.val)) := by
    have eq : Lumen.vector v = fun i:AllSlots J=>g⁻¹ • logWithin G (U (legs J o i.val)) := by
      funext i;apply PiLp.ext;intro _;rfl
    rw [eq];funext i;rw [Pi.smul_apply,smul_inv_smul₀ gp.ne']
  have nn:0≤L*τ:=mul_nonneg pos.le tn
  have len: g*‖Lumen.vector v‖≤L*τ := by
    rw [←Real.norm_of_nonneg gp.le,←norm_smul,vector_eq,pi_norm_le_iff_of_nonneg nn]
    exact fun i=>(logs i.val).2
  have quoted:=price v g gp (len.trans dt)
  have raw:lampShape J part Finset.univ (g • Lumen.vector v)=look part (tally J o U):=by
    rw [vector_eq,←exhibition J o U]
    apply congrArg (fun z=>look part (exhibit J z))
    funext k
    simpa only [selectLinks,Finset.mem_univ,dif_pos,Function.comp_apply] using (logs k).1
  rw [raw,Real.norm_eq_abs] at quoted
  apply quoted.trans
  calc
    A*‖Lumen.vector v‖^(p+1)*g^(p+1) = A*(g*‖Lumen.vector v‖)^(p+1) := by rw [mul_pow];ring
    _ ≤ A*(L*τ)^(p+1) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg gp.le (norm_nonneg _)) len _) ap
    _ = _ :=by rw [mul_pow];ring

/-- A normalized sparse gauge window gives an unconditional fixed-order approximation
to every actual mixed canonical field, in the full original scene law. -/
theorem sparse_stencil_mean (R:PhysicalNext.Repeat.Legato.Run G) (simple:G.Simple)
    (gate:selectedThreshold (angularThreshold G) R.metals R.rolls R.alloy R.kit)
    (P:Palisade) (V:Voice G) (part:Bool) (p K:ℕ) : ∃ C:ℝ, 0≤C ∧
    ∀ᶠ j:ℕ in atTop, ∀ (N n:ℕ) (_:j+1≤N) (o:I→Site (R.family.side (j+1) n)) (g:ℝ), 0<g →
    let x:=R.family.path.levels.clock.hatBeta (j+1);let B:=stencilEdges J o
    (∫U,|look part (tally J o U)-orbitWindow (edgeWindow B (room x)) (sparseTaylor J o g part p) U|
      ∂(scene R.family.path N n (j+1))) ≤
       C*(room x)^(p+1)+(sparseCount (Fintype.card (Slice J)):ℝ)*(x⁻¹)^K*stencilBound J := by
  obtain ⟨δ,C,dp,cp,chart⟩:=sparse_stencil_chart J part p
  refine ⟨C,cp,?_⟩
  have limit:Tendsto (fun x=>room x) atTop (𝓝 0):=by
    simpa only [zero_mul,zero_add,one_mul] using hotel_physical_small P V 0 1
  have grows:Tendsto (fun j:ℕ=>R.family.path.levels.clock.hatBeta (j+1)) atTop atTop:=
    (Multi.Wage.hat_tend simple R.family.path.levels).comp (tendsto_add_atTop_nat 1)
  filter_upwards [sparse_observable_mean R simple gate (Fintype.card (Slice J)) K,
    grows.eventually (limit.eventually (eventually_lt_nhds dp))] with j pay small N n hj o g gp x B
  have count:B.card≤Fintype.card (Slice J):= (Finset.card_image_le.trans_eq (Finset.card_univ))
  have xp:1<x:=R.family.path.levels.fits.delayed _
  have rn:0≤room x:=by unfold MSbar.Heath.Cottage.room MSbar.Heath.Stock.distance;positivity [Real.log_pos xp]
  apply pay N n hj B count (fun U=>look part (tally J o U)) (sparseTaylor J o g part p)
    _ _ (mul_nonneg cp (pow_nonneg rn _)) (stencilBound_pos J).le
    (fun z U=>congrArg (look part) (tally_invariant J o z U)) ((look part).continuous.comp (tally_cont J o)).measurable
    (sparseTaylor_meas J o g part p) (stencil_bounded J o part)
  exact chart o g (room x) gp rn small

end YM.Integration.FVA1Physical.Wilson
