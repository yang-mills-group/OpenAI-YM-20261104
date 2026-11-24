import YangMills.WilsonProof.NativeSupport.Commissioned259.Origin.Published
/-! # Actually read the continuum physical packet in the adjusted position scheme.

Through-p coating in the analytic comparison vs the exact H-reader. Prepare all
G.9 Round hypotheses on these tasks in addition to prior QScale and state enrollment.
Only the *continuation* of the proof into M.3 and M.4, not constructing the underlying
G.9, frame election, etc. here. Point test. See pairing applications for joint tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.GradedFar259.Original
open Function Filter Set MeasureTheory Asymptotics Lattice Wilson RG Source Extraction Table Spec
open Register MS MS.Native MS.Book MS.Menus MS.Tide MS.Fleet MS.Land
open Climb Maxwell XSpace XSpace.Normalize XSpace.Structure1 OPE OPE.Orbits PhysMS
open FVA2.Scale Comparing O.Score O.Enh Dframe ScaleCost Matrix Flash259HorizonFork
open scoped Topology BigOperators Classical Matrix
local notation "late" => 𝓝[>] (0:ℝ)
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Z : ℝ→PhysMS.tower S) (Q:Orbits.Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    {N : WilsonPrescription G} {ν : ℝ}
    {O : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))} {sim : G.Simple}
    {σ : MS.Land.Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match N sim O σ dial)
    {t : ℝ→ℝ} (hZ : Leading F Z) (hq : ∀ d, FieldQuote G (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z) d 1)
    (hQ:LogTrace F Q.port)

open FVA2.O.Read
variable {n d h z:ℕ}
    (θ : Calibrated G t) (S0: StepCost G (GroupS.ψ N.criterion O ν) (GroupS.gaugeN N.scheme N.criterion O ν) t (via Z))
    {D:Fin n→ℕ} {a b c M δ W L:ℝ} {K:Set (Points n)}
    (hd:∀ i,D i≤ z)(hh:h≤z)
    (hW:1≤W)(hK:IsCompact K)(hc':K⊆conf n)
local notation "Vx" => Scale.Measure.outlook N.scheme N.criterion
local notation "Bx" => GroupS.gaugeN N.scheme N.criterion O ν
local notation "e" => fun (_:Fin 1) =>h
local notation "g" => g0 G

-- use in reading any profile vs the true output. Fix probe purchases first.
local notation "D0" => measures F Z e e
local notation "Qz" => measures F Z D e
local notation "Y" => Comparing.panel
-- explicit W large enough from geometry. L covers console bank. Dependences on geometry/prices before η,b,p.
variable (hn:0<n)(ht:collects G L h)(hL:0≤L) (hM:0≤M)(hδ:0<δ)
    (hw:clears W K ({RootG}:Set (Points 1)))
    (hX: Clears W M δ K ({RootG}:Set (Points 1)))
    (P q:ℕ)(hz:q+1≤P)(η:ℝ)(he':0<η)(hx:η<1)

private structure Queries (F:Final C f S) (D:Fin n→ℕ)(K:Set (Points n)) (L W a c b:ℝ) where
  r : ℝ
  T : ℝ
  lo : W ≤ T
  lim₀ : c*(g0 G r)^(-b) ≤ T
  lim : T ≤ a*(g0 G r)^(-b)
  o : Owner F
  x : K
  u : Balls L G D

include S0 θ H hZ hQ hz he' hx hd hh hK hc' hW hM hδ hw hX hL ht hn
/-- M.4 (pointwise no derivatives) on the physical measurements made in M.3, at real r;
The input hypotheses are the precision estimates at G, including `Round` (G.9), true elected
phase, all-orders LogTrace, coherent Leading H. Needs no estimator/cutoff step in addition.
Round at order p *before* Far conversion. -/
theorem M4 : ∀ᶠ b:ℝ in atTop,0<b ∧ ∀ᶠ p:ℕ in atTop,∀ a c:ℝ,0<c→ c≤a →
    Round Vx t Qz hd (fun _=>hh) p a b W K ({RootG}:Set (Points 1)) → Round Vx t D0 (fun _=>hh) (fun _=>hh) p a b W {0} ({RootG}:Set (Points 1)) →
      ∃ B:ℝ,0<B ∧ ∀ᶠ r in late, ∀ T ≥ W,c*g r^(-b) ≤ T → T ≤ a*g r^(-b) →
      ∀ o:Owner F,∀ x∈K,∀ u∈Balls L G D,
        let X:= coefficients F Z Q D h o r x u; let d:= Comparing.panel (instrument F Z h o.1 o.2 r T)
        IsUnit d ∧ stiffness d⁻¹ ≤ B*T^h ∧
          tallyZ (numbers (X-purchased Vx u x h p (t r)))≤ B*(T^(-η)*(g r)^P) ∧
          tallyZ (numbers (X-purchased Vx u x h q (t r)))≤ B*(g r)^(q+1) := by
  have c' : ({RootG}:Set (Points 1)) ⊆ Outside 1 := singleton_subset_iff.mpr ok_wall
  have hs := Original.listing F Z Q H hZ hQ («e»:=e) hK hc' (isCompact_singleton) c' hW hw hM hδ hX hd (fun _=>hh) hh S0 hL θ P η he' hx hn
  filter_upwards [hs] with b ⟨hb,H'⟩; refine ⟨hb,?_⟩
  filter_upwards [eventually_ge_atTop q,H'] with p hq1 H' a c p' hc hx hy
  let I:= Queries F D K L W a c b; let r:I→ℝ:=Queries.r; let l:=Filter.comap r late
  let T:I→ℝ:=Queries.T; let o:I→Owner F:=Queries.o; let M i:=Comparing.panel (instrument F Z h (o i).1 (o i).2 (r i) (T i))
  obtain ⟨i,B,X,Y0⟩:= stageBudget F Z Q H hZ hQ θ S0 hd hh hW hK hc' (l:=l) (T:=T) tendsto_comap
    (Eventually.of_forall (fun i:I=>⟨i.lo,i.lim₀,i.lim⟩)) hb hL ht o (fun i=>i.x.val) (Eventually.of_forall fun i=>i.x.property) (fun i=>i.u.val) (Eventually.of_forall fun i=>i.u.property) P q p hq1 hz η he' (H' a c p' hc hx hy)
  obtain ⟨B,hB,D0'⟩:= B.exists_pos; obtain ⟨A,hA,H⟩:=X.exists_pos; obtain ⟨Zp,hZp,J⟩:=Y0.exists_pos
  refine ⟨B+A+Zp,by positivity,?_⟩
  have g0 := now ((pace sim).comp (tendsto_comap (f:=r)))
  filter_upwards [eventually_comap.mp (i.and (D0'.bound.and (H.bound.and (J.bound.and g0))))] with r task rT hψ hr hv o x hx0 u hu
  obtain ⟨i,B',X,Y0,l⟩:= show IsUnit (Comparing.panel (instrument F Z h o.1 o.2 r rT)) ∧ _ from task (⟨r,rT,hψ,hr,hv,o,⟨x,hx0⟩,⟨u,hu⟩⟩:I) rfl
  let D₀':= Comparing.panel (instrument F Z h o.1 o.2 r rT); let P₀:= coefficients F Z Q D h o r x u
  let S k:= tallyZ (numbers (P₀-purchased Vx u x _ k (t r)))
  have hT:=zero_lt_one.trans_le (hW.trans hψ); change 0 < g r at l
  change ‖stiffness D₀'⁻¹‖ ≤ B * ‖rT^h‖ at B'
  change ‖S p‖ ≤ A*‖rT^(-η)*g r^P‖ at X; change ‖S q‖ ≤ Zp*‖g r^(q+1)‖ at Y0
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ rT^h)] at B'
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ rT^(-η)*g r^P)] at X; rw [Real.norm_of_nonneg (by positivity : 0 ≤ g r ^ (q+1))] at Y0
  refine ⟨i,?_ ,?_ ,?_⟩
  · apply le_trans (le_abs_self _) (le_trans B' ?_); gcongr; linarith
  · apply le_trans (le_abs_self _) (le_trans X ?_); gcongr; linarith
  apply le_trans (le_abs_self _) (le_trans Y0 ?_); gcongr; linarith
end YM.FVA2.GradedFar259.Original
