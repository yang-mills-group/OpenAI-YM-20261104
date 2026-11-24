import YM.Comparison.RG02.Bare.Model
import YM.Comparison.RG02.Normal.Tagged
import YM.Comparison.RG02.Laplace.Scalar
import YM.Comparison.RG02.Bulk.Spur
/-!
# Smooth top input certificate on actual torus and test all orders

 Physical bare families use **exact** Wilson action and noise during this fixed-geometry
 comparison; when coupled, variate **fine** g. E choice of lower path prescriptions
 already in `Chain.step`, use them, augment extra packets to model the bare top exactly.
 No mask norm or uniformity assertions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Comparison.RG02.Bare
open Function Filter Finset MeasureTheory ProbabilityTheory RG Precision Lattice Wilson Exterior Tree
open YM.Push.SectorMeasure
open PertExtension.Series PertExtension.Series.Tested
open Marker Multi Order YM.Next.SectorChange Integral Actual Laplace
open YM.Extra.Trajectories (connected pass_connected)
open YM.Comparison.RG02.Assembly (GradeAt)
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {p : Clip} {P : PathData G} {O : ChartRatio G}
  (K : Bulk.Kernel S p P O) (F : Forest S.ratio)
variable {V : Type} [DecidableEq V] [Fintype V] {R : Census V} (W : Bulk.Colors R G f)
    (t : S.Choices) (x : fieldDir G c 1) (n : ℕ) (D : BudgetPoint)
local notation "T"=>Bulk.Fk K F t W x n
local notation "B"=> realMoment K F W t x
local notation "D₀" g:max => S.push (temperature g) (Wilson.bare (temperature g)) (sample g x)
local notation "O'" g:max => office K F t g 0 x

def rho (g : ℝ) := (O' g)⁻¹* D₀ g
lemma bare_enough (g : ℝ) : Normal.Strong f (G:=G) (Wilson.bare (temperature g)) := by
   have hb := Wilson.bare_cont (G:=G) (n:=f) (temperature g)
   obtain ⟨a,-,ha⟩:= isCompact_univ.exists_isMinOn (s:=Set.univ) Set.univ_nonempty hb.continuousOn
   exact ⟨Env.compact hb,_,bare_pos ..,fun _=> ha (Set.mem_univ _)⟩
omit [Fintype V] in
lemma rho_pos (g : ℝ) (h : 0<g) : 0<rho K F t x g:= mul_pos (inv_pos.mpr (office_pos K F t g 0 x h)) (Normal.total_pos S (temperature g) (sample g x) _ (bare_enough g) K.branches)
lemma vacancy (g : ℝ) : (B g).part R.quiet = rho K F t x g := by
    unfold realMoment rho; rw [Poly.part_smul,Complex.ofReal_mul,Complex.ofReal_inv,grades]; congr 1 -- `Push` vs S.push ofReal
    let d n:=temperature n; let V:=sample g x
    dsimp only; unfold StepData.push; 
    simp_rw [Actual.atMark,top,Poly.part_smul,Passes, fun U=> Poly.pass_part (markedLog g U W) (by apply part_lit_quiet), mul_one]
    simp_rw [Complex.real_smul, ← Complex.ofReal_mul]; exact integral_ofReal

variable (hW : Witnessed W K)
include hW D
/-- Check all: the true Laplace test using g→0⁺ (fixed geometry, using fresh temperature g at
 top and in noise both, not varying the other prescriptions). Also `fortune` for tag witnesses.
 Includes division/log at fixed torus. Specialize physical top via `Composition`. -/
lemma wilson_step_test :
    Fleet.Test (T) B ∧ Trial (detail (logVac (T)) R.quiet) (fun g=>Complex.ofReal (Real.log (rho K F t x g))) n ∧ Fleet.Test (Order.ratio (T)) (fun t'=> Order.unitScale (B t')) ∧ Fleet.Test (Order.logMarked (T)) (fun t'=> connected (Order.unitScale (B t'))) := by
    have H : Fleet.Test (T) B:= fun s=> header K F W t x n D hW s -- order? check
    have he:= Bulk.fk_sym K F t W x n; have hp:= Bulk.fk_unit K F t W x n
    refine ⟨H,?_,Fleet.via hp H he,Fleet.connected_series hp H he⟩
    have hv:=Fleet.scalar hp H he (Bulk.uncolored K F t W x n); simpa only [vacancy,Complex.ofReal_re] using hv
omit hW D

-- specialize path & mark generators arbitrary. W proof independent step choices.
variable {H : History G} (L : Bulk.Chain H) (i u : ℕ) (R)
  (X : Bulk.Colors R G (H.S.side (i+1) u))
local notation "K"=> L.step (i+1) i u (Nat.lt_succ_self i)
local notation "P'"=> H.rep (i+1) u (i+1)
local notation "V₀"=> Config G (H.S.side (i+1) u)
local notation "Λ"=> (ℝ × fieldDir G (H.S.side (i+1) u) 1)
local notation "B₀"=>H.rep (i+1) u i
def bareUp (X : Bulk.Colors R G (H.S.side (i+1) u)) : Bulk.Colors R G (H.S.side (i+1) u) :=
    {X with vac:=fun _ V=> Wilson.energy V-mainTerm (P').clip (P').path V}
include L
omit [Fintype V] in
lemma fixUp : GradeAt 5 (Bulk.projected (bareUp R i u X).vac) := by
   let f (x: fieldDir G (H.S.side (i+1) u) 1):= Wilson.energy (represent x); let g (x: fieldDir G (H.S.side (i+1) u) 1):= mainTerm (P').clip (P').path (represent x)
   have hf : ∀ i, i ≤ 4 → SameJet i g f:= L.peak (i+1) u
   have hp : GradeAt 5 (f - g):= by
       obtain ⟨ha,hb,hc⟩:=hf 0 (by decide); exact ⟨hb.sub ha,fun i hi=> by rw [iteratedFDeriv_sub_apply (hb.of_le le_top) (ha.of_le le_top), (hf i (by omega)).2.2, sub_self]⟩
   exact GradeAt.coarse hp (g:= (Prod.snd:Λ→ _)) contDiffAt_snd rfl
omit [Fintype V] in
lemma still_ok (h : Bulk.Well X) : (bareUp R i u X).Standard := by
   have he:=fixUp R L i u X
   obtain ⟨a,A,Λ₀,hp⟩:= (K).bounds
   refine ⟨⟨he.lower (by decide),h.suppose_mark,fun t p x=>?_,h.gauges,fun _=> Env.compact ?_,h.prices⟩,he⟩
   · unfold bareUp; simp only [energy_gauge,Work.F05.mainTerm_gauge hp x]
   exact energy_cont.sub (main_continuous_π hp).1
lemma no_loop (p : Config G (H.S.side (i+1) u)): loop (P').path p =0:= by
   simp only [loop,RG.Patch.average,uncut,Atom.unmasked, Atom.poly,L.starts (i+1) u]; simp
lemma based (h : Bulk.Well X) (hs : Starts X) : Witnessed (bareUp R i u X) K:= by
   refine ⟨(still_ok R L i u X h).1, hs,?_⟩; intro g; unfold top model; funext U
   unfold Passes Integral.weight localClassic; rw [bareUp,no_loop L i u]; dsimp only [Wilson.bare]; rw [add_sub_cancel, sub_zero, zero_sub, neg_mul]
end YM.Comparison.RG02.Bare
