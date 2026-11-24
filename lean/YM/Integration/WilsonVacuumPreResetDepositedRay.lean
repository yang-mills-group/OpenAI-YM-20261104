import YM.Integration.WilsonVacuumPreResetStationaryChange
import YM.Integration.WilsonVacuumPreResetTorusDepositedGrant
import YM.Integration.ForestRaySeries

/-! Angular coefficients of the actual signed group action at one registered
Wilson spring. The integration uses its original relative variables and determinant. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetDepositedRay
open Function Filter Finset Lattice Laurent Bloch Wilson RG Precision Exterior Tree Matrix PowerSeries
open PhysicalNext.Repeat.Legato Comparison.RG02 Cumulants FreeResolvent WilsonCoeffUV
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue WilsonCoeffUV.Blue.Cameo
open WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam Marker Multi Stationary WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Embroider WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetTorusDeposit
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {U V : Type} [Fintype U] [Fintype V] {σ C : ℝ}

private theorem rows (n : Side) (Z : SeriesA G) (hZ : Draw Z σ C) (hs : 0<σ)
    (θ : Lawn (U⊕V)→Lawn U) (ht : Green θ) (hz : θ 0=0)
    (D : Matrix (Woods G n) (U⊕V) ℝ) (v : Lawn (U⊕V)) :
    ForestRaySeries.Reads v (retool θ (loom D (FundedPeriodAction.formal n Z)))
      (fun g=> FundedPeriodAction.rendered n Z g (mantle (D *ᵥ spider θ (g • v)))) := by
  have hD : loom D X = X := by simp [loom]
  have hθ : retool θ X = X := by simp [retool,reroll]
  induction Z with
  | nil => simpa [FundedPeriodAction.formal,FundedPeriodAction.rendered] using ForestRaySeries.zero v
  | cons a Z ih =>
    have h : Green (turnSeries a.cells (m:=n)) :=
      (turns_analytic a.cells hs (hZ.2 a List.mem_cons_self).toll).contDiffAt
    have hrow := ForestRaySeries.mul (ForestRaySeries.powers v (a.grade-a.rise))
      (ForestRaySeries.linear θ ht hz v D (turnSeries a.cells (m:=n)) h)
    have tail := ih ⟨hZ.1,fun b hb=>hZ.2 b (List.mem_cons_of_mem _ hb)⟩
    simpa only [FundedPeriodAction.formal,FundedPeriodAction.rendered,List.map_cons,List.sum_cons,
      map_add,map_mul,map_pow,hD,hθ,FundedPeriodAction.links] using ForestRaySeries.add hrow tail


variable (R:Run G)(N m p:ℕ)(hm:m<N)(F:Forest (step R m p).ratio)
variable (Z:SeriesA G)
abbrev income := R.family.path.rep N p (m+1)
abbrev pan := panSlice G (step R m p) F (saddle R N m p F)
abbrev jac := stampJ (step R m p) F (center R N m p hm F) (ratio R)

def filed := front (income R N m p).path (income R N m p).clip (fine R m p) + sands Z (fine R m p)

def upperAction : Ink (Woods G (fine R m p)) :=
  jet (fun w:TreeVars G (fine R m p)=>mainTerm (income R N m p).clip (income R N m p).path (mantle w))+
  X^2*jet (fun w:TreeVars G (fine R m p)=>Precision.loop (income R N m p).path (mantle w))+
  FundedPeriodAction.formal (fine R m p) Z

def positive :=
  retool (shift R N m p hm F) (loom (slice R N m p F) (upperAction R N m p Z))+
    retool (shift R N m p hm F) (jet (fun w:Sloc (step R m p) F G=>
      jointPen G (step R m p) (pan R N m p F *ᵥ w)))

variable (v:Sloc (step R m p) F G)

def raw (g:ℝ):ℝ:=
  let w:=spider (shift R N m p hm F) (g • v)
  FundedInteractingPeriod.potential (income R N m p).clip (income R N m p).path Z g
    (mantle (slice R N m p F *ᵥ w))+jointPen G (step R m p) (pan R N m p F *ᵥ w)
theorem paid {σ C : ℝ} (hs : 0<σ) (hZ : Draw Z σ C) :
    ForestRaySeries.Reads (v) (positive R N m p hm F Z)
      (raw R N m p hm F Z v) := by
  let w₀ := fun d : TreeVars G (fine R m p) => mainTerm (income R N m p).clip (income R N m p).path (mantle d)
  let w₂ := fun d : TreeVars G (fine R m p) => Precision.loop (income R N m p).path (mantle d)
  have hP := (R.makes.wilson.represents N p (m+1) hm).good.paths
  have hmain : Green w₀ := by
    have same : intended (m:=(fine R m p)) (income R N m p).clip (income R N m p).path = w₀ := by
      funext d
      unfold intended w₀
      rw [Mosaic.mantle_input]
    rw [←same]
    exact (rye_top hP (fine R m p)).1
  have hloop : Green w₂ := by
    have same : turnSeries (income R N m p).path.loop (m:=(fine R m p)) = w₂ := by
      funext d
      unfold turnSeries w₂ Precision.loop
      rw [Mosaic.mantle_input]
    rw [←same]
    exact (turns_analytic (income R N m p).path.loop hP.width hP.two).contDiffAt
  have ht := shore_green (step R m p) F (saddle R N m p F) (center R N m p hm F) (center R N m p hm F).contDiff.contDiffAt (map_zero _)
  have hz := shore_zero (step R m p) F (saddle R N m p F) (center R N m p hm F) (map_zero _)
  have ha := ForestRaySeries.linear (shift R N m p hm F) ht hz (v) (slice R N m p F) w₀ hmain
  have hb := ForestRaySeries.mul (ForestRaySeries.powers (v) 2)
    (ForestRaySeries.linear (shift R N m p hm F) ht hz (v) (slice R N m p F) w₂ hloop)
  have hc := rows (fine R m p) Z hZ hs (shift R N m p hm F) ht hz (slice R N m p F) (v)
  have hpen : Green (fun u : Sloc (step R m p) F G => jointPen G (step R m p) ((pan R N m p F) *ᵥ u)) :=
    ContDiffAt.comp (g:=jointPen G (step R m p)) (f:=fun u=>(pan R N m p F) *ᵥ u) 0
      (by rw [Matrix.mulVec_zero]; exact penSmooth G (step R m p) ((levels R).blocks m p).branches) (board (pan R N m p F))
  have hq := ForestRaySeries.chart (shift R N m p hm F) ht hz (v) _ hpen
  have hL : loom (slice R N m p F) X=X := by simp [loom]
  have hθ : retool (shift R N m p hm F) X=X := by simp [retool,reroll]
  unfold raw
  simpa only [positive,upperAction,
    FundedInteractingPeriod.potential,w₀,w₂,map_add,map_mul,map_pow,hL,hθ] using
    ForestRaySeries.add (ForestRaySeries.add (ForestRaySeries.add ha hb) hc) hq


private theorem move {I J:Type}[Fintype I][Fintype J](D:Matrix I J ℝ)(P:Ink I):
    X^2*loom D P = loom D (X^2*P):=by
  rw [map_mul,map_pow,show loom D X=X from by simp [loom]]

include hm in
theorem joint {σ C:ℝ}(width:0<σ)(draw:Draw Z σ C):
    X^2*unscaled (step R m p) F (prediction R N m p) (filed R N m p Z)=
      loom (slice R N m p F) (upperAction R N m p Z)+
      jet (fun w:Sloc (step R m p) F G=>jointPen G (step R m p) (pan R N m p F *ᵥ w)):=by
  have budget:=(R.makes.wilson.represents N p (m+1) hm).good.paths
  have h:=FundedInteractingPeriod.series (income R N m p).clip (income R N m p).path
    budget Z width draw (fine R m p)
  have branches:=((levels R).blocks m p).branches
  have pen:=sprouts_move (pen_jets G (step R m p) branches).1 (pen_jets G (step R m p) branches).2.1
  change X^2*(loom (slice R N m p F) (flash (filed R N m p Z))+
    loom (pan R N m p F) (flash (sprig (jointPen G (step R m p)) 2)))=_
  rw [mul_add,move,move,show X^2*flash (filed R N m p Z)=upperAction R N m p Z from h,
    pen,loom_jet (pan R N m p F) _ (penSmooth G (step R m p) branches)]

theorem unscaled_read {σ C:ℝ}(width:0<σ)(draw:Draw Z σ C):
    ForestRaySeries.Reads v (X^2*retool (shift R N m p hm F)
      (unscaled (step R m p) F (prediction R N m p) (filed R N m p Z)))
      (raw R N m p hm F Z v):=by
  have fixed:retool (shift R N m p hm F) X=X:=by simp [retool,reroll]
  have movePhase (P:Ink (Active G F ⊕ Woods G (coarse R m p))):
      X^2*retool (shift R N m p hm F) P =
      retool (shift R N m p hm F) (X^2*P):=by rw [map_mul,map_pow,fixed]
  rw [movePhase,joint R N m p hm F Z width draw,map_add]
  exact paid R N m p hm F Z v width draw

end YM.Integration.WilsonVacuumPreResetDepositedRay
