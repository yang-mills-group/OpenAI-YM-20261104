import YM.Integration.WilsonReportingForestRelative

/-! On the actual restored forest chart, every variable is the logarithm
of its own relative fine bond. The original nonwrapping collar provides a
quantitative estimate even when two bonds share an arbitrary exterior pivot. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonReportingForestPivots
open Filter Finset Set Lattice Wilson Tree RG RG16 MSbar.Heath Precision PertExtension OPE.Therm
open PhysicalNext.Repeat.Legato WilsonPhysicalRegisteredForestAction WilsonPhysicalRegisteredForestCrossing
open WilsonReportingRegisteredAction WilsonPhysicalLocalPlaquetteForest WilsonReportingForestBlocks
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) {I:Type} [Fintype I]
local notation "A"=>R.family.path.levels

/-- The accepted integrand of the joint Haar change of variables determines
the logarithm in the actual coordinate, including its frozen background. -/
theorem chart_angles (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (d:I→ℕ) : ∀ᶠ m:ℕ in atTop,∀per
    (o:I→Site (R.family.side (m+1) per)) (T:Forest ((A).clock.op m per).ratio),
    let B:=incident R T d o
    let E:=moving T B
    let L:=((A).clock.op m per).ratio.count.val
    ∀(v:({i:T.Free|i∉E}:Set T.Free)→G.El) (x:↥E→G.Color), ‖x‖≤J.r →
      restored T B v (Chart.expLinks G (↥E) x)∈cold R m per d o→∀e:↥E, ∃i:I,
      ‖x e‖≤(2*J.C)*(area (extent (depth R (d i)+3) L) L*cool (A) (m+1)) := by
  let D:=fun i=>depth R (d i)+3
  filter_upwards [dates R.family simple slow (Finset.univ.sup D) (half_pos clear.dist)] with m prices per o T
  dsimp only
  intro v x inside good e
  let B:=incident R T d o
  let E:=moving T B
  let L:=((A).clock.op m per).ratio.count.val
  let u:=(cut T E).symm (Chart.expLinks G (↥E) x*background T B v,v)
  have chill:T.drape u∈cold R m per d o:=good
  have atBond:deviation T u e.val=G.lieExp (x e):=(decoded T B v (Chart.expLinks G (↥E) x)).1 e
  obtain ⟨i,near⟩:=anchored R T d o e.val (Finset.mem_filter.mp e.property).1
  obtain ⟨period,fee,_⟩:=prices per (D i) (Finset.le_sup (f:=D) (Finset.mem_univ i))
  let a:=area (extent (D i) L) L*cool (A) (m+1)
  have pt:0≤cool (A) (m+1):=by unfold cool RG.Calendar.hatCoupling;positivity
  have rate:0≤a:=by dsimp [a]; unfold area;positivity
  have bound:G.chord (G.lieExp (x e))≤2*a:=by
    rw [←atBond]
    by_cases h:internal T e.val
    · rw [deviation,if_pos h]
      have loc:=near e.val rfl
      have b:G.chord (u e.val)≤a:=free T (o i) _ period u pt (Set.mem_iInter.mp chill i)
        e.val loc.1 loc.2 h
      linarith only [b,rate]
    · rw [deviation,if_neg h]
      exact pair T (o i) _ period u pt (Set.mem_iInter.mp chill i) e.val (pivot T e.val)
        (pair_of T e.val).symm (fun f hf=>near f (hf.elim (fun z=>z ▸ rfl) (fun z=>z ▸ pair_of T e.val)))
  have half:a≤J.δ/2:=fee
  have read:=clear.near (G.lieExp (x e)) (by linarith only [bound,half])
  rw [(clear.small _ ((norm_le_pi_norm x e).trans inside)).1] at read
  refine ⟨i,read.2.2.trans ?_⟩
  calc
    _≤J.C*(2*a):=mul_le_mul_of_nonneg_left bound (zero_le_one.trans clear.cost)
    _=(2*J.C)*a:=by ring

/-- In the variables of the true finite-g Taylor formula, divide by the
same positive Wilson coupling that multiplies each deposited angle. -/
theorem physical_angles (simple:G.Simple) (slow:∀m,((R.family.S.block m).val:ℝ)≤Real.log (Lambda (A) m))
    (J:Voice G) (clear:Clear G J) (d:I→ℕ) : ∀ᶠ m:ℕ in atTop,∀N,m<N→∀per
    (o:I→Site (R.family.side (m+1) per)) (T:Forest ((A).clock.op m per).ratio),
    let B:=incident R T d o
    let E:=moving T B
    let L:=((A).clock.op m per).ratio.count.val
    let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
    ∀(v:({i:T.Free|i∉E}:Set T.Free)→G.El) (x:↥E→G.Color), ‖g • x‖≤J.r →
      restored T B v (Chart.expLinks G (↥E) (g • x))∈cold R m per d o→∀e:↥E, ∃i:I,
      ‖x e‖≤(2*J.C)*(area (extent (depth R (d i)+3) L) L*cool (A) (m+1))/g := by
  filter_upwards [chart_angles R simple slow J clear d] with m price N live per o T
  dsimp only
  intro v x inside good e
  let g:=Pert.Asymptotics.regulatorRun R.family N per (m+1)
  have b0:0<(A).clock.hatBeta (m+1):=zero_lt_one.trans ((A).fits.delayed _)
  have band:(A).clock.hatBeta (m+1)/2≤R.family.path.β N per (m+1):=
    (R.makes.wilson.represents N per (m+1) live).band.1
  have beta:0<R.family.path.β N per (m+1):=by linarith only [b0,band]
  have gp:0<g:=inv_pos.mpr (Real.sqrt_pos.mpr beta)
  obtain ⟨i,paid⟩:=price per o T v (g • x) inside good e
  refine ⟨i,(le_div_iff₀ gp).mpr ?_⟩
  simpa only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_pos gp,mul_comm ‖x e‖ g] using paid

end YM.Integration.WilsonReportingForestPivots
