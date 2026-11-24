import YM.Integration.WilsonVacuumPreResetDatedBirth
import YM.FormalBulk08.Dove.Zen

/-! The two independent regulator prescriptions start from the same signed Wilson
curvature tensor on the cover. The finite polarization also applies at later dates. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetIndependentBirth
open FormalBulk08.Jets
open Function PowerSeries MvPolynomial FormalBulk08 FormalBulk08.Orb FormalBulk08.Lava FormalBulk08.Lotus
open WilsonCoeffUV WilsonCoeffUV.Blue
open scoped Classical BigOperators
variable {U:Type} [Fintype U]

theorem painted (r:ℕ) (T:Ten ℝ U r): Blue.paint r T=Lava.facade r T:=by
  change (∑ i:Fin r→U,T i • ∏ j,MvPolynomial.X (i j))=_
  simp only [Lava.facade_eq,Lava.cards,MvPolynomial.smul_eq_C_mul]

theorem rank (P:Gen ℝ U) (finite:FiniteGen P) (pure:Pure P) (r:ℕ):
    Lava.marble r (totalR P)=P r:=by
  apply Lava.facade_unique (Lava.marble_agate _ _) (fun x s=>pure r s x)
  rw [Lava.marble_grade]
  let n:=max finite.choose (r+1)
  have hn:still P n:=fun k hk=>finite.choose_spec k ((Nat.le_max_left ..).trans hk)
  rw [visible hn,map_sum]
  have select (k:ℕ):MvPolynomial.homogeneousComponent r (paint k (P k))=
      if k=r then Lava.facade k (P k) else 0:=by
    rw [painted,MvPolynomial.homogeneousComponent_of_mem (Lava.facade_grade ..)]
    by_cases h:k=r
    · subst k;simp
    · simp [h,Ne.symm h]
  simp only [select]
  have hr:r<n:=lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right ..)
  simp [Finset.mem_range.mpr hr]

theorem actual (P:Pal ℝ U) (k:ℕ) (degree:shellK k P) (pure:∀e,Pure (P e)) (e r:ℕ):
    FormalBulk08.Shore.rancho (flash P) e r=P e r:=by
  rw [Shore.rancho,flash,coeff_mk]
  exact rank (P e) (finite_shell degree e) (pure e) r

theorem germ {U:Type} [Fintype U] [DecidableEq U] (f:(U→ℝ)→ℝ):Blue.jet f=Jets.paste f:=by
  apply PowerSeries.ext
  intro e
  apply Jets.orbit_ext
  intro z
  rw [Jets.trace_paste]
  change MvPolynomial.eval z (coeff e (Blue.jet f))=_
  exact Blue.rayon f e z


open Filter Lattice Laurent Bloch Wilson RG Precision Exterior Tree PhysicalNext.Repeat.Legato
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Blue.Cameo
open FormalBulk08.Reef FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Flat
open FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa
open scoped Topology
variable {G:Gauge}

theorem finite (G:Gauge)(n:Side)(e r:ℕ):
    Shore.rancho (Reef.seed G n) e r= -sprig (eWilson (G:=G) (c:=n)) 2 e r:=by
  let f:=eWilson (G:=G) (c:=n)
  have signed:Reef.seed G n= -flash (sprig f 2):=by
    rw [sprig_flash,germ,Reef.seed]
    rfl
  rw [signed,Shore.rancho,map_neg]
  change Lava.canyon r (-(PowerSeries.coeff e (flash (sprig f 2))))=_
  rw [map_neg]
  exact congrArg Neg.neg (actual (sprig f 2) 2 (sprig_count f 2) (sprig_pure f W_green 2) e r)

theorem original (R:Run G)(simple:G.Simple)(u:G.ColorIndex)
    (wood:∀j,Lodge (R.family.path.levels.clock.op j 0).patch)(N e r:ℕ):
    -actionW R.family.path.levels R.metals.O N N e (r+1)=Dove.model R.family.path.levels wood
      (fun j=>(R.family.path.levels.blocks j 0).branches) R.metals.O u N N e (r+1):=by
  let V:=R.family.path.levels
  let b:=fun j=>(V.blocks j 0).branches
  have formal:=Dove.genu V wood b R.metals.O u R.alloy.B.ratio simple (N:=N) (i:=N) le_rfl
  rw [Dove.leaves] at formal
  rw [Dove.leaves,actionW,story_top]
  change -(lop (moon G) e (r+1))=_
  rw [lop,if_neg (Nat.succ_ne_zero _)]
  obtain ⟨s,c,positive,fee⟩:=formal.fare e (r+1)
  let i:Fin (r+1):=0
  have ideal:=FormalBulk08.Bank.stable positive.le (formal.civil e (r+1)) fee i
  funext x
  have actualLimit:=((moon_pages G e (r+1)).point x).neg
  simp only [dilute,if_neg (Nat.succ_ne_zero _)] at actualLimit
  have formalLimit:=ideal.1 x
  simp_rw [←Mesa.bend e i,finite,Pi.neg_apply] at formalLimit
  exact tendsto_nhds_unique actualLimit formalLimit

end YM.Integration.WilsonVacuumPreResetIndependentBirth
