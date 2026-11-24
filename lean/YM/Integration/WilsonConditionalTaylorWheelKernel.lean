import YM.Integration.WilsonConditionalTaylorWheelHeat
import YM.Integration.WilsonConditionalTaylorWheelVacuum
import YM.Integration.WilsonCommonConditionalGaussian

/-! Retain the exact physical saddle and the honest periodized old winding
action in the finite Gaussian. No separately chosen Gaussian is introduced. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelKernel
open Function PowerSeries Lattice RG Wilson Precision Tree FreeResolvent Matrix Bloch
open PhysicalNext.Repeat.Legato FormalBulk08 FormalBulk08.Orb FormalBulk08.Wick FormalBulk08.Series
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open scoped Classical BigOperators Matrix Topology
structure Stage (G:Gauge) where
  R:Run G
  N:ℕ
  j:ℕ
  per:ℕ
  live:j<N
  forest:Forest (R.family.path.levels.clock.op j per).ratio
  tag:(R.family.path.levels.clock.op j per).Choices

variable {G:Gauge} (D:Stage G)
local notation "op" => D.R.family.path.levels.clock.op D.j D.per
local notation "coarse" => D.R.family.side D.j D.per
local notation "fine" => D.R.family.side (D.j+1) D.per
local notation "form" => freeForms D.R.family.path.levels D.N (D.j+1)
set_option quotPrecheck false in
local notation "mean" => installed (op).ratio (predictionA D.R.family.path.levels D.N D.j)
local notation "bank" => Winding.emera (actionW D.R.family.path.levels D.R.metals.O D.N (D.j+1)) fine

def saddle : Saddle ℝ (Active G D.forest):=by
  let Q:=((RunFormalChain.fromRun D.R).step D.N D.j D.per D.live).covariance D.forest D.tag
  have pd:Q.PosDef:=((RunFormalChain.fromRun D.R).step D.N D.j D.per D.live).positive D.forest D.tag
  exact ⟨Q,Q⁻¹,(fun i j=>(Matrix.isHermitian_iff_isSymm.mp pd.isHermitian).apply j i),
    (fun i j=>(Matrix.isHermitian_iff_isSymm.mp pd.inv.isHermitian).apply j i),
    Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr pd.det_pos.ne')⟩

theorem authentic : (saddle D).q=treeInverse G op D.forest form 0:=
  OriginalMarkedHeatCovariance.activeCovariance D.R D.N D.j D.per D.live D.forest D.tag

def amount (z:Pap (Active G D.forest⊕Woods G coarse)):Pap (Woods G coarse):=
  beam (variation (saddle D) (Woods G coarse)).call
    (PowerSeries.map (emer (Active G D.forest) (Woods G coarse)).toRingEquiv.toRingHom z)

theorem full (z:Pap (Active G D.forest⊕Woods G coarse)):
    Blue.Wick (Woods G coarse) (treeInverse G op D.forest form 0) z=amount D z:=by
  rw [←authentic D];exact WilsonConditionalTaylorWheelHeat.full _ _

theorem vacuum :
    inside op D.forest form mean D.R.metals.O bank=
      amount D (expan (shot op D.forest mean D.R.metals.O bank)):=by
  unfold inside
  exact full D _

theorem numerator (w:PChart G fine):
    insideMark op D.forest form mean D.R.metals.O bank w=
      amount D (expan (shot op D.forest mean D.R.metals.O bank)*
        loom (camSlice G op D.forest (extractV G op D.forest mean)) (flash w)):=by
  unfold insideMark
  exact full D _

theorem issued (simple:G.Simple) (q:ℕ) (w:PChart G fine) (degree:shellK q w) (angular:∀e,Pure (w e)):
    amount D (expan (shot op D.forest mean D.R.metals.O bank)*
        loom (camSlice G op D.forest (extractV G op D.forest mean)) (flash w))=
      amount D (expan (shot op D.forest mean D.R.metals.O bank))*
        flash (reed op D.forest form mean D.R.metals.O bank q w):=by
  rw [←numerator,←vacuum]
  have old:=Winding.emera_far D.R.family.path.levels simple D.R.alloy.B.ratio (Nat.succ_le_iff.mpr D.live) fine
  exact inside_reed op D.forest form mean q old.1 D.R.alloy.B.ratio degree
    (D.R.family.path.levels.blocks D.j D.per).branches (age_sym D.R.family.path.levels ..) old.2 angular

end YM.Integration.WilsonConditionalTaylorWheelKernel
end

