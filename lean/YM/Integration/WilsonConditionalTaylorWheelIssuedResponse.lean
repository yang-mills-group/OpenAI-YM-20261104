import YM.Integration.WilsonConditionalTaylorWheelResponse
import YM.Integration.WilsonConditionalTaylorWickVariation

/-! The authentic graded upper heat readout is exactly the original
finite normalized interacting expectation with its signed folded source. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelIssuedResponse
open Function Matrix Lattice RG Exterior Wilson Precision Tree FreeResolvent Bloch PowerSeries Next.Foundations
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Jets FormalBulk08.Orb FormalBulk08.Series Stationary
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Wheel
open WilsonConditionalTaylorWheelKernel WilsonConditionalTaylorWick WilsonConditionalTaylorWickVariation
open MSbar MSbar.Cacao WilsonMovingNormalizedBank
open scoped Classical BigOperators Matrix
variable {G:Gauge} (D:Stage G)
local notation "op" => D.R.family.path.levels.clock.op D.j D.per
local notation "coarse" => D.R.family.side D.j D.per
local notation "fine" => D.R.family.side (D.j+1) D.per
local notation "form" => freeForms D.R.family.path.levels D.N (D.j+1)
set_option quotPrecheck false in
local notation "mean" => installed (op).ratio (predictionA D.R.family.path.levels D.N D.j)
local notation "bank" => Winding.emera (actionW D.R.family.path.levels D.R.metals.O D.N (D.j+1)) fine
local notation "B" => WilsonMovingFiniteConditional.lift (wire G coarse) (Active G D.forest)

theorem deposited (y:wire G coarse→ℝ) (T:Pap (Active G D.forest⊕wire G coarse)):
    glimpse y (amount D T)=contract B (Sum.elim 0 y) (saddle D).q T:=by
  change glimpse y (beam (variation (saddle D) _).call _)=_
  rw [←WilsonConditionalTaylorWheelHeat.full,WilsonConditionalTaylorWheelDeposit.paid]

theorem original (simple:G.Simple) (q:ℕ) (w:PChart G fine) (degree:shellK q w) (angular:∀e,Pure (w e))
    (y:wire G coarse→ℝ):
    glimpse y (flash (reed op D.forest form mean D.R.metals.O bank q w))=
    quotient (WilsonConditionalTaylorWheelResponse.lift (G:=G) op D.forest)
      (WilsonConditionalTaylorWheelResponse.center (G:=G) op D.forest mean y) (saddle D).q
      (WilsonMovingFiniteConditional.interaction (Reef.flush D.forest D.tag D.R.metals.O (-flash bank)))
      (Reef.seat D.forest (flash w)):=by
  have old:=Winding.emera_far D.R.family.path.levels simple D.R.alloy.B.ratio (Nat.succ_le_iff.mpr D.live) fine
  rw [←WilsonConditionalTaylorWheelResponse.normalized op D.forest D.R.metals.O D.R.alloy.B.ratio
    bank old.1 (D.R.family.path.levels.blocks D.j D.per).branches D.tag mean]
  let f:=shot op D.forest mean D.R.metals.O bank
  let T:=loom (camSlice G op D.forest (extractV G op D.forest mean)) (flash w)
  let x:Active G D.forest⊕wire G coarse→ℝ:=Sum.elim 0 y
  have hf:Kind f:=by
    change coeff 0 (shot op D.forest mean D.R.metals.O bank)=0
    rw [shot,loom,coeff_map,coeff_zero_eq_constantCoeff_apply,flash_blank (pack_zero op D.R.alloy.B.ratio),map_zero]
  have pd:(saddle D).q.PosDef:=((RunFormalChain.fromRun D.R).step D.N D.j D.per D.live).positive D.forest D.tag
  have sym: (saddle D).q.IsSymm:=Matrix.isHermitian_iff_isSymm.mp pd.isHermitian
  have one:coeff 0 (mass B x (saddle D).q f)=1:=by
    change coeff 0 (beam _ _)=1
    rw [←WilsonMovingWickCoefficient.complete B x (saddle D).q sym pd.posSemidef (Spring f)]
    exact WilsonMovingGaussianResponse.first _ _ _ _ (MSbar.Cacao.covers hf)
  have live:mass B x (saddle D).q f≠0:=by
    intro h;rw [h,map_zero] at one;exact zero_ne_one one
  have h:=congrArg (fun Z=>glimpse y Z) (WilsonConditionalTaylorWheelKernel.issued D simple q w degree angular)
  change glimpse y (amount D (expan f*T))=glimpse y (amount D (expan f)*
    flash (reed op D.forest form mean D.R.metals.O bank q w)) at h
  have hm (Y Z:Pap (wire G coarse)):glimpse y (Y*Z)=glimpse y Y*glimpse y Z:=map_mul _ _ _
  rw [hm,deposited,deposited,WilsonMovingExponentialConvention.exp f hf,mul_comm (Spring f) T] at h
  apply mul_right_cancel₀ live
  rw [WilsonConditionalTaylorWickVariation.normalized B x (saddle D).q sym pd f T hf]
  exact (mul_comm _ _).trans h.symm

end YM.Integration.WilsonConditionalTaylorWheelIssuedResponse
end

