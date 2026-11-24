import YM.Integration.WilsonOriginalJointGaussianAdmission
import YM.Integration.WilsonOriginalEarnedUnarySheet

/-! Ordinary and connected finite tables of two actually issued families on the same
nonlinear forest, with the complete absolute-chart joint insertion and original divisor. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalJointForestRay
open Function Filter Set Finset Lattice Laurent Wilson RG Source Labels Marker Multi Precision Tree Exterior Bloch Matrix PowerSeries
open LocalComparison PhysicalNext.Repeat.Legato Comparison.RG02 Comparison.RG02.Cumulants Comparison.RG02.Assembly
open Order AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open PertExtension Series Series.Radial Series.Tested
open FreeResolvent WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Wheel WilsonCoeffUV.Embroider WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Cosmos Next.Rank
open WilsonLimitConstruction Work.F08 FullQLocal FullQLocal.RenderedStep
open WilsonVacuumPreResetStationaryChange WilsonVacuumPreResetDepositedGeometric
open WilsonVacuumPreResetDepositedLetters WilsonVacuumPreResetFiniteRegister
open WilsonVacuumPreResetDepositedIntegrand WilsonOriginalOccupiedForestIntegral WilsonOriginalMeasuredOccupiedForest
open WilsonVacuumPreResetDatedDeposit (Issued)
open WilsonVacuumPreResetOriginalOutput (covered)
open WilsonOriginalRelativeFoldedQuiet (relative credit)
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius
attribute [local instance] Gauge.frobInner

variable {G:Gauge}(R:Run G)(N i per:ℕ)(hi:i<N)(F:Forest (step R i per).ratio)(tag:(step R i per).Choices)
  {V:Type}[DecidableEq V][Fintype V]{C:Marker.Census V}(Y:Bulk.Colors C G (fine R i per))
local notation "S" => step R i per
local notation "K" => model R N i per hi
local notation "φ" => relative R N i per hi F (covered R N i per)
variable (B:fieldDir G (coarse R i per) 1)


open WilsonOriginalEarnedUnaryDriver (driver)
open WilsonOriginalSingleGaussianPass (deposit read_deposit)
open PhysicalForestMarkedRay
open WilsonOriginalSingleGaussianReceipt
variable {A H:Type}[Fintype A][Fintype H]
variable (old fresh:Hot C) (a:A→ℂ)(b:H→ℂ)
variable (U:A→Ink (Woods G (fine R i per)))(W:H→Ink (Woods G (fine R i per)))(r:ℕ)
local notation "rangeSpace" => Woods G (coarse R i per)
local notation "arg" => saddle R N i per F
local notation "q₀" => ((model R N i per hi).covariance F tag)
open WilsonCoeffUV.Blue.Cameo WilsonCoeffUV.Power WilsonCoeffUV.Power.Roam WilsonCoeffUV.Winding
open WilsonOriginalJointGaussianIncome
open WilsonOriginalJointGaussianAdmission (source)
open WilsonOriginalMixedGaussianTable (stock)

def forward :Ink (Woods G (fine R i per))→+*Ink ((Active G F)⊕Woods G (coarse R i per)):=
  (retool (shift R N i per hi F)).comp (loom (slice R N i per F))

local notation "placed" => forward R N i per hi F
/-- Rays of the whole incoming log on the actual block, including both signed families. -/
def Rays :Prop := ∀(s:Hot C)(j:ℕ),j≤r → ∀ z:Precision.Key F G→ℝ,
  readJet (Y.power s+j) (chartMark S F arg K B z Y s)=
    (if s.val=old.val then ∑e,a e*(MvPolynomial.eval (Sum.elim z (flatten B)) (coeff j (placed (U e))):ℝ) else 0)+
    (if s.val=fresh.val then ∑e,b e*(MvPolynomial.eval (Sum.elim z (flatten B)) (coeff j (placed (W e))):ℝ) else 0)

include hi tag in
theorem swept :arg=reveal G S F*((reveal G S F).transpose*arg):=by
  have h:=(K).hessian_pos F tag
  rw [OriginalMarkedHeatCovariance.precision R N i per hi F tag] at h
  exact sweeps G S F (prediction R N i per) (lower R N i) (isUnit_iff_ne_zero.mpr h.det_pos.ne')
    (horizon_step (levels R) i N hi _ _ (step R i per).sizes)

theorem written (e:ℕ)(Z:SeriesA G)(well:Bulk.Well Y)
    (rays:Rays R N i per hi F Y B old fresh a b U W r)(s:Hot (Board C r))(z:Precision.Key F G→ℝ):
    Cloud.paint z (driver R N i per hi F tag Y B e Z r s)=
      (source C r (flatten B) old fresh φ a b (fun x=>placed (U x)) (fun x=>placed (W x)) z).part s.val:=by
  rw [←Join.pair_reunite s.val,WilsonOriginalJointGaussianAdmission.evaluated]
  by_cases has:(Join.left s.val).val.Nonempty
  · let t:Hot C:=⟨Join.left s.val,has⟩
    let d:=(Join.right s.val).val.card
    unfold driver family generator
    simp only [if_pos has,dif_pos has,map_smul,smul_eq_mul,if_neg ((hot_iff_ne _).1 has),zero_add]
    apply congrArg ((d.factorial:ℂ)*·)
    have field:Cloud.paint z (kernelJet (Bulk.stage K F B) (Bulk.hinge F)
        (Bulk.markFn S F Y t) (Y.power t+d))=readJet (Y.power t+d) (chartMark S F arg K B z Y t):=by
      rw [Assembly.reading]
      exact PhysicalForestMarkedRay.coefficient S F arg K B z tag Y well t (swept R N i per hi F tag) _
    exact field.trans (rays t d (Order.order_limit r (Join.right s.val)) z)
  · have hq:Join.left s.val=C.quiet:=of_not_not (mt (hot_iff_ne _).2 has)
    have ho:Join.left s.val≠old.val:=fun h=>has (h.symm ▸ old.property)
    have hf:Join.left s.val≠fresh.val:=fun h=>has (h.symm ▸ fresh.property)
    simp only [driver,if_neg has,if_pos hq,if_neg ho,if_neg hf,add_zero,map_smul,smul_eq_mul,WilsonOriginalGaussianFibre.reading]

local notation "absPhase" => shot S F (prediction R N i per) (ratio R) (covered R N i per)

omit [Fintype A] [Fintype H] in
theorem displaced (simple:G.Simple)(x:Option A×Option H):
    Wick rangeSpace q₀ (raiseE φ*option (fun a=>placed (U a)) x.1*option (fun b=>placed (W b)) x.2)=
      Wick rangeSpace q₀ (raiseE absPhase*loom (slice R N i per F) (option U x.1*option W x.2)):=by
  obtain ⟨u,w⟩:=x
  let T:=option U u*option W w
  have together:retool (shift R N i per hi F) (loom (slice R N i per F) T)=
      option (fun a=>placed (U a)) u*option (fun b=>placed (W b)) w:=by
    cases u <;> cases w <;> simp [T,option,forward]
  have exactField:= (WilsonOriginalFoldedChartPayload.original R N i per hi F tag simple (loom (slice R N i per F) T)).1.symm
  rw [together,←mul_assoc] at exactField
  exact exactField

def stockAt (field:Option A×Option H→Ink rangeSpace):Poly (Board C r):=
  stock C r (flatten B) (fun x:Option A×Option H=>charge C old.val a x.1*charge C fresh.val b x.2) field

def moved (x:Option A×Option H):Ink rangeSpace:=
  Wick rangeSpace q₀ (raiseE absPhase*loom (slice R N i per F) (option U x.1*option W x.2))

private theorem moved_stock (simple:G.Simple):
    stockAt R i per B old fresh a b r (fun x:Option A×Option H=>
      Wick rangeSpace q₀ (raiseE φ*option (fun y=>placed (U y)) x.1*option (fun y=>placed (W y)) x.2))=
    stockAt R i per B old fresh a b r (moved R N i per hi F tag U W):=by
  apply congrArg (stockAt R i per B old fresh a b r)
  funext x
  exact displaced R N i per hi F tag U W simple x

private theorem centered {T:Type}[CommRing T](P:PowerSeries T):
    constantCoeff (P-PowerSeries.C (constantCoeff P))=0:=by simp

theorem actual (simple:G.Simple)(e:ℕ)(Z:SeriesA G)(well:Bulk.Well Y)
    (rays:Rays R N i per hi F Y B old fresh a b U W r):
    Cloud.prescription q₀ ((K).symm F tag) 0 (driver R N i per hi F tag Y B e Z r)=
      stockAt R i per B old fresh a b r (moved R N i per hi F tag U W):=by
  apply Eq.trans _ (moved_stock R N i per hi F tag B old fresh a b U W r simple)
  exact WilsonOriginalJointGaussianAdmission.admitted C r (flatten B) old fresh φ a b
    (fun x=>placed (U x)) (fun x=>placed (W x)) (centered _) q₀ ((K).symm F tag) _
    (written R N i per hi F tag Y B old fresh a b U W r e Z well rays)

theorem original (simple:G.Simple){m e:ℕ}{Z:ℕ→SeriesA G}{π:ℕ→Layout G}{Γ:ℕ→Pace.Coin}
    (course:Read R N m e Z π Γ)(lo:m ≤ i){σ cash:ℝ}(well:Bulk.Well Y)
    (bank:WilsonVacuumPreResetDatedDeposit.Issued R N (i+1) e (Z (i+1)) σ cash)
    (B₀:Stationary.Link G (coarse R i per))(hr:r≤e+2)
    (rays:Rays R N i per hi F Y (Stationary.arm G (coarse R i per) 1 B₀) old fresh a b U W r):
    let held:=Stationary.arm G (coarse R i per) 1 B₀
    let raw:=Bulk.Fk K F tag (QuadraticLocal.Fk.grant (π (i+1)) (Step.tape (e+2)) Y) held r
    let target:=stock C r (flatten held) (fun x:Option A×Option H=>charge C old.val a x.1*charge C fresh.val b x.2)
      (fun x=>Wick rangeSpace q₀ (raiseE absPhase*loom (slice R N i per F) (option U x.1*option W x.2)))
    Comparison.RG02.Order.ratio raw=Comparison.RG02.Order.ratio target ∧ logMarked raw=logMarked target:=by
  intro held raw target
  have paid:=WilsonOriginalEarnedUnaryDriver.original R N i per hi F tag Y course lo well bank B₀ r hr
  have read:=actual R N i per hi F tag Y held old fresh a b U W r simple e (Z (i+1)) well rays
  exact ⟨paid.1.trans (congrArg Comparison.RG02.Order.ratio read),paid.2.trans (congrArg logMarked read)⟩

end YM.Integration.WilsonOriginalJointForestRay
