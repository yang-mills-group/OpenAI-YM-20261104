import YM.Integration.WilsonOlderFreshSoftSocketHistory
import YM.Integration.WilsonOlderFreshSoftSocketOpening

/-! The actual fixed socket supplies the initial scalar-series identity on all finite directions and all signed test components. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshSoftSocketDeposit
open Laurent Bloch Precision WilsonCoeffUV.Blue WilsonCoeffUV.Power Work.F08 AnalyticNext.QuarticMatch.Sheets MultiNext.SignedSource Tree
open Function Finset Lattice Wilson RG Source Labels Comparison.RG02
open WilsonCoeffUV WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Embroider
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Soil WilsonCoeffUV.Cosmos
open OriginalMarkedSourceComet IndependentSourcePathFamily WilsonThermometerDeclaredSeeds
open WilsonReceivedCanonicalVerseRegister (offer start)
open FormalBulk08 WilsonCoeffUV.Winding PhysicalNext.Repeat.Legato
open scoped Classical BigOperators
variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I]{D:I→ℕ}

theorem mapped {V W U:Type}[NormedAddCommGroup V][NormedAddCommGroup W][NormedSpace ℝ V][NormedSpace ℝ W]
    (f:V→ₗ[ℝ]W)(C:Blue.Cost)(Y:Pal V U):ply f (affix C Y)=affix C (ply f Y):=by
  funext e r x
  simp only [ply_v,affix,Finset.sum_apply,Pi.smul_apply,map_sum,map_smul]

omit [DecidableEq I] [Fintype I] in
theorem inputs {S:Finset I}{k:ℕ}(P Q:Era G (Pen D S))(C:Blue.Cost)(hp:Auth k P)(hq:Auth k Q)
    (printed:∀(A:Case D)(n:Side),readO A P n=Blue.soil C * readO A Q n):
    ∀n,P.1 n=affix C (Q.1 n):=by
  intro n
  funext i r x
  apply pen_inj
  intro A
  have words:flash (pPly A S (P.1 n))=flash (pPly A S (affix C (Q.1 n))):=by
    rw [show pPly A S (affix C (Q.1 n))=affix C (pPly A S (Q.1 n)) from mapped ..]
    rw [sponsor _ _ (ply_shell (touch A S).toLinearMap (hq.span n))]
    exact printed A n
  have all:=by_flash (ply_shell (touch A S).toLinearMap (hp.span n))
    (ply_shell (touch A S).toLinearMap (affix_shell C _ (hq.span n)))
    (fun i=>ply_pure _ (hp.pale n i)) (fun i=>ply_pure _ (aspire C _ (hq.pale n) i)) words
  exact congr_fun (congr_fun (congr_fun all i) r) x

variable (R:Run G)(d:I→ℕ)(κ:(i:I)→Knob (D i))(pt:I→Chamber)(q:(i:I)→Choice R d i)(z:I → Cover)
local notation "hi_" => WilsonOlderFreshSoftSocketPole.raw R d κ pt q
local notation "lo_" => WilsonReceivedCanonicalVerseRegister.offer R d κ pt q
local notation "lag_" => WilsonOlderFreshSoftSocketPole.lag R d q

theorem original (S:Finset I)(f:Pen D S→L[ℝ]ℝ)(n:Side):
    (tuftV f (levelsO (independent (hi_) z) S)).1 n=affix (PowerSeries.X^(∑i∈S,lag_ i))
      ((tuftV f (levelsO (start R d κ pt q z) S)).1 n):=by
  let C:Blue.Cost:=PowerSeries.X^(∑i∈S,lag_ i)
  have h:Eu d (independent (hi_) z):=legal _ _ fun _ _=>Nat.le_add_left _ _
  have l:Eu d (start R d κ pt q z):=legal _ _ fun i _=>WilsonReceivedCanonicalVerseBasis.grade R d κ pt i (q i)
  have a:=inputs (levelsO (independent (hi_) z) S) (levelsO (start R d κ pt q z) S) C
    (placedO _ h _) (placedO _ l _) (fun A n=>by
      simpa only [C,Blue.soil,map_pow,PowerSeries.map_X] using
        WilsonOlderFreshSoftSocketOpening.ordinary R d κ pt q z A n S) n
  change ply f.toLinearMap _=affix C (ply f.toLinearMap _)
  rw [a,mapped]

end YM.Integration.WilsonOlderFreshSoftSocketDeposit
end
