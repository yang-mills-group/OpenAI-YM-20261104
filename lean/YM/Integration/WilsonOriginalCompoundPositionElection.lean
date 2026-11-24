import YM.Integration.WilsonOriginalCompoundVertexStrip
import YM.Integration.WilsonOriginalBlissReflectedElection

/-! Buy the original compound strip, finite conditional forests and covered
vacuum vertices with the one physical Wilson/MS prescription. Additional
receipts can be joined before the original course is selected. -/
set_option autoImplicit false
noncomputable section
universe u
namespace YM.Integration.WilsonOriginalCompoundPositionElection
open Function Filter Wilson
open WilsonLimitConstruction.FundedCompanySelection
variable {G:Gauge}

def Invoice (Q:WilsonOriginalCompoundStrip.Request G):Prediction G:=
  WilsonWindowJointPurchase.Together
    (WilsonWindowJointPurchase.Together (@WilsonOriginalCompoundStrip.Filed G Q)
      (@WilsonOriginalCompoundLodge.Filed G))
    (@WilsonOriginalCompoundVertex.Filed G)

theorem prepaid (Q:WilsonOriginalCompoundStrip.Request G)(simple:G.Simple):
    WilsonFundedWindowMenu.AllPrices (@Invoice G Q):=by
  intro s price
  exact WilsonWindowJointPurchase.joint
    (WilsonWindowJointPurchase.joint
      (WilsonOriginalProfileStrip.prepaid (WilsonOriginalCompoundStrip.programme Q) simple s _)
      (WilsonEmittedDictionaryForecast.prepaid _ s _))
    (WilsonOriginalCompoundVertex.prepared (fun _ _=>0) s price)

noncomputable abbrev funded (Q:WilsonOriginalCompoundStrip.Request G)(cap U:ℕ→ℕ)
    (mono:Monotone cap)(simple:G.Simple){ε:ℝ}(pos:0<ε):=
  WilsonOriginalBlissReflectedElection.funded.{u} (@Invoice G Q) (prepaid Q simple) cap U mono simple pos

noncomputable abbrev withSupplement (Q:WilsonOriginalCompoundStrip.Request G)(extra:Prediction G)
    (paid:WilsonFundedWindowMenu.AllPrices (@extra))(cap U:ℕ→ℕ)(mono:Monotone cap)
    (simple:G.Simple){ε:ℝ}(pos:0<ε):=
  WilsonOriginalBlissReflectedElection.funded.{u} (WilsonWindowJointPurchase.Together (@Invoice G Q) (@extra))
    (fun s price=>WilsonWindowJointPurchase.joint (prepaid Q simple s price) (paid s price)) cap U mono simple pos

end YM.Integration.WilsonOriginalCompoundPositionElection
end
