import YM.Integration.WilsonOlderFreshConnectedLamp
import YM.Integration.WilsonOlderFreshConnectedAppointment
import YM.Integration.WilsonOlderFreshGraphSlate
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshConnectedRoll
open Function Filter Finset MeasureTheory Lattice RG Precision Wilson Tree Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology
variable {G:Gauge}{n e m N l b t:ℕ}{A:ℝ}{k D:Fin n   →   ℕ}{S J:Finset (Fin n)}{c:Fin n}


open WilsonOlderFreshConnectedBoard Push.PriceCompiler

open QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Poetry
open WilsonOlderFreshConnectedLamp WilsonOlderFreshGraphSlate
variable (Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)(X:Input Q hm S k D A)
variable (J:Finset (Fin n))(c:Fin n)(l N:ℕ)(o:Cover)(v:Case D)
abbrev Words (J:Finset (Fin n))(c:Fin n)(r:ℕ):=Frill J c × RadP G r
abbrev Page (J:Finset (Fin n))(c:Fin n)(l j:ℕ):=Σ r:Fin (l+j+1),Σ _x:Words (G:=G) J c r.val,Stationary.Ink G r.val

def packet (j:ℕ)(r:Fin (l+j+1))(x:Words (G:=G) J c r.val): Comet G (Pen D J) r.val:=
  packetH J (output X J N) l (e+1) c o x.1 j r x.2

def roll (j:ℕ):Poetry.Roll G Unit:=
  ⟨Page (G:=G) J c l j,fun z=>lamp (packet Q hm X J c l N o j z.1 z.2.1) v z.2.2⟩

theorem ward (j:ℕ):(roll Q hm X J c l N o v j).honest:=
  fun z=>WilsonOlderFreshConnectedLamp.lawful (packet Q hm X J c l N o j z.1 z.2.1) v z.2.2 

def cost (J:Finset (Fin n))(l j:ℕ)(v:Case D)(M:ℝ):ℝ:=
  ((l+j+1:ℕ):ℝ)*((∏i∈J,‖v i‖)*M)

theorem faith (j:ℕ){M w:ℝ}(w0:0 ≤ w)
    (issued:∀r:Fin (l+j+1),Rooted Q hm X J c l N w M o j r):
    (roll Q hm X J c l N o v j).Faith {()} () (j+l+2) w (cost J l j v M):=by
  let B:=∏i∈J,‖v i‖
  have b0:0 ≤ B:=Finset.prod_nonneg (fun _ _=>norm_nonneg _)
  constructor
  · intro z
    apply WilsonOlderFreshConnectedLamp.aperture
    exact Nat.le_of_lt_succ z.1.isLt
  · change SumBudget (fun z:Page (G:=G) J c l j=>(lamp (packet Q hm X J c l N o j z.1 z.2.1) v z.2.2).money w) _
    apply Push.Local.sumBudget_sigma (a:=fun _:Fin (l+j+1)=>B*M)
    · intro r
      obtain ⟨μ,born,_heard,raw,_dressed⟩:=issued r
      let W:=packet Q hm X J c l N o j r
      let paid:=fun x:Words (G:=G) J c r.val=> Real.exp (w*feeH (toe J c o x.1) c J) * lease (W x) (μ x) w
      have paid0: SumBudget paid M:=raw
      apply Push.Local.sumBudget_sigma (a:=fun x:Words (G:=G) J c r.val=>B*paid x)
      · intro x
        refine ⟨fun i=>(lamp (W x) v i).fee_nn w,(hasSum_fintype _).summable,?_⟩
        rw [tsum_fintype]
        have h:=WilsonOlderFreshConnectedLamp.paid (W x) v (μ x) (born x) w
        have extra: 1 ≤ Real.exp (w*feeH (toe J c o x.1) c J):=Real.one_le_exp (mul_nonneg w0 (Nat.cast_nonneg _))
        exact h.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (stripV_n ..) extra) b0)
      · exact Push.Local.sumBudget_mul_left paid0 b0
    · have hM:0 ≤ M:=by
        obtain ⟨_,_,_,h,_⟩:=issued (⟨0,by omega⟩)
        exact (tsum_nonneg h.1).trans h.2.2
      refine ⟨fun _=>mul_nonneg b0 hM,(hasSum_fintype _).summable,?_⟩
      rw [tsum_fintype]
      simp only [Finset.sum_const,Fintype.card_fin,Finset.card_univ,nsmul_eq_mul]
      rfl

def booked (w M:ℝ)(positive:0<l)(sw:0 ≤ w)
    (issued:∀j,j ≤ e → ∀r:Fin (l+j+1),Rooted Q hm X J c l N (2*w) M o j r):Copy G l e w where
  roll j:=roll Q hm X J c l N o v j
  fare j:=cost J l j v M
  paid j:=faith Q hm X J c l N o v j (by positivity) (issued _ (Nat.le_of_lt_succ j.isLt))
  legal j:=ward Q hm X J c l N o v j
  positive:=positive

theorem exact (j:ℕ)(r:Fin (l+j+1))(x:Words (G:=G) J c r.val){w M:ℝ}
    (issued:Rooted Q hm X J c l N w M o j r){n':Side}(U:Config G n')(a:Site n'):
    ∑i, ((roll Q hm X J c l N o v j).leg ⟨r,x,i⟩).atom.unmasked U a =
      (Rolls.dip (packet Q hm X J c l N o j r x) (touch v J)).unmasked U a:=by
  obtain ⟨μ,born,hear,_raw,_⟩:=issued
  let P:=packet Q hm X J c l N o j r x
  calc
    _=∑i,(∫y:Sky D,Express.mica v J y ∂μ x i)*(sprigB P i).unmasked U a:=by
      apply Finset.sum_congr rfl
      intro i _
      rw [show (∫y:Sky D,Express.mica v J y ∂μ x i)=(touch v J) (P.wage i)
        from ((born x i).2.2.2 v).symm]
      exact WilsonOlderFreshConnectedLamp.value P v i U a
    _=_:=(hear x v U a).symm

end YM.Integration.WilsonOlderFreshConnectedRoll
end
