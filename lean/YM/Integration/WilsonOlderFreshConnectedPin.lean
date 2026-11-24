import YM.Integration.WilsonOlderFreshConnectedRoll
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshConnectedPin
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
variable {G:Gauge}{n e m N l b t:ℕ}{A:ℝ}{k D:Fin n    →    ℕ}{S J:Finset (Fin n)}{c:Fin n}


open WilsonOlderFreshConnectedBoard Push.PriceCompiler

open QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Poetry
open WilsonOlderFreshConnectedLamp WilsonOlderFreshGraphSlate WilsonOlderFreshConnectedRoll
variable (Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor  ≤  m)(X:Input Q hm S k D A)
variable (J:Finset (Fin n))(c:Fin n)(l N:ℕ)(o:Cover)(v:Case D)

variable (u:Frill J c)

def selected (j:ℕ):Poetry.Roll G Unit:=
  ⟨{z:Page (G:=G) J c l j//z.2.1.1=u},fun z=>(roll Q hm X J c l N o v j).leg z.val⟩

theorem paid (j:ℕ){M w:ℝ}(w0:0 ≤ w)
    (issued:∀r:Fin (l+j+1),Rooted Q hm X J c l N w M o j r):
    (selected Q hm X J c l N o v u j).Faith {()} () (j+l+2) w (cost J l j v M):=by
  have h:=faith Q hm X J c l N o v j w0 issued
  exact ⟨fun z=>h.1 z.val,Push.Local.sumBudget_subtype (fun z:Page (G:=G) J c l j=>z.2.1.1=u) h.2⟩

def book (w M:ℝ)(positive:0<l)(sw:0 ≤ w)
    (issued:∀j,j ≤ e → ∀r:Fin (l+j+1),Rooted Q hm X J c l N (2*w) M o j r):Copy G l e w where
  roll j:=selected Q hm X J c l N o v u j
  fare j:=cost J l j v M
  paid j:=paid Q hm X J c l N o v u j (by positivity) (issued _ (Nat.le_of_lt_succ j.isLt))
  legal j z:=ward Q hm X J c l N o v j z.val
  positive:=positive

theorem heard (j:ℕ)(r:Fin (l+j+1))(z:RadP G r.val){w M:ℝ}
    (issued:Rooted Q hm X J c l N w M o j r){n':Side}(U:Config G n')(a:Site n'):
    ∑i, ((selected Q hm X J c l N o v u j).leg ⟨⟨r,(u,z),i⟩,rfl⟩).atom.unmasked U a =
      (Rolls.dip (packet Q hm X J c l N o j r (u,z)) (touch v J)).unmasked U a:=
  WilsonOlderFreshConnectedRoll.exact Q hm X J c l N o v j r (u,z) issued U a

theorem income {w M:ℝ}(positive:0<l)(sw:0 ≤ w)
    (issued:∀j,j ≤ e → ∀r:Fin (l+j+1),Rooted Q hm X J c l N (2*w) M o j r):
    ∑j:Fin (e+1),(book Q hm X J c l N o v u w M positive sw issued).fare j  ≤ 
      (e+1:ℕ)*((l+e+1:ℕ)*((∏i∈J,‖v i‖)*M)):=by
  have hM:0 ≤ M:=by
    obtain ⟨_,_,_,h,_⟩:=issued 0 (Nat.zero_le _) ⟨0,by omega⟩
    exact (tsum_nonneg h.1).trans h.2.2
  have h:=mul_nonneg (Finset.prod_nonneg (fun i (_:i∈J)=>norm_nonneg (v i))) hM
  calc
    _ ≤ ∑_:Fin (e+1),((l+e+1:ℕ):ℝ)*((∏i∈J,‖v i‖)*M):=by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right _ h
      exact_mod_cast (show l+j.val+1 ≤ l+e+1 by have hj:=j.isLt;omega)
    _=_:=by simp [nsmul_eq_mul]
end YM.Integration.WilsonOlderFreshConnectedPin
end
