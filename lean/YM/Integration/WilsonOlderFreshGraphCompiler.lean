import YM.Integration.WilsonOlderFreshGraphCommission

/-! A width, an order and one marked loan determine the renderer tariff
before any Wilson block is elected. Present all real charged ordered tile
arrays to the original compiler in one family, with their actual admission
salary as its test variable. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshGraphCompiler
open Function Filter Finset Lattice Laurent Bloch RG Precision Wilson FormalBulk08
open Next.Free Reef Flat Orb Wick Series Mesa Jets City Cork Bank Wine Dove Dove.Lab
open Exterior Stationary Lotus Shore Gorge Rift Lava Kemp
open Pose Glide Dawn Rial Roof Trellis Aster Borough Elm
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels PowerSeries
open PhysicalNext.Repeat.Legato Next.Foundations PhysicalNext PhysicalNext.Repeat
open RG.Supply Org QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Mentor Push.PriceCompiler
open Primer AllOrder AllOrder.Ink AllOrder.Floe Primitives.TwoWave QuadraticLocal.Poetry
open WilsonOlderFreshGraphSchool WilsonFundedWindowMenu WilsonWindowJointPurchase
open scoped Topology ENNReal BigOperators Classical

open QuadraticLocal.Poetry QuadraticLocal.Sunrise.Aviary QuadraticLocal.Earn
open AllOrder.Ink.Money Primitives.TwoWave
variable {G:Gauge} {d Q:ℕ}

abbrev ArrayBank (G:Gauge) (d:ℕ) := (e:ℕ)→(r:Fin (d+e+1))→Tile (Biglot (Loc G 1)) r.val
def diagram (t:ArrayBank G d) (e:ℕ):Ink.Field (Loc G 1⊕Unit):=WilsonOlderFreshGraphInk.all (t e)

structure Submission (G:Gauge) (d Q:ℕ) (a:ℝ) where
  bank : ArrayBank G d
  wage : ℝ
  wage0 : 0 ≤ wage
  earned : ∀j,j ≤ Q→(diagram bank j).Good a wage (j+d+2)
  witness : ∀j,j ≤ Q→∀u,Focus.Depicted {()} ((diagram bank j).slip u)
  ward : ∀n:Side,∀s:Board Unit n ℝ,∀j,j ≤ Q→Haiku.Vernal G n
    (fun e A=>(diagram bank e).table n (mingle A s)) j

def strip (I:Unit→Loan) (Q:ℕ) (a:ℝ):=Agenda.path a I {()} Q (Q+1)

structure Press (G:Gauge) (I:Unit→Loan) (d Q:ℕ) (a:ℝ) where
  emit : ℕ→Submission G d Q a→Poetry.Roll G Unit
  cap : ℝ
  positive : 0 ≤ cap
  rental : Fin (Q+1)→Submission G d Q a→ℝ
  uniform : ∀p,(∑j,rental j p) ≤ cap*(1+p.wage)
  priced : ∀(j:Fin (Q+1))(p:Submission G d Q a),
    (emit j.val p).Faith {()} () (j.val+d+2) (strip I Q a) (rental j p) ∧ (emit j.val p).honest
  reading : ∀j,j ≤ Q→∀(p:Submission G d Q a)(n:Side)(A:Board (Loc G 1) n ℝ)(s:Board Unit n ℝ),
    (diagram p.bank j).table n (mingle A s) =
      ∑l∈Finset.range (Q+1),((emit l p).folded l j).table n (mingle A s)

theorem ready (G:Gauge) (d Q:ℕ) (a:ℝ) (I:Unit→Loan) (level:(I ()).toll=d) (ha:0<a):
    Nonempty (Press G I d Q a):=by
  classical
  by_cases h:Nonempty (Submission G d Q a)
  · letI := h
    let Γ:Submission G d Q a→ℝ:=Submission.wage
    let T (e:ℕ)(p:Submission G d Q a):=diagram p.bank e
    have enrolled : Aviary.Marquis I Γ {()} a Q 1 T:=by
      refine ⟨ha,?_,?_,?_⟩
      · intro j hj
        refine ⟨Γ,⟨1,zero_le_one,fun p=>⟨p.wage0,?_⟩⟩,?_⟩
        · simp [Γ,abs_of_nonneg p.wage0]
        · intro p
          simpa [T,Γ,Aviary.plusK,level] using p.earned j hj
      · exact fun j hj p=>p.witness j hj
      · exact fun n s j hj p=>p.ward n s j hj
    obtain ⟨P,hP⟩:=Agenda.volume {()} () I T enrolled (by simp)
    have input (j:Fin (Q+1)):Agenda.Booked {()} () I (P j.val) Γ j.val (2*(strip I Q a/2)) 1:=by
      rw [show 2*(strip I Q a/2)=strip I Q a by ring]
      exact hP.booking j.val j.isLt
    obtain ⟨b,hb,C,_,fund,mass⟩:=WilsonOlderFreshGraphTariff.original I level
      (fun j:Fin (Q+1)=>P j.val) _ _ input
    refine ⟨⟨P,b,hb,C,?_,?_,?_⟩⟩
    · intro p
      simpa only [Γ,abs_of_nonneg p.wage0] using mass p
    · intro j p
      simpa only [show 2*(strip I Q a/2)=strip I Q a by ring] using fund j p
    · exact fun j hj p n A s=>hP.recollects j (Nat.lt_succ_of_le hj) p n A s
  · refine ⟨⟨fun _ p=>False.elim (h ⟨p⟩),0,le_rfl,fun _ _=>0,
      fun p=>False.elim (h ⟨p⟩),fun _ p=>False.elim (h ⟨p⟩),fun _ _ p=>False.elim (h ⟨p⟩)⟩⟩

def before_block (G:Gauge) (d Q:ℕ) (a:ℝ) (I:Unit→Loan) (level:(I ()).toll=d) (ha:0<a):
    Press G I d Q a:=Classical.choice (ready G d Q a I level ha)

end YM.Integration.WilsonOlderFreshGraphCompiler
end
