import YM.Integration.WilsonMeasuredPublicEntranceOrderedRoster
import YM.Integration.WilsonMeasuredPublicEntranceSeparatedPins
import YM.Integration.WilsonReflectedPublicOrientedFaces
/-! At a fixed reporting date every member of a finite stencil uses the same selected weak and pooled fields at the original cutoff. The bound on their current projections holds on the two ordered regulator tails. Their named values are then identified on the appointed subfilter. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferForkNodes
open Function Filter Finset Set Extraction Spec Table Lattice RG Wilson Source OPE Cells
open PhysicalNext.Repeat.Legato Trace.Terrace Next.UVStress Climb Extra.Multi Extra.Histories
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMeasuredPublicEntranceOrderedRoster (raw enrolled)
open WilsonMeasuredPublicEntranceOrderedPins (physical publicValue Release)
open WilsonReflectedPublicOrientedFaces (displayed)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}(F:Final R.family order S)
  {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{arch:Arch R.family}{D T n:ℕ}
  {r:Fin n→ ℝ}(books:∀i,Book F (l:=l) H arch D T (r i))
  (d:Fin n→ Fin (D+1))(name:∀i,Bool→ S.Field (d i).val)
local notation "C₀" => R.family
local notation "ds" => (fun i : Fin n => Fin.val (d i))

def rotation (e:ℕ):ℝ:=∑s:Signed,‖(((C₀).labels.level e).act s.ortho).toContinuousLinearMap‖

theorem bound (e:ℕ)(x:(C₀).label e)(t:Motion):
    ‖displayed R e x t‖≤rotation (R:=R) e*‖x‖:=by
  classical
  let L:=fun s:Signed=>(((C₀).labels.level e).act s.ortho).toContinuousLinearMap
  have one:‖L t.1‖≤rotation (R:=R) e:=Finset.single_le_sum (f:=fun s:Signed=>‖L s‖)
    (fun s _=>norm_nonneg _) (Finset.mem_univ t.1)
  have same:‖(if t.2 then star x else x)‖=‖x‖:=by split <;> simp
  exact ((L t.1).le_opNorm _).trans (by rw [same];gcongr)

theorem continuous (e:ℕ)(t:Motion):Continuous (fun x:(C₀).label e=>displayed R e x t):=by
  unfold displayed
  apply (((C₀).labels.level e).act t.1.ortho).continuous_of_finiteDimensional.comp
  split
  · exact continuous_star
  · exact continuous_id

def marked (b:Fin n→ Bool)(t:Fin n→ Motion)(z:ℕ×ℕ)(i:Fin n):(C₀).label (d i).val:=
  displayed R (d i).val (raw F books d name i (b i) z) (t i)

def represents (b:Fin n→ Bool)(t:Fin n→ Motion)(i:Fin n):(C₀).label (d i).val:=
  displayed R (d i).val (enrolled F books d name i (b i)).label (t i)

theorem named (simple:G.Simple)(below:(l:Filter _)≤order.fuse)(f:ℕ)(o:Fin n→ Cover)
    (safe:Extraction.Order.grid (C₀) f o∈conf n)(b:Fin n→ Bool)(t:Fin n→ Motion):
    Tendsto (fun z:ℕ×ℕ=>physical (C:=C₀) ds f o z.1 z.2 (marked F books d name b t z))
      (l:Filter _) (𝓝 (publicValue (C:=C₀) (S:=S) ds f o (represents F books d name b t))):=by
  have data:=WilsonMeasuredPublicEntranceSeparatedPins.variation R F ds f o simple below
    (marked F books d name b t) (represents F books d name b t)
    (fun i=>((continuous (R:=R) (d i).val (t i)).tendsto _).comp (enrolled F books d name i (b i)).approaches) safe
  unfold publicValue
  rw [S.class_agrees S F.room.kernel.laws.toSymmetric (fun _=>le_rfl) ds safe]
  exact data

theorem original:
    ∃first:ℕ,∃cap:Fin n→ ℝ,
      (∀N p,first≤N→ ∀b t i,‖marked F books d name b t (N,p) i‖≤cap i) ∧
      ∀f:ℕ,∀sites:Finset (Fin n→ Cover),
        (∀o∈sites,Extraction.Order.grid (C₀) f o∈YM.generic n)→ 
        (∀o∈sites,Nonempty (Release (C:=C₀) (S:=S) (order:=order) ds f o cap)) ∧
        ∀ε:ℝ,0<ε→ order.late fun N p=>∀o∈sites,∀b t,
          ‖physical (C:=C₀) ds f o N p (marked F books d name b t (N,p))-
            publicValue (C:=C₀) (S:=S) ds f o (marked F books d name b t (N,p))‖≤ε:=by
  classical
  obtain ⟨first,income,_,wage,_⟩:=WilsonMeasuredPublicEntranceOrderedRoster.original F books d name
  let cap:=fun i=>rotation (R:=R) (d i).val*max (income i true) (income i false)
  have paid:∀N p,first≤N→ ∀b t i,‖marked F books d name b t (N,p) i‖≤cap i:=by
    intro N p late b t i
    apply (bound _ _ _).trans
    apply mul_le_mul_of_nonneg_left _ (Finset.sum_nonneg fun _ _=>norm_nonneg _)
    apply (wage N p late i (b i)).trans
    cases b i
    · exact le_max_right ..
    · exact le_max_left ..
  refine ⟨first,cap,paid,?_⟩
  intro f sites safe
  have issued:∀o∈sites,Nonempty (Release (C:=C₀) (S:=S) (order:=order) ds f o cap):=
    fun o inside=>WilsonMeasuredPublicEntranceOrderedPins.original F ds f o (safe o inside) cap
  refine ⟨issued,?_⟩
  intro ε ep
  let P:=fun (z:ℕ×ℕ) (o:Fin n→ Cover)=>∀y:(C₀).book.Vector ds,(∀i,‖y i‖≤cap i)→ 
    ‖physical (C:=C₀) ds f o z.1 z.2 y-publicValue (C:=C₀) (S:=S) ds f o y‖≤ε
  have all:∀ᶠz in order.fuse,∀o∈sites,P z o:=by
    apply (Finset.eventually_all _).mpr
    intro o inside
    exact (order.fused _).mpr (WilsonMeasuredPublicEntranceOrderedPins.ordered ds f o (issued o inside).some ep)
  have scheduled:order.late fun N p=>first≤N:=by
    exact Filter.Eventually.of_forall fun _=>order.mesh.cofinal.eventually (eventually_ge_atTop first)
  filter_upwards [(order.fused _).mp all,scheduled] with volume columns late
  filter_upwards [columns,late] with uv bought live
  intro o inside b t
  exact bought o inside _ (paid _ _ live b t)

end YM.Integration.WilsonMeasuredPublicEntranceTransferForkNodes
end
