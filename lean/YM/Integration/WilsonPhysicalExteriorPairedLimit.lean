import YM.Integration.WilsonPhysicalExteriorFundedRows
import YM.Integration.WilsonPhysicalExteriorFieldGram
import YM.Integration.MSDeckProbeGram
import YM.FVA2.Tiles

/-! One original two-site gauge experiment, shared by every subtraction
argument and all field probes. Its actual limiting square at tree order
is the nondegenerate MS physical Gram. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorPairedLimit
open Function Filter Finset Lattice PhysicalNext.Repeat.Legato
open MS MS.Land MS.Rake MS.Dial MS.Tide MS.Menus MS.Theater MS.Tone
open FVA2 FVA2.ColorCode FVAAlt2 Lobby Precision RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Lodge
open Pert Pert.Position Pert.Scale Extra.FD OPE.Levy RG11.Fields
open WilsonPhysicalExteriorFieldGram
open scoped Classical BigOperators Topology
variable {G:Gauge}{B:MS.Local.Physical.Deck G}{O:Booked B}
variable (R:Run G) (M:MS_Data G O) (Q:Prescription B)
local notation "PS" => PowerSeries ℂ

def observed (T:Trial ℕ (Fin 2)) (d h:ℕ) (μ:ℝ) (i:ℕ) :=
  pair R.metals.O (basisR R) Q d h (situated T i) (spacing T i) (μ-T.profile.θ i)

def limit (x:Fin 2→QP) (d h:ℕ) (μ:ℝ) (k:ℕ) (a:Glyph B d) (b:Glyph B h) :=
  Dial.tour M ![owner a,owner b] μ x univ k

def Read (T:Trial ℕ (Fin 2)) (x:Fin 2→QP) : Prop :=
  Tendsto T.profile.θ atTop atTop ∧ ∀ μ:ℝ,∀ d h k:ℕ,∀ a:Glyph B d,∀ b:Glyph B h,
    Tendsto (fun i=>PowerSeries.coeff k (observed R Q T d h μ i a b)) atTop
      (𝓝 (limit M x d h μ k a b))

theorem actual (hG:G.Simple) (paid:TaylorOKPl M (Lobby.Table (basisR R) B) Q)
    (x:Fin 2→QP) (hx:Injective x): ∃ T:Trial ℕ (Fin 2), Read R M Q T x := by
  let q:Side:=⟨2,by decide⟩
  let o (j:ℕ):Cover:=fun _=>(Tiles.cells q j:ℤ)
  have ho (j:ℕ): Tiles.Daily q j (o j):=by
    intro i;change (Tiles.cells q j:ℤ)≤Tiles.cells q j ∧ (Tiles.cells q j:ℤ)≤(2*Tiles.cells q j:ℕ)
    exact ⟨le_rfl,by exact_mod_cast (by omega : Tiles.cells q j≤2*Tiles.cells q j)⟩
  let T:=Tiles.ladder x q 0 o 0
  refine ⟨T,Tiles.forward q (by decide:1<q.val),?_⟩
  intro μ d h k a b
  let u:Fin 2→Label B:=![owner a,owner b]
  obtain ⟨m,hm⟩:=Tiles.ranges q (by decide:1<q.val) μ x hx
  let S:=Tiles.ladder x q μ o m
  obtain ⟨hs,foot⟩:=hm o ho
  obtain ⟨vol,hv⟩:=Dial.check_tPl M (Lobby.Table (basisR R) B) u S paid hs hG true
  have twins:=Lobby.twins R.metals.O (basisR R) Q u M R.alloy.B.ratio hs hv k
  have conv:=((Dial.contin M u x hx univ k μ).1.tendsto).comp foot
  apply (tendsto_add_atTop_iff_nat m).mp
  exact Dial.agrees S twins hs.upright conv

theorem head (V:Warehouse G) (p q:E4) (hp:p≠q) (d:ℕ) (μ:ℝ) :
    IsUnit (show Matrix (Glyph B d) (Glyph B d) ℂ from limit M (Fountain.metric (couple p q)) d d μ 0) := by
  have eq:(show Matrix (Glyph B d) (Glyph B d) ℂ from limit M (Fountain.metric (couple p q)) d d μ 0)=
      MSDeckProbeGram.matrix M d p q μ 0 := by
    apply Matrix.ext;intro a b
    unfold limit MSDeckProbeGram.matrix MSDeckProbeGram.raw
    congr 1;funext i;fin_cases i <;> rfl
  rw [eq];exact MSDeckProbeGram.invertible V M μ hp d

end YM.Integration.WilsonPhysicalExteriorPairedLimit
end
