import YM.Next.FREE_KERNELS.Rack
import YM.OPE.Compatible.Aroma.Clasp
import YM.OPE.Compatible.Rhus.Scar
import YM.Next.STATIONARY.FullPlanned
/-! # Propagate aesthetic PathData at patch. Quantifier setup. K factual from tangent Prog. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Votive
open Function Filter Lattice Laurent MeasureTheory RG Finset Next.Free Exterior WithLp Work.F08 Matrix Bloch Precision Stationary
open scoped Topology BigOperators Classical
variable {G:Gauge}{σ γ x y a b d δ C A c z :ℝ}{j i u:ℕ}{P : MapPrices}{T Z:Patch}{D:Stationary.Fluent G}
-- Uniform budgets m of any auxiliary path. Stash X,p.quote
structure Sponsor (G:Gauge) where
   K : KernelChoices
   X : MapPrices
   l : ℕ→ℝ
   γ : ℕ→ℝ
   b : ℕ→ℕ
   h : Catalog K X l γ b
   affordable (P:Patch) : P.Branches K G
variable (B:Sponsor G)
def TicketBed (K:Sponsor G)(i:ℕ)(p:Clip)(U:Train i)(X:Bed):Prop:= p.direct ≤ K.γ i ∧ Defined K.K.penalty (K.l i) U X∧ X.covered (K.X.α i) (K.X.Ω i) ∧ (∀ n:Side, Floor X p n (K.X.η i) (K.X.Ω i))∧(∀ n:Side, Bid.Sworn X n G)
lemma atBed (K:Sponsor G)(p:Clip)(h:p.direct ≤ K.γ i) (hi:4 ≤ i)(U:Train i): ∃ X,TicketBed K i p U X:=by
   obtain ⟨X,hX,hc,hp,hv,hK⟩:= K.h.bottom i hi p h U; exact ⟨X,h,hX,hc,hp,fun n=>hv n _⟩ -- hv order
lemma ticket_hull (p:Clip)(U:Train i)(X:Bed)(h:TicketBed B i p U X)(m:ℕ→Side) : Stationary.Hull X (B.X.η i) (B.X.α i) (pacesE B.X i) p m G:=by
    obtain ⟨hb,h,hK,hg,H⟩:=h; have hx:=cover_revise hK le_rfl (paces_extend _ _); exact ⟨hx.2.1,hx.2.2.2.1,fun n=>floor_revise (hg n) le_rfl (paces_extend ..),fun _=> H _⟩
-- joint β predicted property at second order on cofinal tori
structure Pilgrim (G:Gauge)(P:Flight j i)(Z: KernelChoices) (p q: Clip)(R T: PathData G) (α:ℝ)(L: ChartRatio G) : Prop where
   cohabit : ∃ m:ℕ→ Side, Tendsto (fun i=>(m i).val) atTop atTop ∧ ∃ Θ χ Λ:ℝ,0<χ∧∀ (k:ℕ), let S:=P.visit (c:=m k) (f:=m k*P.L) Z rfl; let f:= Woody.forest S.ratio P.odd
                                      Bid.Larger (G:=G) S∧ ∃ g, Critical f p R g ∧ ClassicalMatch f p q R T g ∧ FiniteBound f R T p q α L g Θ χ Λ
lemma naturalHigh (P:Patch)(b:KernelChoices)(h:P.Branches b G):∃ m:ℕ→Side, Tendsto (fun i=>(m i).val) atTop atTop ∧ ∀ i:ℕ,Bid.Larger (G:=G) (StepData.mk (c:=m i) (f:=m i * P.L) P b rfl):=by
    let v(i:ℕ):Side:=⟨i+(100*Pressure.macroR P+2),by omega⟩; refine ⟨v,tendsto_add_atTop_nat _,fun i=>⟨h,?_,?_⟩⟩
    · change 100* Pressure.macroR P ≤ (v i).val*P.L.val; exact (show 100*Pressure.macroR P ≤ (v i).val from by dsimp [v]; omega).trans (Nat.le_mul_of_pos_right _ P.L.pos)
    change 1< i+(100*Pressure.macroR P+2); omega -- `Side` order coer
end YM.OPE.Votive
