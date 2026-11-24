import YM.Integration.WilsonLocalPlaquetteForest

/-! The dated reporting-forest Wilson price, with the literal measured upper
density at the ultraviolet endpoint. The tested coordinates keep their
common exterior pivot at every comparison. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonLocalPlaquetteReporting
open Function Finset Set MeasureTheory Lattice RG Wilson Tree RG16
open PhysicalNext.Repeat.Legato
open WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots WilsonLocalPlaquetteField
open WilsonLocalPlaquetteForest WilsonLocalPlaquetteAction
open scoped Classical BigOperators Matrix.Norms.Frobenius
variable {G:Gauge} {c f:Side} {S:StepData c f}

def charge (p:ℕ) (C β:ℝ) (density:Config G f→ℝ) (T:Forest S.ratio) (B:Finset T.Free)
    (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) (X Y:↥(moving T B)→G.Color) : Prop :=
  let E:=moving T B
  let g:=(Real.sqrt β)⁻¹
  let s:=support T E
  let x:=extend T E X 0
  let y:=extend T E Y 0
  let w:=background T B v
  (∀i:↥E,g*‖X i‖<1 ∧ g*‖Y i‖<1)→
  |Real.log (density (restored T B v (fun i=>G.lieExp (g•X i)))/
    density (restored T B v (fun i=>G.lieExp (g•Y i))))+
    β*booked (p+2) s (filled T E v w) 1 (extend T E w 1) x y g|≤C*g^(p+1)*load (p+3) s x y

theorem received (G:Gauge) (p:ℕ) : ∃C:ℝ,0≤C ∧ ∀(c f:Side) (S:StepData c f) (T:Forest S.ratio)
    (B:Finset T.Free) (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El)
    (X Y:↥(moving T B)→G.Color) (β:ℝ),0<β→charge p C β (bare β) T B v X Y := by
  obtain ⟨C,nonneg,bill⟩:=WilsonLocalPlaquetteAction.measured G p
  refine ⟨C,nonneg,?_⟩;intro c f S T B v X Y β hβ room
  let E:=moving T B
  let g:=(Real.sqrt β)⁻¹
  let w:=background T B v
  rw [entire T B v X g,entire T B v Y g]
  apply bill f (support T E) (filled T E v w) 1 (extend T E w 1) (extend T E X 0) (extend T E Y 0) β hβ
  exact fun i hi=>⟨paid_room T E X g (fun j=>(room j).1) i hi,paid_room T E Y g (fun j=>(room j).2) i hi⟩

theorem dated (R:Run G) (p:ℕ) : ∃C:ℝ,0≤C ∧ ∀N per m:ℕ,m<N→
    ∀(T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free)
    (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) (X Y:↥(moving T B)→G.Color),
    let β:=(R.family.path.rep N per (m+1)).beta
    charge p C β (bare β) T B v X Y := by
  obtain ⟨C,nonneg,bill⟩:=received G p
  exact ⟨C,nonneg,fun N per m live T B v X Y=>bill _ _ _ T B v X Y _ (Overlay.beta_positive R.makes.wilson live)⟩

theorem terminal (R:Run G) (p:ℕ) : ∃C:ℝ,0≤C ∧ ∀m per:ℕ,
    ∀(T:Forest (R.family.path.levels.clock.op m per).ratio) (B:Finset T.Free)
    (v:({e:T.Free|e∉moving T B}:Set T.Free)→G.El) (X Y:↥(moving T B)→G.Color),
    let Q:=R.family.path.rep (m+1) per (m+1)
    charge p C Q.beta Q.eval T B v X Y := by
  obtain ⟨C,nonneg,bill⟩:=dated R p
  refine ⟨C,nonneg,?_⟩;intro m per T B v X Y
  have issued:=bill (m+1) per m (Nat.lt_succ_self m) T B v X Y
  dsimp only
  have source : (R.family.path.rep (m+1) per (m+1)).eval=bare (R.family.beta (m+1) per) :=
    (R.makes.wilson.starts (m+1) per).2
  rw [source];exact issued

end YM.Integration.WilsonLocalPlaquetteReporting
