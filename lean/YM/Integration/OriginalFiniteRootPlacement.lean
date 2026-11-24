import YM.Integration.OriginalMarkedRootDependence
import YM.Integration.FundedMarkedWindingWindow

/-! The finite heat of independently deposited held sources depends only
on their actual torus placements. The proof takes the periodization of the
cover data used by the original finite heat, including the full marked
exponential on every subset. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.OriginalFiniteRootPlacement
open Function Filter Finset Lattice RG Wilson Gauge Marker Precision Tree
open WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Mer
open WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Winding WilsonCoeffUV.Embroider WilsonCoeffUV.Embroider.Canvas
open WilsonCoeffUV.Soil WilsonCoeffUV.Cosmos WilsonCoeffUV.Power Bloch FreeResolvent Work.F08
open IndependentSourcePathFamily OriginalMarkedSourceComet
open scoped Topology BigOperators Classical

variable {V : Type} [DecidableEq V] [Fintype V] {G : Gauge} {D : V→ℕ} {n f : Side}
variable {I : V→Type} [∀ v,Fintype (I v)] (X : ∀ v,I v→Seed G (D v))

omit [Fintype V] in
private theorem singleShift (v : V) (p : Cover) (i l : ℕ) :
    (single X v p).2 i l = revolve p ((single X v 0).2 i l) := by
  funext z
  simp [single, source, cn, shifted, skewV, revolve, Prod.snd_sum, Finset.sum_apply, jog]

omit [Fintype V] in
theorem singletonFinite (v : V) {a b : Cover} (he : wrap n a=wrap n b) :
    (remade (single X v a)).1 n = (remade (single X v b)).1 n := by
  funext i l z
  change Carp.plume ((single X v a).2 i l) n z = Carp.plume ((single X v b).2 i l) n z
  rw [singleShift X v a,singleShift X v b,sigmaMint,sigmaMint,he]

theorem input {a b : V → Lattice.Cover} (he : ∀ i, wrap n (a i)=wrap n (b i)) (J : Finset V) :
    ((repaint (independent X a)) J).1 n = ((repaint (independent X b)) J).1 n := by
  by_cases one : ∃ v,J={v}
  · obtain ⟨v,rfl⟩ := one
    simpa only [repaint,IndependentSourcePathFamily.singleton] using singletonFinite X v (he v)
  · have empty (z : V → Lattice.Cover) : independent X z J=0 := by
      unfold independent
      apply sum_eq_zero
      intro v hv
      exact dif_neg (fun eq => one ⟨v,eq.symm⟩)
    change (remade (independent X a J)).1 n = (remade (independent X b J)).1 n
    rw [empty a,empty b]

omit [Fintype V] in
theorem exponential (E F : family G D) (he : ∀ J, (E J).1 n=(F J).1 n) (S : Finset V) :
    (levelsO E S).1 n=(levelsO F S).1 n := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hz : S=∅
    · subst S; rw [empty_level,empty_level]
    let look : Era G (Pen D S)→ₗ[ℝ] _ := LinearMap.proj n ∘ₗ LinearMap.fst ℝ _ _
    change look (levelsO E S)=look (levelsO F S)
    conv_lhs => rw [levelsO,dif_neg hz]
    conv_rhs => rw [levelsO,dif_neg hz]
    simp only [map_smul,map_sum]
    congr 1
    apply sum_congr rfl
    intro A hA
    split
    next h =>
      simp only [map_smul]
      congr 1
      change foam h.1 ((E A).1 n) ((levelsO E (S\A)).1 n) =
        foam h.1 ((F A).1 n) ((levelsO F (S\A)).1 n)
      rw [he A,ih (S\A) (sh_k h.1 h.2)]
    next _ => rfl

omit [Fintype V] in
theorem reference (A : Levels G) (O : ChartRatio G) (m N : ℕ) (n : Side)
    (E F : family G D) (he : ∀ J,((repaint E) J).1 (n*(loose A m).L)=
      ((repaint F) J).1 (n*(loose A m).L)) (k : V→ℕ) (C : Cost) :
    coilH A O m N n E k C=coilH A O m N n F k C := by
  let L := loose A m
  let S := AnalyticNext.QuarticMatch.Sheets.stepAt L A.clock.kernel n
  let Z := xree L A.clock.kernel n
  let H := freeForms A N (m+1)
  let M := roam A N m n
  let P := emera (actionW A O N (m+1)) (n*L.L)
  have raw : oven S Z H M O P (repaint E)=oven S Z H M O P (repaint F) := by
    funext J
    exact congrArg (srShade S Z H M O P) (exponential (repaint E) (repaint F) he J)
  unfold coilH WilsonCoeffUV.Wheel.Mark.mist inHeat
  dsimp only
  dsimp only [S,Z,H,M,P,L] at raw
  rw [raw]

omit [DecidableEq V] [Fintype V] in
theorem chart (P : Patch) (n : Side) (a b : V → Lattice.Cover) (stencil : V→Site P.L)
    (he : ∀ v,wrap n (a v)=wrap n (b v)) (v : V) :
    wrap (n*P.L) (chartIn P a stencil v)=wrap (n*P.L) (chartIn P b stencil v) := by
  let g := ratioN P.L n
  have q := congrArg g.embed (he v)
  rw [g.embed_wrap,g.embed_wrap] at q
  exact (map_add _ _ _).trans ((congrArg (fun u => u+wrap (n*P.L) (lift (stencil v))) q).trans
    (map_add _ _ _).symm)

/-- Independent reanchoring, on the same original finite source stencil,
for the full charged finite operator at all orders and all labelled marks. -/
theorem deposited (A : Levels G) (O : ChartRatio G) (m N : ℕ) (n : Side)
    (a b : V → Lattice.Cover) (stencil : V→Site (loose A m).L) (he : ∀ v,wrap n (a v)=wrap n (b v))
    (k : V→ℕ) (C : Cost) :
    coilH A O m N n (independent X (chartIn (loose A m) a stencil)) k C =
      coilH A O m N n (independent X (chartIn (loose A m) b stencil)) k C :=
  reference A O m N n _ _ (input X (chart (loose A m) n a b stencil he)) k C

theorem roots (A : Levels G) (O : ChartRatio G) (m N : ℕ) (n : Side)
    (placements : V→Site n) (v w : V) (stencil : V→Site (loose A m).L) (k : V→ℕ) (C : Cost) :
    let a := fun t => lift (placements v)+lift (placements t-placements v)
    let b := fun t => lift (placements w)+lift (placements t-placements w)
    coilH A O m N n (independent X (chartIn (loose A m) a stencil)) k C =
      coilH A O m N n (independent X (chartIn (loose A m) b stencil)) k C :=
  deposited X A O m N n _ _ stencil (fun _ => by simp) k C

end YM.Integration.OriginalFiniteRootPlacement
end
