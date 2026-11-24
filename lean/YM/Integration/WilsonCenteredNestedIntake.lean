import YM.Integration.WilsonCenteredNestedPhysical

/-! Buy the finitely many local signed comparisons before any of the
child radii or the positions are supplied. This needs no lower bound
on an internal child-to-parent ratio. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCenteredNestedIntake
open OPE OPE.Orbits OPE.Orbits.Reader OPE.Nesting OPE.Nesting.Tree OPE.Nesting.Composite OPE.Nesting.Atom
open Extraction Spec Table Filter Set WilsonCenteredNestedProgram WilsonCenteredNestedProducts
open scoped Classical BigOperators Topology
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (F : Final C f S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

def localRows (A : Rule F Q) (g L E : ℝ → ℝ) (M η : ℝ) :
    (t : Tree) → (t.Leaf → S.Tag) → (t.Inner → ℕ) → ℕ → Prop
  | bud,_,_,_ => True
  | fork n p,v,D,H =>
    (∀ (j : Branches F Q (f:=p) (rollCaps D)) (m : Fin (H+1)) (c : Q.channels m),
      ∀ᶠ r:ℝ in 𝓝[>]0,∀ (x : Fin n → E4) (o : E4),
        (∀ i,‖x i - o‖ ≤ M*r) → (∀ i k,i ≠ k → η*r ≤ ‖x i - x k‖) →
        let child := echoTags F Q v j
        Priced (express Q m c x child o) (A n m c r (g r) x child o)
          (L r * (r^m.val / ∏ i,r^((child i).1))) (E r)) ∧
    ∀ i,localRows A g L E M η (p i) (childWages i v) (childAge i D) (rollCaps D i)

private theorem smaller {P : ℝ → Prop} (h : ∀ᶠ r:ℝ in 𝓝[>]0,P r) :
    ∀ᶠ r:ℝ in 𝓝[>]0,∀ a,0 < a → a ≤ r → P a := by
  obtain ⟨δ,dp,inside⟩ := Metric.mem_nhdsWithin_iff.mp h
  filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0:ℝ) dp)] with r hr
  intro a ap ar
  have rp := ap.trans_le ar
  have cap : a < δ := ar.trans_lt (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos rp] using hr)
  exact inside ⟨by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ap] using cap,ap⟩

theorem original (A : Rule F Q) (g L E : ℝ → ℝ) (M η : ℝ) (t : Tree) (v : t.Leaf → S.Tag)
    (D : t.Inner → ℕ) (H : ℕ) (rows : localRows F Q A g L E M η t v D H) :
    ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s : t.Inner → ℝ) (z : t.Plot),
      t.Tapered r 1 s → t.Relative M η s z → calibrated F Q A g L E t s z v D H := by
  induction t generalizing H with
  | bud => exact Eventually.of_forall (fun _ _ _ _ _=>True.intro)
  | fork n p ih =>
    have here := eventually_all.mpr (fun j=>eventually_all.mpr (fun m=>eventually_all.mpr (rows.1 j m)))
    have below := eventually_all.mpr (fun i=>ih i _ _ _ (rows.2 i))
    filter_upwards [smaller here,smaller below] with r atRoot atChild
    intro s z level rel
    let a := s (.inl ())
    have gate := atRoot a level.1 level.2.1
    have children := atChild a level.1 level.2.1
    constructor
    · intro j m mh c
      apply gate j ⟨m,Nat.lt_succ_of_le mh⟩ c (skyline z) (anchor z)
      · intro i; exact rel.1 (.inr ⟨i,(p i).topSeat⟩)
      · intro i k ne; exact rel.2.1 i k (p i).topSeat (p k).topSeat ne
    intro i; exact children i (childAge i s) (childPlace i z)
      (by simpa only [mul_one] using level.2.2 i) (rel.2.2 i)

theorem filed {n : ℕ} {p : Fin n → Tree} (bank : Nesting.Uniform F Q) (A : Rule F Q)
    (g L : ℝ → ℝ) (Ln : ∀ r,0 ≤ L r) (order : ℕ) (v : (fork n p).Leaf → S.Tag)
    (D : (fork n p).Inner → ℕ) (m : ℕ) (c : Q.channels m) (M η ε : ℝ)
    (Mn : 0 ≤ M) (ηp : 0 < η) (ep : 0 < ε)
    (rows : localRows F Q A g L (fun a=>|g a|^order) M η (fork n p) v D m) :
    ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s : (fork n p).Inner → ℝ) (z : (fork n p).Plot),
      Accept r M η s z →
        ‖Kernel.output F Q z v c - run F Q A g (fork n p) s z v D m ⟨Fin.last m,c⟩‖ ≤
          bothToll (wages v) ε m D s +
          WilsonCenteredNestedPhysical.vertexFee F Q s v D m L (fun a=>|g a|^order) := by
  filter_upwards [WilsonCenteredNestedPhysical.original F Q bank A g L Ln order n p v D m c M η ε Mn ηp ep,
    original F Q A g L _ M η (fork n p) v D m rows] with r price intake
  exact fun s z h=>price s z h (intake s z h.levels h.relative)

end YM.Integration.WilsonCenteredNestedIntake
