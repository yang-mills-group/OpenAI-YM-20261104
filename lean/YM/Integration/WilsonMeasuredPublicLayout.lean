import YM.OPE.Cards.Scale

/-! Two original schedule levels furnish the common tiling for a finite packet of different widths. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicLayout
open Function Filter Set Lattice Cells Wilson Extraction Word Next.Phase
open scoped Classical Topology BigOperators
variable {I : Type} [Fintype I] {G : Gauge} (C : Family G) {N p : ℕ}
  {coarse packet micro wall : ℕ} {m : I → ℕ}
local notation "side" => C.side N p

structure Placed (m:I → ℕ) (u:I → Site (C.side N p)) where
  fine : Tiling (C.side N p)
  wide : Tiling (C.side N p)
  cell : wide.Cell
  first : fine.kind=.link
  second : wide.kind=.link
  base : fine.base=wide.base
  subdiv : fine.side.val ∣ wide.side.val
  live : ∀i,m i ≤ N
  divides : ∀i,Cells.span C.S (live i) p ∣ fine.side.val
  together : ∀i,wide.which (u i)=cell
  clearance : ∀i,Inside fine (3*Cells.span C.S (live i) p) (u i)
  separate : ∀i j,i≠j → fine.side.val < separation (u i) (u j)

/-- The center and stencil offsets are actual torus data. All inequalities in physical
lengths are charged before the common offset is chosen. -/
theorem original (hc:coarse ≤ packet) (hp:packet ≤ micro) (hm:micro ≤ wall) (hn:wall ≤ N)
    (later:∀i,wall ≤ m i) (live:∀i,m i ≤ N) (anchor:Site (C.side N p))
    (u:I → Site (C.side N p)) (displacement:I → Cover)
    (supports:∀i,u i=wrap (C.side N p) (displacement i)+anchor)
    (reach:∀i a,((displacement i) a).natAbs < 3*Cells.span C.S (hp.trans (hm.trans hn)) p)
    (room : 10*C.S.a packet < C.S.a coarse)
    (slack : 6*(Fintype.card I:ℝ)*C.S.a wall < C.S.a micro)
    (space : ∀i j,i≠j → C.S.a micro < C.S.a N*(separation (u i) (u j):ℝ)) :
    Nonempty (Placed C m u) := by
  have hpack:=hp.trans (hm.trans hn)
  have hmfr:=hm.trans hn
  have hcfr:=hc.trans hpack
  obtain ⟨x,wideInside,smallInside⟩ := OPE.Cards.seats C hpack hc hp hm hn
    (fun _ : Unit=>anchor) u (by simp only [Fintype.card_unit,Nat.cast_one,one_mul]; linarith) (by linarith)
  let W := (center C.S p hcfr (0:Site (C.side N p))).newly x
  let Y := (center C.S p hmfr (0:Site (C.side N p))).newly x
  have sub (i:I) : Cells.span C.S (live i) p ∣ Cells.span C.S hn p :=
    Around.inherits (later i) (live i)
  have hatRoom : Inside W (3*Cells.span C.S hpack p) anchor := wideInside ()
  refine ⟨⟨Y,W,W.which anchor,rfl,rfl,rfl,Around.inherits (hc.trans hp) hmfr,live,
    fun i=>Around.inherits (hm.trans (later i)) (live i),?_,?_,?_⟩⟩
  · intro i
    exact W.which_chamber ((supports i).symm ▸ (W.fits_stencil hatRoom (reach i)))
  · intro i
    have hi := (inside_stripe Y rfl _ _).mp (smallInside i)
    have hle := Nat.le_of_dvd (C.S.toDepth hn p).count.property (sub i)
    apply (inside_stripe Y rfl _ _).mpr
    intro a
    obtain ⟨u,v⟩:=hi a
    exact ⟨(Nat.mul_le_mul_left 3 hle).trans u,
      (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hle) _).trans_lt v⟩
  · intro i j ne
    apply (Nat.cast_lt (α:=ℝ)).mp
    apply lt_of_mul_lt_mul_left _ (C.S.a_pos N).le
    exact (C.S.embeds_scale (C.S.toDepth hmfr p)).le.trans_lt (space i j ne)

end YM.Integration.WilsonMeasuredPublicLayout
