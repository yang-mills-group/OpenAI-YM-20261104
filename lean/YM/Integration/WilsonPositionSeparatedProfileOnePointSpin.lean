import YM.PhysMS.Frame.Measured

/-! The actual one-point read is constant in position and invariant under
each signed lattice rotation, in the unselected and every selected state. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionSeparatedProfileOnePointSpin
open Function Filter Set Table Spec OPE OPE.Orbits Climb Trace.Pilot PhysMS Lattice
open scoped Classical BigOperators Topology
variable {G : Gauge} {L : Register G} {S T : Table L}

private theorem single (x : Points 1) : x∈conf 1 := fun i j _=>Subsingleton.elim i j

private theorem relocate (x y : Points 1) : Points.across (y 0-x 0) x=y := by
  apply WithLp.ofLp_injective _
  funext i
  have hi : i=0 := Subsingleton.elim _ _
  subst i
  change x 0+(y 0-x 0)=y 0
  abel

theorem stationary (H : T.Hierarchy) (x y : Points 1) (v : Fin 1→L.Token) : T.read x v=T.read y v := by
  have eq:=H.translations 1 x (single x) (y 0-x 0) v
  rw [relocate] at eq
  exact eq.symm

theorem mirror (law : S.RealSpin) (H : T.Hierarchy) (valid : T.respects S)
    (d : ℕ) (s : Signed) (x : Points 1) (v : S.Field d) :
    S.classMoment T (fun _=>d) x (fun _=>S.mirror law d s v)=S.classMoment T (fun _=>d) x (fun _=>v) := by
  obtain ⟨y,rfl⟩:=S.onto d v
  let a : Fin 1→L.Token:=fun _=>⟨d,y⟩
  have bill:=H.spin.mirror s (single x) a
  calc S.classMoment T (fun _=>d) x (fun _=>S.mirror law d s (S.project d y))=
        T.read x (L.move s ∘ a) := S.class_agrees T H.laws.toSymmetric valid _ (single x) (fun _=>L.mirrorGroup d s y)
       _ = T.read (Points.move s.ortho x) (L.move s ∘ a) := stationary H _ _ _
       _ = T.read x a := bill
       _ = _ := (S.class_agrees T H.laws.toSymmetric valid _ (single x) (fun _=>y)).symm

theorem subtraction {W : Type*} [AddCommGroup W] [Module ℂ W] (M : MultilinearMap ℂ (fun _ : Fin 1=>W) ℂ) (u v : W) :
    M (fun _=>u-v)=M (fun _=>u)-M (fun _=>v) := by
  have fix (a : W) : Function.update (fun _ : Fin 1=>(0:W)) 0 a=(fun _=>a) := by
    funext i
    have hi : i=0:=Subsingleton.elim _ _
    subst i
    simp
  simpa only [fix] using M.map_update_sub (fun _=>0) 0 u v

variable {C : Family G} {o : Extraction.Order} {U : Table C.book} (F : Final C o U)

theorem all_states (d : ℕ) (s : Signed) (x : Points 1) (v : U.Field d) (p : Viewers F) :
    U.classMoment (spectator F p) (fun _=>d) x (fun _=>v-U.mirror F.room.kernel.spin d s v)=0 := by
  rw [subtraction,mirror F.room.kernel.spin (spectate F p) (spectate_respects F p),sub_self]

theorem measured (J : ℝ→PhysMS.tower U) (lead : PhysMS.Leading F J) (d : ℕ) (s : Signed)
    (v : (Bel C.book).Field d) :
    ∀ᶠ r in trail,∀(p : Viewers F)(x : Points 1),
      U.classMoment (spectator F p) (fun _=>d) (r • x)
        (fun _=>J r d (v-(Bel C.book).mirror (Maxwell.Free.spin_free C.labels) d s v))=0 := by
  filter_upwards [lead.equivariant d] with r fixed p x
  simp_rw [map_sub,fixed.1 s]
  exact all_states F d s (r • x) (J r d v) p

end YM.Integration.WilsonPositionSeparatedProfileOnePointSpin
