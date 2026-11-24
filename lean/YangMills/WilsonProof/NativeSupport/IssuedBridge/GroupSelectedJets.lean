import YangMills.WilsonProof.NativeSupport.IssuedBridge.GroupMaxwellScaling
set_option autoImplicit false
noncomputable section
namespace YangMills.IssuedPhysical
open YM YM.Spec YM.OPE.Orbits YM.Maxwell YM.Maxwell.Free
open Function Filter Set
open scoped Topology BigOperators InnerProductSpace Classical

variable {g : GaugeGroup} {C : Family g.core} {p : Extraction.Order} {S : Table C.book}
variable (F : Final C p S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

theorem selectedScaling (X : Climb.Scaling S) (h : Pert.FirstExtension F X)
    (all : ∀n j:ℕ,∀q:Fin n→(freeTable C.labels).Tag,∀marks:Fin n→Bool,∀ab:Fin n→Axis×Axis,
      ∀K:Set (Points n),IsCompact K→K⊆conf n→∀t:ℝ,0<t→∀ᶠk:ℕ in atTop,∀x∈K,∀viewer:OPE.Viewers F,
      ‖iteratedFDeriv ℝ j (fun y=>S.useAt (OPE.spectator F viewer) (X.r k • y)
          (Pert.scaledPhysical X F.sector.energy k q marks ab)) x-
        iteratedFDeriv ℝ j (Ward.disc (Pert.freeWithStress C.labels q marks ab)) x‖≤t) :
    Reconstruction.SelectedMaxwellJets (IssuedMaxwell.Reference.issued g) (hierarchy F Q) (issuedScaling F Q X h) := by
  intro n j q marked ab K hK hsep ε hε
  let v (i : Fin n) : (freeTable C.labels).Tag := ⟨(q i).1,(fields C.labels _).symm (q i).2⟩
  have hh := all n j v marked ab K hK hsep ε hε
  have free (z : Points n) : Ward.disc (Pert.freeWithStress C.labels v marked ab) z =
      Wick.moment g.core z (fun i => if marked i then -polStress g.core (ab i).1 (ab i).2
        else (q i).2.val) := by
    rw [Ward.disc, display]
    congr 1
    funext i
    change supply C.labels (Pert.freeWithStress C.labels v marked ab i) = _
    unfold Pert.freeWithStress
    split_ifs with hi
    · change address C.labels 4 (-original C.labels (ab i).1 (ab i).2) = _
      rw [map_neg,inertia]
    · exact congrArg Subtype.val ((fields C.labels (q i).1).apply_symm_apply (q i).2)
  rw [funext free] at hh
  filter_upwards [hh] with k hk
  exact fun x hx => hk x hx (some F.α.atPoint)
end YangMills.IssuedPhysical
end
