import YM.Contacts.Pulse.Synced
import YM.Contacts.Milling.Tower
/-! CP3, unmarked power mills tied to actual Passage. Accompanied by
 `celestial` instance nonperturbative contact extension. NOT a power
 prediction of the theories' contact values yet, nor is this implementing
 all of the MS convention. This supplies a conserving & winding-bounded
 all-order step calculator from the ACTUAL chosen construction -- forms,
 Charts and block tags. Many size costs remain post-L and not ready for
 propagation in the full Target 6. No cutoff power convergence except the
 stated basic `Epoch` comparison of leading kinetic symbol. Don't interpret
 `permit` nor specs extending these local analytic-germ integrals as an
 asymptotic expansion for the actual trajectory positive-order cores at
 varying widths. See claim map. -/
namespace YM.Contacts.Milling
noncomputable section
open Lattice RG Wilson Precision Org Pulse Pulse.Spine Lumen
open Contacts.Solstice PhysicalNext.Repeat.Legato
open Spec
variable {G:Gauge}
structure Garnet (u:Passage G) where
    x:G.ColorIndex
    E: ∀ N, RackCore u.A.B.a u.A.B.M N
    shine (n:ℕ): Theatre u.M.O x (E n) -- theorem args?
lemma garnet (h:G.Simple)(u:Passage G): Nonempty (Garnet u):= by
   obtain ⟨v⟩:= Stationary.colorAvail G h; obtain ⟨E,he⟩:= procession v u.M.oga u.A.B.plan; exact ⟨⟨v,E,he⟩⟩ -- 
lemma wheel_phase (u:Passage G) : u.Z.path.levels=u.A.B.a:= rfl
lemma linksUp (u:Passage G)(N p i:ℕ)(h:i≤N): Attached (u.A.B.M.H N i) ((u.Z.path.rep N p i).path) := by
    have he:= ((u.T.sticks N p).prices i (Nat.zero_le _) h).1.path; change Attached _ ((u.T.history N p i).path); rw [he,u.A.B.bases]; exact u.A.B.support.links N i h
-- KP Truce power comparison still here.
theorem bore_path (G:Gauge)(h:G.Simple){b:ℝ}(hx:0<b)(t:BidTri G)(F:Extraction.Order): ∃ (u:Passage G), admits t u ∧ u.Z.path.levels.clock.kernel.penalty=b ∧ Nonempty (Garnet u) ∧
   ∃ (g: Extraction.Order) (A:Table u.Z.book) (Z:Final u.Z (F.refine g) A) (M:Devices Z.sector.derivatives), MultipleLight Z M ∧ Nonempty (Transport.SystemBasis M) ∧ Nonempty (Thresholds M):= by
  obtain ⟨u,hu,hZ,H⟩:= through_truce G h hx t F; exact ⟨u,hu,hZ,garnet h u,H⟩
end
end YM.Contacts.Milling
