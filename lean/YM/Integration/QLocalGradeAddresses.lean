import YM.Integration.QLocalVacuumOrderRestriction

/-! Literal ordinary and compulsory addresses of a restricted physical vacuum bank, including
one native aggregate validity receipt on its entire signed residual. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalGradeAddresses

open Lattice RG Wilson IterationFour IterationFour.Vacuum FullQLocal LocalComparison Global
open QLocalVacuumOrderRestriction
open scoped Classical

variable {G : Gauge} {n : Side}

def «prefix» : ℕ → ℕ ↪ ℕ
  | 0 => .refl ℕ
  | h+1 => («prefix» h).trans ⟨fun i => Payload.coding.symm (.inl i),
      fun _ _ e => Sum.inl.inj (Payload.coding.symm.injective e)⟩

def address (before : List (Piece G n)) : ℕ ↪ ℕ :=
  (⟨fun i => Payload.coding.symm (.inr i), fun _ _ e => Sum.inr.inj (Payload.coding.symm.injective e)⟩ : ℕ ↪ ℕ).trans
    («prefix» before.length)

theorem original (L : List (Piece G n)) (f : Piece G n → ℝ) (B : Activities G n) (i : ℕ) :
    (Render.adorn f B L).reg («prefix» L.length i)=B.reg i ∧
      (Render.adorn f B L).E («prefix» L.length i)=B.E i := by
  induction L with
  | nil => exact ⟨rfl,rfl⟩
  | cons a L ih => simpa [Render.adorn,Payload.attach,«prefix»,Function.comp_def] using ih

theorem piece (f : Piece G n → ℝ) (B : Activities G n) (before after : List (Piece G n))
    (a : Piece G n) (i : ℕ) :
    (Render.adorn f B (before++a::after)).reg (address before i)=a.packet.labels i ∧
    (Render.adorn f B (before++a::after)).E (address before i)=(f a) • a.packet.action i := by
  induction before with
  | nil => simp [Render.adorn,Payload.attach,address,«prefix»,Function.comp_def]
  | cons b before ih => simpa [Render.adorn,Payload.attach,address,«prefix»,Function.comp_def] using ih

/-- Affine support, site and full signed field are taken from the same physical index even
when intermediate retained and omitted orders interleave in the original list. -/
theorem omitted (p : ℕ) (f : Piece G n → ℝ) (B : Activities G n)
    (pre post : List (Piece G n)) (a : Piece G n) (ha : p<a.power) (i : ℕ) :
    let S := pre++a::post
    (Render.adorn f B (extra S p)).reg (address (extra pre p) i) = (Render.adorn f B S).reg (address pre i) ∧
    (Render.adorn f B (extra S p)).E (address (extra pre p) i) = (Render.adorn f B S).E (address pre i) := by
  have h : extra (pre++a::post) p = extra pre p ++ a::extra post p := by simp [extra,ha]
  dsimp only
  rw [h]
  exact ⟨(piece f B (extra pre p) (extra post p) a i).1.trans (piece f B pre post a i).1.symm,
    (piece f B (extra pre p) (extra post p) a i).2.trans (piece f B pre post a i).2.symm⟩

theorem retained (p : ℕ) (f : Piece G n → ℝ) (B : Activities G n)
    (pre post : List (Piece G n)) (a : Piece G n) (ha : a.power≤p) (i : ℕ) :
    let S := pre++a::post
    (Render.adorn f B (held S p)).reg (address (held pre p) i) = (Render.adorn f B S).reg (address pre i) ∧
    (Render.adorn f B (held S p)).E (address (held pre p) i) = (Render.adorn f B S).E (address pre i) := by
  have h : held (pre++a::post) p = held pre p ++ a::held post p := by simp [held,ha]
  dsimp only
  rw [h]
  exact ⟨(piece f B (held pre p) (held post p) a i).1.trans (piece f B pre post a i).1.symm,
    (piece f B (held pre p) (held post p) a i).2.trans (piece f B pre post a i).2.symm⟩

theorem valid_at (L : List (Piece G n)) {b : BudgetPoint} {f c : Piece G n→ℝ}
    (rows : ∀a∈L, a.packet.Invoice b (c a)) {B : Activities G n} {d z : ℝ} (hB : B.Valid b d z) :
    (Render.adorn f B L).Valid b (d+(L.map (fun a=>‖f a‖*c a)).sum) z := by
  induction L with
  | nil => simpa only [Render.adorn,List.map_nil,List.sum_nil,add_zero] using hB
  | cons a L ih =>
    have next := Payload.payment (f a) (rows a List.mem_cons_self)
      (ih (fun a ha=> rows a (List.mem_cons_of_mem _ ha)))
    rw [List.map_cons,List.sum_cons,add_comm (‖f a‖*c a),←add_assoc]
    exact next

theorem admitted {S : List (Piece G n)} {b : BudgetPoint} {rank : ℕ} {width budget d z : ℝ}
    (H : ZeroAwareVacuumPackets S b rank width budget) (h : Render.permits S b) (hw : 0<width)
    (p : ℕ) (g : ℝ) (B : Activities G n) (hB : B.Valid b d z) :
    (Render.adorn (Render.prefactor g) B (extra S p)).Valid b (d+debit H p g) z ∧
    (Render.adorn (Render.prefactor g) B (extra S p)).forced=B.forced ∧
    (Render.adorn (Render.prefactor g) B (extra S p)).K=B.K :=
  ⟨valid_at (extra S p) (fun a ha => ZeroAwareCappedRenderInvoice.invoice H h hw a (List.mem_filter.mp ha).1) hB,
    compulsory (extra S p) _ B⟩

end YM.Integration.QLocalGradeAddresses
end
