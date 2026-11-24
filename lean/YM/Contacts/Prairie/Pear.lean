import YM.Contacts.Prairie.Motion
import YM.Contacts.Prairie.Torch
namespace YM.Contacts.Prairie
open Function Set Finset Filter RG Wilson Lattice Precision Exterior Push.AbsoluteSums Extra.Iteration
open Bloch Milling Milling.Steam Pulse Spine MergeProof Milling.Forge Laurent Stationary Matrix Work.F08
open Milling.Garf Form House PertExtension.Series Tree Larch FreeResolvent PhysicalNext.RankCovariance
open Next.Free Milling.Lumen Barrage.Reserve
open scoped Topology BigOperators Matrix Classical NNReal ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G: Gauge}
namespace Parcel
open Origin Barrage.Slope Ion Resetter
variable (e:Parcel G) (p q u:Word) (s:Step) (n:Side) {i j:ℕ} {ζ:ℝ≥0}{b:ℝ}
abbrev White := Mixed G (e.flag s)
abbrev raw := axisLine G (e.flag s) (prom (e.Cov p s))
abbrev beam := axisSky G (e.flag s) (e.A p s)
abbrev planter : Cross s.L (Dye G) (e.White s) := adopt (Cellar G s.L) (Dye G)
variable {S:Boom}{e s}
namespace License
variable (T:e.License S ζ)(hs:s∈S)
include T hs
lemma raw_bill : Climb S (terrain (2*ζ) (e.White s)) (fun p=> plane (e.raw p s)):= by
   obtain ⟨v,hv,h⟩:=T.base _ hs; obtain ⟨b,hb,h'⟩:= T.pairs _ hs; let a:ℝ:= Fintype.card (e.White s); have ha:0≤a:=Nat.cast_nonneg _; refine ⟨⟨_,mul_nonneg ha hv,fun i hi=>?_⟩,_,mul_nonneg ha hb,fun p q u hp hq hu=>?_⟩
   · let he:= flight_stem (line_shape (S:=e.flag s) (brace _ (h i).direct hv) hv) hv; exact ⟨he.left,he.rows,he.columns⟩
   let U p:=e.raw p s; let Z p:=e.Cov p s; let W:=minusRows (U (u++p)) (U (u++q)); let V:=minusRows (Z (u++p)) (Z (u++q)); let H:=b*mileage u; have hw: W=axisLine G (e.flag s) (prom V) := by rw [show prom V= _ from Eq.symm (prom_diff (P:=e.flag s) ..)]; ext (x|x) (y|y) v<;> first|rfl|simp [U,W,raw,axisLine,minusRows]
   have hy:0≤ H:=mul_nonneg hb (mileage_pos _).le; let hk:= flight_stem (line_shape (S:=e.flag s) (brace V (h' _ _ u hu).direct hy) hy) hy; change Pulse.Track _ (plane W) _; rw [hw,mul_assoc]; exact ⟨hk.left,hk.rows,hk.columns⟩
lemma beam_bill : Threads S (tunnel (α:=e.White s) (β:=Dye G) (2*ζ)) (fun p=> plane (e.beam p s)):= by
   obtain ⟨v,hv,h⟩:=T.base _ hs; obtain ⟨b,hb,h'⟩:=T.pairs _ hs; let a:ℝ:= Fintype.card (Dye G); let f:ℝ:= Fintype.card (e.White s); have ha:0≤a:= Nat.cast_nonneg _; have hf:0≤f:= Nat.cast_nonneg _; let w:=1+v; have hw:= add_nonneg zero_le_one hv
   refine ⟨⟨_,mul_nonneg (add_nonneg hf ha) hw, fun p h'=> weir_up (flight_stem (sky_shape (U:=e.A p s) (h p).feed hv) hw) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ha) hw) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hf) hw) ⟩,_,mul_nonneg (add_nonneg hf ha) hb,fun p q u hi hj hk=>?_⟩
   let y:=b*mileage u; have hy:0 ≤ y:=mul_nonneg hb (mileage_pos _).le; let Y:=minusRows (e.beam (u++p) s) (e.beam (u++q) s); have he : Y.strip (2*ζ:ℝ≥0) y:= by
      rintro (x|x) j
      · simp [Width,Y,beam,axisSky,minusRows]; exact budget_loosen budget_zero hy
      exact (h' p q u hk).flow x j
   change Weirs _ (plane Y) _ _; rw [mul_assoc]; exact weir_up (flight_stem he hy) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ha) hy) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hf) hy)
lemma round_trips : Threads S (access s.L (α:=Dye G) (β:=Dye G) (2*ζ)) (fun p=>install (e.A p s)):= by
   obtain ⟨v,hv,h⟩:=T.base _ hs; obtain ⟨b,hb,h'⟩:=T.pairs _ hs; let a:ℝ:=Fintype.card (Dye G); let f:ℝ:= Fintype.card (Cellar G s.L); have ha:0≤a:=Nat.cast_nonneg _; have hf:0 ≤ f:= Nat.cast_nonneg _; let φ:= beamPrice (2*ζ); have hs (p:ℝ)(hp:0≤p): 0≤φ p:= mul_nonneg (Real.exp_pos _).le hp
   refine ⟨⟨(a+f)*φ v,mul_nonneg (add_nonneg ha hf) (hs v hv),fun p h'=> weir_up (ledgers (α:=Dye G) (h p).feed hv) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ha) (hs v hv)) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hf) (hs v hv))⟩, (a+f)*φ b,mul_nonneg (add_nonneg ha hf) (hs b hb),fun p q u hi hj hk=>?_⟩
   let Y:= mileage u; have hu:0≤ b*Y:= mul_nonneg hb (mileage_pos _).le; rw [show (a+f)*φ b*mileage u =(a+f)*φ (b*Y) by unfold φ Y beamPrice; ring]; exact weir_up (ledgers (α:=Dye G) (β:=Dye G) (L:=s.L) (h' p q u hk).flow hu) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ha) (hs _ hu)) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hf) (hs _ hu))
omit T hs in
lemma planted : Threads S (access s.L (α:=Dye G) (β:=e.White s) (2*ζ)) (fun _=>install (e.planter s)):= Threads.alone (ledgers (σ:=2*ζ) (L:=s.L) (α:=Dye G) (R:=e.planter s) (adopt_cost _ _ _) zero_le_one)
omit hs
variable {ι X:Type}[Fintype ι]
lemma emit_lt : ζ < 2*ζ:= by rw [two_mul]; exact lt_add_of_pos_right _ T.light
lemma pa {P:Word→Field ι (Node X)}(k:ℕ)(h:Fleet S (terrain (2*ζ) X) P):Fleet S (bath ζ k X) P:= Holds.trade h ((fit_spare (2*ζ) ζ k T.emit_lt).choose) (zero_le_one.trans (fit_spare _ _ _ T.emit_lt|>.choose_spec.1)) fun _ _ he=> expand_fee T.emit_lt he
end License
end Parcel
end
end YM.Contacts.Prairie
