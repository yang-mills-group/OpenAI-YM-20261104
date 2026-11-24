import YM.Integration.WilsonReportingLength
import YM.Integration.WilsonMacroscopicRichWatchReader
import YM.Integration.WilsonMacroscopicRichFixedDecoder

/-! All real radii on a submitted reporting tuple enter the open detector room at once. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichWatchRooms
open Real Filter Set Wilson OPE Lattice RG16 RG16.Literal PhysMS
open WilsonMacroscopicRichFixedWatchSale
open scoped Topology BigOperators Classical
variable {G:Gauge}(C:Family G){I:Type}[Fintype I]

omit [Fintype I] in
theorem placed (B:ℝ){P:ℝ→Prop}(small:∀ᶠr in Trace.Pilot.trail,P r):
    ∀ᶠm:ℕ in atTop,∀(M η ρ:ℝ)(x:I → Cover), Tuple C M η B m ρ x →
      P (C.S.a m*ρ) ∧ WithinRoom (C.S.a m*ρ) M η (fun i=>C.S.gridPoint m (x i)) 0:=by
  obtain ⟨δ,pos,inside⟩:=mem_nhdsGT_iff_exists_Ioo_subset.mp small
  have late:∀ᶠm:ℕ in atTop,WilsonReportingLength.radius C (B+1) m<δ:=
    (WilsonReportingLength.fine C (B+1)).eventually (Ioo_mem_nhdsGT pos) |>.mono fun _ e=>e.2
  filter_upwards [late] with m threshold M η ρ x cells
  have Λ:0<Lambda C.path.levels m:=by
    unfold Lambda
    linarith [Real.log_nonneg (C.path.levels.fits.delayed m).le]
  have lo:=mul_pos (C.S.a_pos m) ((Real.rpow_pos_of_pos Λ _).trans_le cells.lo)
  have hi: C.S.a m*ρ<δ:=(mul_le_mul_of_nonneg_left cells.hi (C.S.a_pos m).le).trans_lt threshold
  exact ⟨inside ⟨lo,hi⟩,fun i=>by simpa only [sub_zero] using cells.contour i,cells.missing⟩

theorem estimate {a:ℕ}(K:Fin a→ℝ)(pos:∀i,0≤K i){fee:ℝ}(nn:0≤fee)
    (y:Fin a→ℂ)(signed:∀z:Fin a→ℂ,‖∑i,z i*y i‖≤fee*∑i,‖z i‖*K i):
    ‖y‖≤fee*∑i,K i:=by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg nn (Finset.sum_nonneg fun i _=>pos i))).2 fun i=>?_
  have one:=signed (fun j=>if i=j then 1 else 0)
  have single:‖y i‖≤fee*K i:=by simpa [apply_ite,ite_mul] using one
  exact single.trans (mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _=>pos j) (Finset.mem_univ i)) nn)

end YM.Integration.WilsonMacroscopicRichWatchRooms
