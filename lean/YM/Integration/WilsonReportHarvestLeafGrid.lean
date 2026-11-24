import YM.RG05Readout.Pulse.Nearby

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonReportHarvestLeafGrid
open Function Finset Filter Set Lattice Wilson RG RG05Readout
open RG05Readout.Native RG05Readout.Flatten RG05Readout.Pulse RG05Readout.Address
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge}{C:Family G}{I:Type}[Fintype I][DecidableEq I]{b j N per:ℕ}

theorem occupied {d:ℕ} (h:b ≤ N) (t:Site (C.S.toDepth h per).count) (a:Letter d) (f:Body)
    (ne:readJ a (placeR (C.S.toDepth h per) t) f≠0):
    placeR (C.S.toDepth h per) t∈Native.box ∩ tsupport f.val:=by
  constructor
  · simpa only [smul_zero,add_zero] using
      mapsR (C.S.toDepth h per) (C.S.toDepth_odd h per) t Native.box0
  · by_contra outside
    have hd:iteratedFDeriv ℝ (depth a) f.val (placeR (C.S.toDepth h per) t)=0:=
      notMem_support.mp (fun hh=>outside (support_iteratedFDeriv_subset _ hh))
    apply ne
    rw [Pulse.sample];simp [hd,Tensor.diagonal]

theorem placed (h:b ≤ N) {J:ℕ} (o:Site (C.side b per))
    (small:separation o 0 ≤ J) (t:Site (C.S.toDepth h per).count)
    (margin:C.S.a b*(2*(J:ℝ)+1)<C.S.radius per):
    C.S.place ((C.S.toDepth h per).assemble (o,t))=
      C.S.place o+C.S.a b • placeR (C.S.toDepth h per) t ∧
      ‖C.S.place ((C.S.toDepth h per).assemble (o,t))‖ ≤ C.S.a b*(2*(J:ℝ)+1):=by
  let A:=C.S.toDepth h per
  let v:Cover:=A.count.val • lift o+lift t
  have ht:placeR A t∈Native.box:=by
    simpa only [smul_zero,add_zero] using mapsR A (C.S.toDepth_odd h per) t Native.box0
  have geom:C.S.place o+C.S.a b • placeR A t=C.S.gridPoint N v:=grid_pair h (lift o) t
  have ho:= (MergeProof.Ribbons.normC C b per o).2
  have budget:‖C.S.place o+C.S.a b • placeR A t‖ ≤ C.S.a b*(2*(J:ℝ)+1):=calc
    _ ≤ ‖C.S.place o‖+‖C.S.a b • placeR A t‖:=norm_add_le _ _
    _ ≤ 2*C.S.a b*(separation o 0:ℕ)+C.S.a b:=add_le_add ho (room_B (C:=C) (b:=b) _ ht)
    _ ≤ C.S.a b*(2*(J:ℝ)+1):=by
      have hs:(separation o 0:ℝ) ≤ J:=by exact_mod_cast small
      nlinarith [mul_le_mul_of_nonneg_left hs (C.S.a_pos b).le]
  have wrapped:Lattice.wrap _ v=A.assemble (o,t):=by
    simpa only [Lattice.wrap_lift] using (grid_wrap (C:=C) (p:=per) h (lift o) t).symm
  have hl:lift (A.assemble (o,t))=v:=reads_grid (C:=C) wrapped (geom ▸ budget.trans_lt margin)
  have position:C.S.place (A.assemble (o,t))=C.S.place o+C.S.a b • placeR A t:=by
    change C.S.gridPoint N (lift (A.assemble (o,t)))=_
    rw [hl,←geom]
  exact ⟨position,position.symm ▸ budget⟩

end YM.Integration.WilsonReportHarvestLeafGrid
