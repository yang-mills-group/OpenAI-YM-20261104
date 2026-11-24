import YM.RG05Readout.Pulse.Chills

/-! At a mesh younger than the requested physical radius, the original territorial clearance and the contracted jets give an exact, uniformly priced finite bouquet. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabYoungBouquet
open Function Finset Filter Set MeasureTheory Lattice Wilson RG Source Extraction RG05Readout RG05Readout.Address RG05Readout.Native
open RG05Readout.Nuclear RG05Readout.Pulse RG05Readout.Flatten RG05Readout.Records
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{C:Family G}{b N per:ℕ}{V:Type}[DecidableEq V][Fintype V]

def fee (s:V→ℕ)(d:ℕ)(η:ℝ):ℝ:=mintBase s 2 d*(η/16)⁻¹^((∑i,(s i+2))+4*Fintype.card V)+(redeem s d 2*2+1)*(η/16)

omit [DecidableEq V] in
private theorem contracted (f:Wave V)(o:V→Site (C.side b per)){r X:ℝ}(rp:0<r)(room:C.S.a b≤r)
    {d:ℕ}(tested:Tall f d 1 X)(z:E4):Tall (cropX f o r z) d 1 X:=by
  intro j age y
  unfold cropX;rw [shoots,norm_smul,one_pow,one_mul,mul_comm r⁻¹,←div_eq_mul_inv,Real.norm_of_nonneg (pow_nonneg (div_nonneg (C.S.a_pos _).le rp.le) _)]
  have bound:=pow_le_one₀ (div_nonneg (C.S.a_pos b).le rp.le) ((div_le_one rp).2 room) (n:=j)
  exact (mul_le_of_le_one_left (norm_nonneg _) bound).trans (by simpa only [one_pow,one_mul] using tested j age _)

theorem original (s:V→ℕ)(h:b≤N)(o:V→Site (C.side b per)){r η X:ℝ}(rp:0<r)(room:C.S.a b≤r)
    (ep:0<η)(small:η≤1)(Ψ:Wave V)(d:ℕ)(grade:(∑i:V,(s i+2))+4*Fintype.card V<d+1)
    (scatter:Scattering Ψ η)(xp:0≤X)(sizeX:Tall Ψ (d+1) 1 X):
    ∃F:E4→Wave V,Bouquet s Native.box (Pulse.buy C b per o (r*η/2)) F (fee s d η*X) ∧
      ∀z:E4,∀j≤∑i,s i,∀w:V→Site (C.S.toDepth h per).count,
        pie (F z) (cropX Ψ o r z) j (placeR (C.S.toDepth h per) ∘ w):=by
  let a:=fun w:V→Site (C.S.toDepth h per).count=>placeR (C.S.toDepth h per) ∘ w
  let z:=η/16
  have live:0<z:=by dsimp [z];positivity
  have smallCell:z≤1:=by dsimp [z];linarith
  have clear:r*η/2+2*C.S.a b*(2*z)≤r*η:=by dsimp [z];nlinarith [mul_le_mul_of_nonneg_right room ep.le]
  let L:=Finset.univ.image a
  have short (i)(hi:i∈L):‖i‖<(2:ℝ):=by
    obtain ⟨w,_,rfl⟩:=Finset.mem_image.mp hi
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i=>Pert.Cellular.cells_bd ?_)) one_lt_two
    change placeR (C.S.toDepth h per) (w i)∈Native.box
    simpa only [smul_zero,add_zero] using mapsR (C.S.toDepth h per) (C.S.toDepth_odd _ _) (w i) Native.box0
  obtain ⟨F,roster,jet⟩:=vitality s Native.box (Pulse.buy C b per o (r*η/2)) (cropX Ψ o r) 2 z L
    (crop_cont o r Ψ) (territory o r η Ψ scatter rp _ _ clear) (fun i _=>contracted Ψ o rp room sizeX i)
    xp le_rfl live smallCell grade zero_le_two short
  refine ⟨F,roster.permit (fun _ _=>rfl) (le_of_eq ?_),fun τ i eligible w=>jet τ _ (Finset.mem_image_of_mem _ (Finset.mem_univ w)) i ?_⟩
  · unfold fee z;ring
  · have D:=le_trans eligible (Finset.sum_le_sum (g:=fun i:V=>s i+2) (s:=Finset.univ) (fun i _=>Nat.le_add_right ..));omega

end YM.Integration.WilsonSeparatedOriginalSlabYoungBouquet
