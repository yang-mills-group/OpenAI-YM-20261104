import YM.FormalOPE.RG10.Spiral.Costate
/-!
# Rotation of the Wilson symbol, which heats the stencil before deployment
No new spectral bounds needed for this exact-diagonal normalization theorem: use the accepted
unrestricted torus/cover limit of the plaquette multiplier, slot by slot. -/
set_option autoImplicit false
noncomputable section
namespace YM.FormalOPE.RG10.Spiral
open Function Wilson Lattice Gauge Precision Exterior Work.F03 Further.CorrectedLift.Compass
   PertExtension Filter RG PertExtension.LatticePT LatticePT.Projection Finset
open Further.CurvedGaussianJets.Shape AnalyticBridge.CouplingShape Next.Rank Hue Normal
open scoped Topology ContDiff BigOperators Classical RealInnerProductSpace
variable {G:Gauge} {n : Side}
local notation "Λ" => Hue.Panel RG.Slot G
local notation "ν" => LatticePT.colorBasis (G:=G)
local notation "F" => covarianceSymbol G
local notation "γ" => Bid.Dir G n

def clockwise (s:Signed)(p:Λ): Λ →₀ ℂ:= Finsupp.single (bend G s p.1,p.2) (↑(wind s p.1.plaq):ℂ)
variable (n) in
def rig : Symmetric Λ := ⟨fun i j=> ↑(earning (Converter.position n i.1) (Converter.position n j.1) (ν i.2) (ν j.2)),fun i j=>by rw [earning_comm]⟩
lemma landing (q:ℕ+)(hq:1<q.val)(i j:Λ) : Tendsto (fun k=> (rig (G:=G) (side q k)).cov i j) atTop (𝓝 ((F).cov i j)) := by
 change Tendsto (fun k=> (↑(earning _ _ _ _):ℂ)) _ (𝓝 (ite _ _ _)); split_ifs with h
 · simp_rw [earning_color,if_pos h]; exact Complex.continuous_ofReal.continuousAt.tendsto.comp (Converter.incline_limit (q:=q) i.1 j.1 hq)
 simp_rw [earning_color,if_neg h,Complex.ofReal_zero]; exact tendsto_const_nhds
private lemma coordinate (s:Signed)(C:Symmetric Λ)(i j:Λ):
    (scope (clockwise s) C).cov i j = (wind s i.1.plaq:ℝ) • (wind s j.1.plaq:ℝ) • C.cov (bend G s i.1,i.2) (bend G s j.1,j.2) := by
   unfold scope treats clockwise; simp only [Finsupp.linearCombination_single, Pi.smul_apply,Complex.real_smul]; ring -- maybe smul_eq_mul
lemma rig_spins (n:Side)(s:Signed): scope (clockwise s) (rig (G:=G) n) = rig n := by
 ext1; funext i j; rw [coordinate]
 change _ • _ • (↑(earning _ _ _ _):ℂ)= ↑(earning _ _ _ _); rw [sent,sent, Complex.real_smul,Complex.real_smul,← Complex.ofReal_mul,← Complex.ofReal_mul,← mul_assoc]
 exact congr_arg _ ((earning_spin s (Converter.position n i.1) (Converter.position n j.1) (ν i.2) (ν j.2)).symm)
lemma earn (s:Signed) : scope (clockwise s) F = F := by
 ext1;funext i j
 let q : ℕ+ := 3
 apply tendsto_nhds_unique (f:= fun k=> (rig (G:=G) (side q k)).cov i j) (l:=atTop) ?_ (landing q (by decide) ..)
 let w k:= rig (G:=G) (side q k)
 have he k : (w k).cov i j=(scope (clockwise s) (w k)).cov i j:=congr_fun₂ (congr_arg Symmetric.cov (rig_spins (G:=G) _ s).symm) ..
 change Tendsto (fun k=>(w k).cov i j) _ _; simp_rw [he,coordinate]
 exact ((landing q (by decide) ..).const_smul (wind s j.1.plaq)).const_smul (wind s i.1.plaq)
lemma braid (s : Signed)(P:poly Λ): milk F (exchange (clockwise s) P)=exchange (clockwise s) (milk F P):= by rw [prepared,earn]
end YM.FormalOPE.RG10.Spiral
