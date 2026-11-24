import YM.Integration.WilsonIndependentConditionalFiniteGrant
import YM.Integration.WilsonIndependentPostedGrant

/-! The nonconstant angular rows of the genuinely normalized unmarked block, with a finite-order offer. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentConditionalRawVacuum
open Filter Matrix RG Lattice WilsonCoeffUV Blue Bank Soil RegulatorIR Budget Diagram
open Bloch Laurent Metric Precision FreeResolvent Work.F08 Wilson Tree
open AnalyticNext.QuarticMatch.Sheets Exterior WilsonCoeffUV.Mer Embroider
open WilsonIndependentConditionalUnshiftedQuiet WilsonIndependentConditionalUnshiftedExit
open WilsonIndependentConditionalFiniteGrant (tip)
open scoped Topology BigOperators Classical

def finite {I:Type}[Fintype I](K:Matrix I I ℝ)(V:Pal ℝ I)(e:ℕ):Gen ℝ I:=
  ∑ j∈Finset.range (3*e+1),abr K V j e

variable {α:Type}[Fintype α]{G:(n:Side)→ ropes (Site n) α α}{Γ:ropes Cover α α}
    {V:(n:Side)→Pal ℝ (Co n α)}{P:Pal ℝ (Cloth α)}{d:ℕ}

theorem covered (fund:Pilots G Γ)(sym:Γ.transpose=Γ)
    (quiet:∀ i≤d,∀ r,0<r→Yields (fun n=>V n i r) (P i r))(vp:∀ n i,i≤d→Pure (V n i))
    (e r:ℕ)(he:e≤d)(hr:0<r):
    Yields (fun n=>finite (G n) (V n) e r) (ceaseHeat Γ P false e r):=by
  have q (i s):Yields (fun n=>tip (V n) d i s) (tip P d i s):=by
    by_cases h:i≤d∧0<s
    · simpa only [tip,if_pos h] using quiet i h.1 s h.2
    simp only [tip,if_neg h];exact Yields.zero
  have v (n i):Pure (tip (V n) d i):=by
    intro s
    by_cases h:i≤d∧0<s
    · simpa only [tip,if_pos h] using vp n i h.1 s
    simp only [tip,if_neg h];exact Smooth.zero
  have smooth:gradedSymmetric (tip P d):=fun i s=>(q i s).sym (Eventually.of_forall fun n=>v n i s)
  have hfin (n j):abr (G n) (tip (V n) d) j e r=abr (G n) (V n) j e r:=
    WilsonIndependentConditionalCappedBlue.quiet (G n) (fun i hi s hs=>if_pos ⟨hi,hs⟩) j e he r hr
  have hcov (j):logHeat Γ (tip P d) false j e=logHeat Γ P false j e:=
    WilsonIndependentConditionalThermalCap.quiet Γ (fun i hi s hs=>if_pos ⟨hi,hs⟩) j e he
  have row (j):Yields (fun n=>abr (G n) (V n) j e r) (logHeat Γ P false j e r):=by
    have paid:=tide_pages fund q j e r
    rw [WilsonIndependentConditionalCoverVacuum.original fund sym q smooth j e r hr,hcov j] at paid
    exact paid.congr (Eventually.of_forall fun n=>hfin n j)
  have result:=parcelY (s:=Finset.range (3*e+1)) (P:=fun n j=>abr (G n) (V n) j e)
    (F:=fun j=>logHeat Γ P false j e) (fun j _=>row j)
  simpa only [finite,ceaseHeat,heated,Finset.sum_apply] using result

theorem original {W:Gauge}(A:Levels W){m N:ℕ}(finer:m<N)
    {Y:(n:Side)→Pal ℝ (Co n (Hinge W (loose A m).L))}{T:Pal ℝ (Cloth (Hinge W (loose A m).L))}
    (quiet:∀ i≤d,∀ r,0<r→Yields (fun n=>Y n i r) (T i r))(pure:∀n i,i≤d→Pure (Y n i))
    (e r:ℕ)(he:e≤d)(hr:0<r):
    let B:=loose A m;let K:=A.clock.kernel;let H:=freeForms A N (m+1);let Γ:=kernel B (shuttleM (conditional A N m))
    let M:=post B (shuttleM (feedA A N m))
    Yields (fun n=>scoop (fade (ends B K (roam A N m) n) (finite (matrix B K H n) (Y n) e) r))
      (scoop (prism M (ceaseHeat Γ T false e) r)):=by
  intro B K H Γ M
  let g:=resin A N m finer
  have inc:=WilsonIndependentConditionalUnshiftedQuiet.covariance B K g
  have sym:=WilsonIndependentConditionalUnshiftedQuiet.symmetric B K g (fun n=>Bank.age_sym A N (m+1) (n*B.L))
  have money:=covered inc sym quiet pure e r he hr
  exact scoopY (prism_fold (predictor B K g) money)

end YM.Integration.WilsonIndependentConditionalRawVacuum
