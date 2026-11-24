import YM.Integration.WilsonSeparatedOriginalSlabChildSites
import YM.Integration.WilsonSeparatedOriginalSlabReturn

/-! Common true translations of any of the seven original marked products may be recentered at the held coarse unit. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonSeparatedOriginalSlabChildLaw
open Function Finset Lattice RG Wilson Source Push.GridApprox OPE OPE.Therm MeasureTheory
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Records
open MergeProof.Accent PhysicalNext.Repeat.Legato WilsonMacroscopicForwardTransfer WilsonSeparatedOriginalSlabChildSites
open scoped Classical BigOperators Topology
variable {G:Gauge}{a n N per:ℕ}

private theorem inject (S:Schedule){j p:ℕ}:Function.Injective (S.place (m:=j) (p:=p)):=by
  intro x y eq
  have lifted:lift x=lift y:=by
    funext k
    have h:=congrArg (fun z:E4=>(WithLp.ofLp z) k) eq
    change S.a j*(lift x k:ℝ)=S.a j*(lift y k:ℝ) at h
    exact_mod_cast mul_left_cancel₀ (S.a_pos j).ne' h
  rw [←wrap_lift x,←wrap_lift y,lifted]

theorem embedded (S:Schedule)(A:Ratio (S.side a per) (S.side n per))(B:Ratio (S.side n per) (S.side N per))
    (D:Ratio (S.side a per) (S.side N per))(c:Site (S.side a per)):B.embed (A.embed c)=D.embed c:=by
  apply inject S;rw [S.embeds_place B,S.embeds_place A,S.embeds_place D]

variable (R:Run G)
theorem invariant (aN:a ≤ N)(c:Site (R.family.side a per))(X:Config G (R.family.side N per) → ℂ)(smooth:Continuous X):
    actualTransport R.family (N:=N) (X ∘ pull 1 ((R.family.S.toDepth aN per).embed c)) aN 1=
      actualTransport R.family (N:=N) X aN 1:=by
  have turned:=congrFun (WilsonPositionSeparatedProfileCenteredBranch.covariance R N per aN c X smooth) (1:Config G (R.family.side a per))
  have id:pull 1 c (1:Config G (R.family.side a per))=1:=by rw [pull_one];rfl
  rw [comp_apply,id] at turned
  simp only [actualTransport]
  apply congrArg (fun v:ℂ=>((R.family.path.rep N per a).eval 1)⁻¹ • v)
  simpa only [Records.dyes,Function.comp_apply,Complex.real_smul] using turned

def marks (s:Fin 3 → ℕ)(v:(i:Fin 3) → Palette R.family (s i))(o:Fin 3 → Site (R.family.side n per))
    (f:Fin 3 → Body)(J:Finset (Fin 3))(W:Config G (R.family.side N per)):ℂ:=
  ∏i∈J,Records.clinic R.family per N (s i) (v i) n (o i) (1,false) (f i) W

private theorem translated (nN:n ≤ N)(s:Fin 3 → ℕ)(v:(i:Fin 3) → Palette R.family (s i))(o:Fin 3 → Site (R.family.side n per))
    (c:Site (R.family.side n per))(f:Fin 3 → Body)(J:Finset (Fin 3)):
    marks R (N:=N) s v o f J ∘ pull 1 ((R.family.S.toDepth nN per).embed c)=marks R s v (fun i=>o i+c) f J:=by
  funext W;apply prod_congr rfl;intro i _
  exact WilsonSeparatedOriginalSlabTranslation.clinic R.family nN (s i) (v i) (o i) c (f i) W

theorem original (an:a ≤ n)(nN:n ≤ N)(A:Ratio (R.family.side a per) (R.family.side n per))(s:Fin 3 → ℕ)
    (v:(i:Fin 3) → Palette R.family (s i))(o:Fin 3 → Site (R.family.side n per))(c:Site (R.family.side n per))
    (f:Fin 3 → Body)(J:Finset (Fin 3)):
    actualTransport R.family (N:=N) (marks R (N:=N) s v o f J ∘ pull 1 ((R.family.S.toDepth nN per).embed c)) (an.trans nN) 1=
      actualTransport R.family (N:=N) (marks R s v (site A o c) f J) (an.trans nN) 1:=by
  let q:=A.parent (o 0+c)
  let D:=R.family.S.toDepth (an.trans nN) per
  have positions:(fun i=>site A o c i+A.embed q)=fun i=>o i+c:=by
    funext i
    change (o i+c)+A.root (-q)+A.root q=o i+c
    rw [map_neg];abel
  have inside:=translated R nN s v (site A o c) (A.embed q) f J
  rw [embedded R.family.S A (R.family.S.toDepth nN per) D,positions] at inside
  rw [translated R nN s v o c f J,←inside]
  exact invariant R (an.trans nN) q _ (continuous_finsetProd _ fun i _=>Records.clinic_cut ..)

end YM.Integration.WilsonSeparatedOriginalSlabChildLaw
