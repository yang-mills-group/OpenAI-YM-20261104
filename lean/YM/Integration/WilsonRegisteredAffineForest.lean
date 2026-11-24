import YM.AveragedStep.Stokes.Larger
import YM.Next.FLUCTUATIONS.Charts
import YM.Integration.WilsonReportingForestRelative
import YM.Integration.WilsonPhysicalHistoryKioskPlaquettes
import YM.Integration.WilsonRegisteredShortField

/-! The original forest segment fixes every saved bond. Relative group
motion controls every plaquette on a deposited regular support. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRegisteredAffineForest
open Lattice Wilson Tree RG OPE.Therm Precision PertExtension PhysicalNext.Repeat.Legato
open Push.AbsoluteSums.Animals WilsonPhysicalRegisteredForestAction WilsonReportingForestPivots
open WilsonInheritedRegisteredField
open scoped Classical
variable {G:Gauge} {c f:Side} {S:StepData c f}

private theorem path (U W:Config G f) {δ:ℝ} (bond:∀e,G.chord (W e*(U e)⁻¹) ≤ δ)
    (x:Site f) (w:Walk):G.chord (travel W x w*(travel U x w)⁻¹) ≤ (w.length:ℝ)*δ := by
  induction w generalizing x with
  | nil=>simp [travel]
  | cons d w ih=>
    have step:G.chord (d.read W x*(d.read U x)⁻¹) ≤ δ:=by
      by_cases neg:d.neg
      · simp only [Step.read,neg,if_true]
        rw [AveragedStep.Loops.chord_inv_pair (G:=G) (W (d.used x)) (U (d.used x))]
        exact bond (d.used x)
      simp only [Step.read,neg]
      exact bond _
    calc
      _ ≤ G.chord (d.read W x*(d.read U x)⁻¹)+
          G.chord (travel W (x+d.vec) w*(travel U (x+d.vec) w)⁻¹) :=
        AveragedStep.Loops.chord_prod (G:=G) (d.read W x) (travel W (x+d.vec) w) (d.read U x) (travel U (x+d.vec) w)
      _ ≤ δ+w.length*δ:=add_le_add step (ih _)
      _ = _ := by rw [List.length_cons,Nat.cast_add,Nat.cast_one];ring

theorem plaquette (U W:Config G f) {δ:ℝ} (bond:∀e,G.chord (W e*(U e)⁻¹) ≤ δ)
    (z:Face (Per f)) : G.chord (faceValue W z) ≤ G.chord (faceValue U z)+4*δ := by
  let a:=faceValue W z
  let b:=faceValue U z
  have curve : G.chord (a*b⁻¹) ≤ (4:ℝ)*δ:=path U W bond z.1 (square z.2.val.1 z.2.val.2)
  calc
    G.chord a = G.chord ((a*b⁻¹)*b):=by rw [inv_mul_cancel_right]
    _ ≤ G.chord (a*b⁻¹)+G.chord b:=G.chord_triangle _ _
    _ ≤ _:=by linarith only [curve]

/-- Every actual gauge link, including a crossing-parent link over a possibly
nontrivial pivot. The bound is independent of period and of the forest. -/
theorem bonds (G:Gauge) : ∃ C r:ℝ,0<C ∧ 0<r ∧
    ∀ {c f:Side} {S:StepData c f} (T:Forest S.ratio) (B:Finset T.Free)
      (v:({i:T.Free|i∉moving T B}:Set T.Free)→G.El) (X:↥(moving T B)→G.Color),
    ‖X‖ ≤ r→∀ {t:ℝ},t∈Set.Icc 0 1→∀e:Edge (Site f),
    let u (a:ℝ):=restored T B v (Chart.expLinks G (↥(moving T B)) (a • X))
    G.chord (u t e*(u 1 e)⁻¹) ≤ 2*C*‖X‖ := by
  obtain ⟨C,r,cp,rp,bill⟩:=Next.Fluctuations.chord_chart_cost G
  refine ⟨C,r,cp,rp,?_⟩
  intro c f S T B v X ball t dt e u
  let E:=moving T B
  let x (a:ℝ):=Chart.expLinks G (↥E) (a • X)
  let z (a:ℝ):=(cut T E).symm (x a*background T B v,v)
  have same (a:ℝ):u a=T.drape (z a):=rfl
  by_cases trunk:e∈T.trunks
  · rw [same,same,T.on_tree (z t) ⟨e,trunk⟩,T.on_tree (z 1) ⟨e,trunk⟩]
    simp;positivity
  let e':T.Free:=⟨e,trunk⟩
  have free (a:ℝ):u a e=z a e':=T.off_tree _ e'
  rw [free,free]
  by_cases moving:e'∈E
  · let s:↥E:=⟨e',moving⟩
    have value (a:ℝ):z a e'=x a s*background T B v s:=
      congr_fun (congr_arg Prod.fst ((cut T E).apply_symm_apply (x a*background T B v,v))) s
    rw [value,value,show (x t s*background T B v s)*(x 1 s*background T B v s)⁻¹=
      x t s*(x 1 s)⁻¹ by group]
    have ts:‖t‖ ≤ 1:=by rw [Real.norm_eq_abs,abs_of_nonneg dt.1];exact dt.2
    have tx:‖t • X s‖ ≤ ‖X‖:=by rw [norm_smul];exact (mul_le_of_le_one_left (norm_nonneg _) ts).trans (norm_le_pi_norm X s)
    have one:x 1 s=G.lieExp (X s):=by simp [x,Chart.expLinks]
    calc
      _ ≤ G.chord (x t s)+G.chord ((x 1 s)⁻¹):=G.chord_triangle _ _
      _ ≤ C*‖X‖+C*‖X‖:=by
        rw [G.chord_inv,one]
        exact add_le_add ((bill _ (tx.trans ball)).trans (mul_le_mul_of_nonneg_left tx cp.le))
          ((bill _ ((norm_le_pi_norm X s).trans ball)).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm X s) cp.le))
      _ = _:=by ring
  have same' (a:ℝ):z a e'=v ⟨e',moving⟩:=
    congr_fun (congr_arg Prod.snd ((cut T E).apply_symm_apply (x a*background T B v,v))) ⟨e',moving⟩
  rw [same',same',mul_inv_cancel,Gauge.chord_one]
  positivity

end YM.Integration.WilsonRegisteredAffineForest
end
