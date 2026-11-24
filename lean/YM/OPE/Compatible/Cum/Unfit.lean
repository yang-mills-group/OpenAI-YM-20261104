import YM.OPE.Compatible.Cum.Lurid
/-! # External knot. no output
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra.Shell
open Function Filter MeasureTheory Module
open scoped Topology BigOperators ComplexConjugate Classical ContDiff RealInnerProductSpace ENNReal
open Next.Free Bloch PertExtension Series Asymptotics GaussianScore Radial Finset Flock Coin Lattice Laurent RG Precision Flume Script Page Planned.PrimaryIntegral295.Carrier Matrix
variable {I J: Type}{N:Side} {s:Finset J}[DecidableEq J]{v w:J→ℕ}{Q:∀ i:J,Script I (w i+v i)}{Ω:Row I I} {X:J→Bool}{i:J}{e d:ℕ}
lemma unfit (h:i∈s)(ha:X i=false)(P:Script I (e+d)): Shell.Hall Ω v w Q X s d e P=0:=by
     apply inductS (J:=J) (fun s d e=>∀ R:Script I (e+d), i∈s→Shell.Hall Ω v w Q X s d e R=0) _ _ _ _ _ P h
     · intro s e R h; rw [Hall_nil,if_neg (fun hx=>by simp [hx] at h)]
     intro s d e hA hB hP P hi; rw [script_run, hA _ hi]; have hW: WalkK Ω e d P (Shell.Hall Ω v w Q X s)=0:=by cases d with | zero=>rfl | succ d=> rw [soak_plus]; exact sum_eq_zero fun i _=>hB d (by omega) e _ hi
     rw [hW]; simp only [zero_add]; refine Finset.sum_eq_zero fun a hx=> ?_; split
     next hf=>
          have he:i∈ s.erase a:= mem_erase.mpr ⟨(fun e=>by rw [←e,ha] at hf; cases hf),hi⟩; suffices hp :∀ u (P':Script I (w a+u)),Once Ω (Shell.Hall Ω v w Q X (s.erase a)) e d P (w a) u P'=0 from hp _ _ ; intro u P'; cases u
          next=>rfl
          next u=>rw [once_plus];exact sum_eq_zero fun i _=>hP _ hx _ _ _ he
     next=>rfl
end YM.OPE.Libra.Shell
