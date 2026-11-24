import YM.OPE.Compatible.Mould.Skate
/-! # Layer.Finitum φ arith. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Quit.Jac
open Function Filter Set Lattice Laurent Tree MeasureTheory RG Next.Free FreeResolvent WithLp Work.F08 Matrix Bloch Precision Wilson Exterior Stationary Woody Next.Foundations Flume Flume.Virgin Libra Weir Votive Cascade Score Flume.Script
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open MSbar.Tree MSbar.Tree.Resolvent PertExtension Series ScriptJ GaussianScore Work.F05 Cascade Cascade.Paver Cascade.Rill Glass Coin Pilot Radial Flock Frequency Streamer Further.FreeCovariance.KP Arc Stranded Adhesion Drift Prairies
open Shell Char Planned.PrimaryIntegral295.Carrier Terp Silt Silt.Float Module Finset Silt.Float Votive Alps Roles
open Quit.PriceZ Hark JetS
variable {n c f:Side}{E F Q:Type}
variable [NormedAddCommGroup E][NormedSpace ℝ E]
variable [NormedAddCommGroup F][NormedSpace ℝ F]
variable {u q:ℝ}
variable {g:E≃ₗ[ℝ] (Fin 3→ F)}{S T:E→L[ℝ] E}
lemma Thruster.net (h:Thruster g S T q)(i:Phase)(x:E)(hp:∀ j:Phase,j.val < i.val → g x j=0):∃ y:E, x=(S^i.val) y ∧ g x i= g y 0:=by
     fin_cases i
     · exact ⟨_,rfl,rfl⟩
     · obtain ⟨y,rfl⟩:= h.next x (hp 0 (by decide)); exact ⟨y,(show _ from (show S y=(S^1) y by rw[pow_one])),h.up 0 1 rfl _⟩
     obtain ⟨y,rfl⟩:= h.far x (hp 0 (by decide)) (hp 1 (by decide)); exact ⟨y,(show S (S y)= (S^2) y by rw[pow_two]; rfl),(h.up 1 2 rfl (S y)|>.trans (h.up 0 1 rfl y))⟩
lemma soFar (S:E→L[ℝ] E)(A:E→Token) (h:∀ i,A (S i)= Ū * A i) (x:E)(v:Phase) : (A ((S^v.val) x)).seq v.val=(A x).seq 0:=by
     fin_cases v; · rfl
     · change (A ((S^1) x)).seq 1= _; rw [pow_one,h,boneL]
     change (A ((S^2) x)).seq 2=_; rw [pow_two,byway,h,boneH,h,boneL]
lemma ζRows (Q:E→L[ℝ] E)(x:E)(n:ℕ):(Q^n) x = (fun u:E=>Q u)^[n] x:=by induction n generalizing x with
     | zero=>rfl
     | succ i ih=> rw [pow_succ,byway, ih];rfl
lemma Thruster.isNet (h:Thruster g S T q)(i:Phase)(x:E)(hp:∀ j:Phase,j.val < i.val → g x j=0):∃ y:E, x=(fun u=> S u)^[i.val] y ∧ g x i= g y 0:= by obtain ⟨y,hy,hx⟩:=h.net i x hp; exact ⟨y,hy.trans (ζRows ..),hx⟩
omit [NormedAddCommGroup E][NormedSpace ℝ E] in
lemma soFarV (S:E→E)(A:E→Token) (h:∀ i,A (S i)= Ū * A i)(x:E)(v:Phase): (A ((S^[v.val]) x)).seq v.val=(A x).seq 0:=by
     fin_cases v; · rfl
     · change (A (S x)).seq 1=_; rw [h,boneL]
     change (A (S (S x))).seq 2=_; rw [h,boneH,h,boneL]
end YM.OPE.Quit.Jac
