import YM.OPE.Compatible.Parch.Mirror
/-!
# Leading linear action. Genuine Ward calculus.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Claw
open Function Filter Set Lattice Laurent Wilson RG Matrix Precision Cascade
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
open PertExtension Series Libra ScriptJ GaussianScore Radial JetS Rill Arc Stranded Adhesion Score
open Flock Libra.Shell Next.Foundations Weir Exterior Bloch Next.Free Frequency Streamer Votive Flume Flume.Script Glass Quit.PriceZ Quit Paver
open Drift Char Silt Silt.Float Module Variance Merchant Stand
variable {G:Gauge}
attribute [local instance] Gauge.frobInner
variable {D V:Type}
local notation "E!"=>Libra.Keys G D
variable (R:Cascade.Score D V)[Fintype D]
open Pawn
lemma tenure (P:E!→ℝ)(j:ℕ)(hP:ContDiffAt ℝ ω P 0)(hp:Hush P j)(ht:insured R P): R.Marbles (mold P j):= by
       refine (Drift.pores R (tallJ j P)).2 fun {X Y s} h=>?_ ; let x(t:ℝ):= t⁻¹ • X t; let y(t:ℝ):= t⁻¹ • Y t; let U:= Signal j P hP hp x (Gael.walk X h.hX h.gx); let g:= Signal j P hP hp y (Gael.walk Y h.hY h.gy)
       refine U.equality (g.cong ?_); filter_upwards [Tested.eventually_pos, h.law.filter_mono nhdsWithin_le_nhds] with i (hi:0 < i) hx; unfold x y; rw [smul_inv_smul₀ hi.ne',smul_inv_smul₀ hi.ne', ht.march _ _ _ hx]
lemma Culm (P:E!→ℝ)(j:ℕ)(hP:ContDiffAt ℝ ω P 0)(hp:Hush P j)(ht:insured R P): LevelA R (rank P j):=by
      let h:= tenure R P j hP hp ht; exact LinearBell R h 0 (fun i hi x=>False.elim (Fin.not_lt_zero i hi)) -- jet defeq
lemma sleep_ (f:E!→ℝ)(u:E!):chrom f u u=2*rank f 2 u:=by
      rw [Merchant.podium]; unfold rank Tensor.coeff Tensor.diagonal; simp only [_root_.smul_apply,smul_eq_mul]; rw [show (![u,u] : Fin 2→E!)=(fun _=>u) from funext fun i=>by fin_cases i <;>rfl]; norm_num [Nat.factorial]; ring -- h unused
lemma surgeon (f:E!→ℝ)(hp:ContDiffAt ℝ ω f 0)(h:LevelA R (rank f 2))(g:G.El)(x y:E!):chrom f (glint D g x) (glint D g y)=chrom f x y:=by
      let K:=chrom f; have hx(u:E!): K (glint D g u) (glint D g u)=K u u:=(sleep_ f _).trans ((congr_arg (2*·) (h.inherits u g)).trans (sleep_ f _).symm); have he(a b:E!): K a b=K b a:=turnsT f (hp.of_le le_top) a b
      let H:=hx (x+y); let z:=glint D g; change K _ _= K x y; rw [show glint D g (x+y)=_ from (map_add z x y), K.map_add, K.map_add,LinearMap.add_apply,LinearMap.add_apply,map_add,map_add,map_add,map_add] at H; linarith only[H,hx x,hx y,he (z x) (z y),he x y]
lemma jitter (f:E!→ℝ)(hp:ContDiffAt ℝ ω f 0)(h:LevelA R (rank f 2))(g:V→G.Color)(x:E!): chrom f (gillS R g) x=0:=by
      let K:= chrom f; let v:=gillS R g; have he:K x v=K v x:=turnsT f (hp.of_le le_top) x v; have hx(i:E!): K (i+v) (i+v)=K i i:=(sleep_ f _).trans ((congr_arg (2*·) (h.tilts i g)).trans (sleep_ f _).symm); have hP: K v v=0:=by have ht:=hx 0; rw[zero_add,map_zero] at ht; exact ht
      change K v x=0; let hV:=hx x; rw [K.map_add,LinearMap.add_apply, map_add,map_add] at hV; linarith only[hV,hP,he] -- tests
end YM.OPE.Claw
