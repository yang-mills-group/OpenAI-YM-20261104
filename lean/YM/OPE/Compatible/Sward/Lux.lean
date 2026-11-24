import YM.OPE.Compatible.Sward.Ale
import YM.OPE.Compatible.Frog.Eye
/-!
# Wick drag on infinite support gauge frames, fixed period as chosen.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Silt.Phere
open Next.Free Bloch MeasureTheory Function Filter Finset Lattice Laurent Flume Flume.Script Flume.Page Precision Module Libra Shell Char RG Work.F08 Float
open scoped Topology BigOperators Classical
variable {I G K E F X:Type}{m r i j n k:ℕ}{C D:ℝ} {H:Gauge}
open Cloud JetS
open scoped ContDiff
variable {v y:fieldX (Shade H)}
open Tensor WardBin
-- budget C estimate.O. Use masks of bad axes
open Cascade Terp Paver Rill Shell FreeResolvent Exterior MSbar.Tree MSbar.Tree.Resolvent Frequency Streamer
open Votive
variable {N:Side}{L:KernelChoices} (x:Site N)
open Drift Shell Char
variable {τ :Char.Phase→ℕ}{d:ℕ}
open PertExtension Series GaussianScore
section poll
open Matrix
lemma atlasVolt (A:Mat (Tab (Shade H) N))(M:Mat (FreeResolvent.Slot H N 1))(ht:A=M.submatrix (station H N) (station H N)): A= OrderR H N*M*(OrderR H N)ᵀ:=by
     subst A; ext i j; simp only [Matrix.mul_apply,OrderR,Matrix.transpose_apply, Matrix.submatrix_apply,id_eq,Matrix.one_apply,ite_mul,mul_ite,one_mul,zero_mul,sum_ite_eq,mem_univ,if_true,mul_one,mul_zero]
lemma flareU (v:Train r)(h: r≥4) (p:Seat k m (Shade H))(b:ℝ):
     let A:=rentV H v h L N; let M:= CapeV L H v N
     formSong m k H x (boostS A b m k p)= fixExp (opus M) b k (formSong m k H x p) :=by
          intro A M; let F:= (lapD A m k).toLinearMap; let S:= formSong m k H x; let K:= M.submatrix (station H N) (station H N); have hh(P:Seat k m (Shade H)): S (F P)= opus M (S P):=by
               funext i; change ((worldR m k x _ (lapD A m k P) i).compContinuousLinearMap _)=wind i • Semester M ((worldR m k x _ P (i+2)).compContinuousLinearMap fun _=>_); rw [hornT K _ _ (dripped H v h L x) P i,columnAlong _ _ _ (atlasVolt K M rfl)];rfl
          have ht(i:ℕ): S ((F^i) p)=(opus M ^i) (S p):=by induction i with| zero=>simp|succ i ih=> rw [pow_succ',pow_succ',End.mul_apply,End.mul_apply,hh,ih]
          rw[boostS,Hflow,Hflow,map_sum]; exact Finset.sum_congr rfl fun i _=>by rw [map_smul, ht i]
lemma breathQ (C:KernelChoices)(v:Train r)(H:Gauge)(n:Side)(h:4 ≤ r) : Sustains (Vessel C v H n h) (spool H n).toContinuousLinearMap ((terra_money C h).choose+1):=by
       let T:=rentV H v h C n; let F:= spool H n; let P:= Vessel C v H n h; refine ⟨T.positive,fun i=>?_⟩; have he(a):Ferry F.toContinuousLinearMap a = coQ (flats H n).toContinuousLinearMap ((station H n) a):=by apply LinearMap.ext;intro z; exact congr_fun ((deckW H n).apply_symm_apply (F z)).symm a -- q
       let X(i:Tab (Shade H) n):= (station H n) i; have ht:Oriel P F.toContinuousLinearMap i i= CapeV C H v n (X i) (X i):=by change P.wick (Ferry F.toContinuousLinearMap i) (Ferry F.toContinuousLinearMap i)=_;rw [he]; exact congrFun (congrFun ((Hport C v H n h).choose_spec.1) (X i)) (X i) -- prop
       obtain ⟨p,t⟩:=i; rw [ht]; let y:= (p,t); have hb : CapeV C H v n (X y) (X y)=T.val t t (0-0):=by convert (dripped H v h C p 0 0 t t) using 1; simp [X,y]
       rw[hb]; exact T.lease ..
end poll
open Flock Stranded
local notation "S!"=>Bid.Dir H N
lemma canyon (u:S!)(b:ℝ)(hp:0 ≤ b)(f g:S!→ℝ)(k:ℕ)(h: Bond f)(hc:Bond g)(ht:∀ x:S!, (N.val:ℝ)^5*‖f x-g x‖≤ b*(1+‖spool H N x‖)^k) (C:KernelChoices)(v:Train r)(hz:4 ≤ r):
       let B:= Vessel C v H N hz; let m:=PertExtension.Chart.tangent H (Exterior.Body 1 N); let X:=Dawn m B
       ‖X f u-X g u‖ ≤ quotaB (Shade H) ((terra_money C hz).choose+1) k*(1+‖spool H N u‖)^k*b/(N.val:ℝ):=by
          intro A m X; let Z:= spool H N; let T:=Z u; let F(i:S!):=f (i+u); let G(i:S!):=g (i+u); let n:ℝ:=N.val; have hn:0<n:=by unfold n; exact_mod_cast N.pos
          have hh(f:S!→ℝ)(h: Bond f): Bond (fun i=> f (i+u)):= h.comp (fun k=>by simp_rw [map_add]; exact (Bond.glyph k).add (Bond.keep _))
          have hF:Bond F:=hh f h; have hG:Bond G:=hh g hc; rw [show X f u-X g u=A.average m (F-G) from (curb m A _ _ hF hG).symm]
          have ht(i:S!): ‖(F-G) i‖ ≤ b/n^5*clockY T Z.toContinuousLinearMap i^k:=by
               apply le_trans ?_ (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity: (0:ℝ) ≤1+‖Z (i+u)‖) (show 1+‖Z (i+u)‖ ≤ _ from by unfold clockY T; rw [map_add]; change 1+ _ ≤1+‖Z u‖+‖Z i‖;linarith only [norm_add_le (Z i) (Z u)]) k) (by positivity : (0:ℝ)≤ b/n^5))
               change ‖f _-g _‖≤b/n^5* _; let y:= i+u; rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_comm]; exact ht _
          refine (Mile m A _ (breathQ C v H N hz) T _ (b/n^5) (by positivity) k ⟨hF.sub hG,ht⟩).trans_eq ?_; change n^4 * _ * (1+‖T‖)^k *(b/n^5)= _ * b/n; field_simp; unfold T Z; ring
end YM.OPE.Silt.Phere
