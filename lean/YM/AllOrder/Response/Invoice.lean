import YM.AllOrder.Response.Wallet
import YM.X.Gauss.Plausible
import YM.Work.G05.Taylor
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Response
open Finset Filter Function Laplace.SigmaP Laplace PositionX.Jet PertExtension.Series PositionX.Gauss Radial Asymptotics Work.G05
open scoped Topology ContDiff BigOperators Classical
variable {Y X:Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
   [NormedAddCommGroup X][NormedSpace ℝ X]{P:ℝ→X} {u v:Book X}{n k:ℕ}{q:X}
section finite
-- plausible tpoly regularity. mechanical pulses commute.
lemma nearStep {F:Y→ℝ} {B:X→ₗ[ℝ] Y} (p:Y)(h:Plausible F): Plausible (fun x=>F (p+B x)):=by
 induction h with
 | atom c=>exact Plausible.atom _
 | times f y _ ih=>
    convert ih.mul (Plausible.add (Plausible.atom (y p)) (Plausible.line (y.comp B))) using 1; ext; simp
 | add h h' H H'=>exact H.add H'
variable {u:Book X} (h:∀ i,Plausible (u i))
include h
lemma square_p (k:ℕ):∀ n,Plausible (energy u k n):= by
 induction k with
 | zero=> intro n; rw [level]; by_cases hi:n=0; exact hi.symm ▸ (show Plausible (wirings (X:=X) 1 0) from Plausible.atom _); rw [show _ from (show wirings (X:=X) (fun _=>1) n=0 from funext (fun x=>if_neg hi))]; exact Plausible.atom _
 | succ k ih=>
    intro n; rw [powered]; have he:= funext (fun x=> plus_real (energy u k) u x n)
    refine he.symm ▸ (show Plausible _ from ?_); rw [show (fun x=> ∑ i∈Finset.range (n+1),_)=∑ i∈Finset.range (n+1),energy u k i * u (n-i) from funext fun i=> by simp only [Finset.sum_apply]; rfl]; exact Plausible.sum fun i _=> (ih i).mul (h _)
lemma along_p (a:Tape)(n k : ℕ):Plausible (arrow a u n k):= by
 rw [arrow, Finset.sum_apply]; exact Plausible.sum fun i _=> (square_p h i k).scale _
lemma exp_p (h':u 0=0)(k:ℕ):Plausible (EXP u k):=by rw [Expo h' (le_refl k)]; exact along_p h _ _ _
lemma log_p (h':u 0=1) (k:ℕ): Plausible (LOG u k):= by rw [Lords h' (le_refl k)]; apply along_p; intro i;exact (h i).sub (level u ▸ square_p (fun i=>h i) 0 i) -- wired.
end finite
section algebra
-- proof alignment along ANY real varying directions
variable {m:ℕ}[FiniteDimensional ℝ X]
def echo (P:ℝ→X)(t:ℝ):=t • P t
lemma weigh_curved {G:X→ℝ} (h:ContDiffAt ℝ ω G 0)(hp:ContDiffAt ℝ ω P 0): someJ (G ∘ echo P) = weigh P (jet G):= by
 funext n; let f:= echo P; have he:f 0=0:= zero_smul ..; have hF:ContDiffAt ℝ ω f 0:= contDiffAt_id.smul hp
 let g:= blockTaylor n G
 have hv:g ∘ f=grass P (jet G) n := by
   funext x; unfold g blockTaylor grass delay Function.swap; rw [comp_apply,Finset.sum_apply]; refine Finset.sum_congr rfl fun i hi=>?_ ; exact Tensor.homogeneous (Tensor.coeff G i 0) (P x) x
 have hx : someJ (G ∘ f) n=someJ (g ∘ f) n:= by unfold someJ; rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition (x:=0) (he.symm ▸ h) hF le_top, iteratedDeriv_vcomp_eq_sum_orderedFinpartition ((blockTaylor_contDiff n G ω).contDiffAt) hF le_top]; rw [he]; congr 1; refine Finset.sum_congr rfl fun i _=>?_ ; rw [show iteratedFDeriv ℝ i.length g 0=_ from blockTaylor_jets (h.of_le le_top) i.length i.length_le]
 exact (show someJ (G ∘ echo P) n=someJ (grass P (jet G) n) n from hv ▸ hx).trans ((studio hp (show Budget (P 0) (jet G) n from fun i _=> (Plausible.stamp G i).smooth.contDiffAt)).writes n le_rfl)

variable (hp:ContDiffAt ℝ ω P 0)
omit hp [FiniteDimensional ℝ X] in
lemma weigh_zero (P:ℝ→X)(u:Book X): weigh P u 0=u 0 (P 0):= by simp [weigh]
omit hp [FiniteDimensional ℝ X] in
lemma weigh_higher (h:(∀ i<m,u i=0))(n:ℕ) : weigh P u (n+m)=weigh P (fun i=>u (i+m)) n := by
 unfold weigh; rw [show n+m+1=m+(n+1) from (by omega), Finset.sum_range_add]; rw [show ∑ i∈Finset.range m,someJ (u i∘ P) (n+m-i)=0 from Finset.sum_eq_zero fun i hi=> ?_,zero_add];
 · apply Finset.sum_congr rfl; intro i hi; rw [show m+i=i+m from add_comm ..,show n+m-(i+m)=n-i from (by omega)]
 rw [h i (mem_range.mp hi)]; have ht : someJ ((0:X→ℝ) ∘ P) (n+m-i)=just (0:ℝ) (n+m-i):=(Act.static (n:=n+m-i) _).writes _ le_rfl; rw [ht]; simp [just]
omit hp [FiniteDimensional ℝ X] in
lemma weigh_const {q:X}(u:Book X):weigh (fun _=>q) u=Function.swap u q:=by
 funext i; unfold weigh; simp_rw [show ∀ (j n:ℕ), someJ (u j ∘ (fun (_:ℝ)=>q)) n= just (u j q) n from fun j n=> (Act.static (n:=n) _).writes _ le_rfl]; rw [Finset.sum_eq_single_of_mem i (by simp)]; simp [just]; intro b hb he; simp only [just]; rw [if_neg]; simp only [mem_range] at hb; omega
end algebra
end YM.AllOrder.Response
