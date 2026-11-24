import YM.AllOrder.Haiku.Agent
set_option autoImplicit false
noncomputable section
namespace YM.AllOrder.Haiku
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Response Ink Ink.Method Ink.Money
open Tree Wilson Exterior Precision Push Pressure Next.Fluctuations MeasureTheory
open Stationary
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
variable {G:Gauge} {n m c:Side}{a C D:ℝ}{k N:ℕ} {ι:Type}
local notation "L"=> Coarse G
-- defeq Ward.Link footing
local notation "F[" n "]"=> Stationary.Link G n

namespace Coat
open PertExtension.Series Radial
-- ticket at packet . Pure order shift r. Model exposed scalar log offline at EVERY j beyond.
def trade (r:ℕ)(S:Packet G k) (j:ℕ)(n:Side): F[n]→ℝ := if r≤j then jet (turnSeries S (m:=n)) (j-r+k) else 0
variable (r:ℕ){S:Packet G k} (h:SumBudget (fun j=>(S j).budget a) C)(hp:0<a)
include h hp
lemma pump (v:ℝ→F[n])(he: ContDiffAt ℝ ω v 0) (j:ℕ) : weigh v (fun i=> trade r S i n) j = if r≤j then someJ ((turnSeries S (m:=n)) ∘ echo v) (j-r+k) else 0:= by
 let f:=turnSeries S (m:=n); split; rename_i hv;
 · have ht:AnalyticAt ℝ f 0:= turns_analytic S hp h; have hh:= turns_low (m:=n) S hp h; have hu(i:ℕ)(hi:i<k) : jet f i=0:= by ext y; rw [jet, (rays_jet ht k).1 hh i hi]; simp
   rw [weigh_curved ht.contDiffAt he,weigh_higher hu (j-r)]; nth_rw 1 [← show j-r+r=j from Nat.sub_add_cancel hv];
   rw [weigh_higher (m:=r) (show ∀ i<r, trade r S i n=0 from fun i hi=> if_neg hi.not_ge)]; apply congr_fun _ (j-r); apply congr_arg _ (funext (fun x:ℕ=>?_)); unfold trade; rw [if_pos (Nat.le_add_left ..),Nat.add_sub_cancel]
 unfold weigh; refine Finset.sum_eq_zero (fun i hi=>?_); have ht:i ≤ j:= Nat.le_of_lt_succ (Finset.mem_range.mp hi); dsimp only; rw [show trade r S i n=0 from if_neg (by omega)]; exact ((Act.static (0:ℝ) (n:=j-i)).writes _ le_rfl).trans (by simp [just]) -- may beta
lemma trade_et (he:∀ i,(S i).Invariant)(j:ℕ)(n:Side): Etiquette (trade r S) n j:= by
 have hh : ∀ t U, orbitRaw S (Lattice.gauge t U)=orbitRaw S (U:Config G n):= by intro t U; simp only [orbitRaw,Work.F05.pull_gauge_zero,Work.F05.uncut_gauge S he]
 refine ⟨fun v w u x hV hW hQ hU => ?_,fun v s hV=> ?_⟩
 · let f:=orbitRaw S (m:=n); have hx:(f ∘ Haiku.life (G:=G) w) =ᶠ[𝓝 0] f ∘ Haiku.life (G:=G) v:= hU.mono fun i he=> (congr_arg f he).trans (hh ..); simp only [pump r h hp v hV,pump r h hp w hW]; apply if_congr Iff.rfl ?_ rfl; exact congr_arg (fun x:ℝ=> _* x) ((hx.iteratedDeriv _).eq_of_nhds.symm) -- check
 let w:= orderTurn (G:=G) s ∘ v; have ht:ContDiffAt ℝ ω w 0:= (orderTurn s).contDiff.contDiffAt.comp _ hV
 have hx(t:ℝ) : orbitRaw S (Haiku.life (G:=G) w t)=orbitRaw S (Haiku.life (G:=G) v t):= by
     apply Eq.trans (b:=orbitRaw S (pull s 0 (input G n (t• v t)))); · apply congr_arg; unfold Haiku.life; simp only [Function.comp_apply]; change Stationary.input G n (t• orderTurn _ _)=_; rw [← map_smul]; exact (flip_links ..).symm
     exact orbit_axis .. -- arguments
 rw [pump r h hp v hV,pump r h hp _ ht]; exact if_congr Iff.rfl (congr_arg (fun f=> someJ f _) (funext fun t=> (hx t).symm)) rfl

omit h hp
lemma trade_r (j:ℕ)(n:Side) (he : k≤r+2): Rank F[n] (j+2) (trade r S j n):= by unfold trade; split; exact (Project.maturity _ _).up (by omega); exact Rank.nil _ 0
-- ready frames all positive ranks from orbit_cost & Jet.
variable {F : ι → Packet G k}{Λ:ι→ℝ}
lemma tradeStory (h:Curled Λ F) (j p:ℕ): Ready Λ (fun i=> trade r (F i) j) p:= by
 by_cases ht:r≤j; swap; · apply Ready.nought; intros i n; rw [trade,if_neg ht]; simp -- maybe pi.zero
 by_cases hx: j-r+k=p+1; swap; · apply Ready.nought; intro i n; rw [trade,if_pos ht]; exact Project.other _ hx
 obtain ⟨t,ht',C,hC,hV⟩:=h; obtain ⟨η,D,hD,hL,H⟩:= orbit_cost G k p ht'; choose A hA hψ using fun i=> H (F i) (C i) ((hV i).1); refine ⟨A,η,_,hD,hC.mul (gia D hL), hA,fun i n=>?_⟩; rw [trade, if_pos ht,hx]; apply Coat.remake _ _ (Project.self _ (turns_analytic _ ht' ((hV i).1)).contDiffAt _).symm (hψ i n)
end Coat
end YM.AllOrder.Haiku
