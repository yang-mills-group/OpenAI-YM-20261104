import YM.AllOrder.Haiku.Spoil
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
open Work.F05 PertExtension.Series Radial
section refund
def summer (p:Clip)(W:PathData G) (a:ℝ) (n:Side)(U:Config G n) := a*secondTerm p W U + Precision.loop W U
def Stipend (p:Clip)(W:PathData G)(a:ℝ)(k:ℕ)(n:Side):Link G n→ℝ:= clerk (fun n=>mainTerm (n:=n) p W) 2 k n+clerk (Coat.summer p W a) 0 k n

variable (p:Clip) (V:ι→PathData G)(Λ:ι→ℝ)(q:ι→ℝ) (γ:ι→ℝ) (hq:Grade Λ q) (hV:∀ i,(V i).Bounds p a C (q i))
lemma Ready.scaleR {f:ι→Ink.Money.Bills (Coarse G)}(h:Ready Λ f k)(he:∀ i n,AnalyticAt ℝ (f i n) 0) (hG:Grade Λ (fun i=> |γ i|)): Ready Λ (fun i n=> γ i • f i n) k:= by
  obtain ⟨A⟩:= h; refine ⟨fun i=>(γ i:ℂ) • A.shape i,A.heigh,_,A.pos,hG.mul A.bill,fun i j t=> ?_,fun i n=> (A.period i n).weigh _ (he i n)⟩; have hm:= Firm.const (α:=Keys k) A.pos (γ i:ℂ); simpa only [Complex.norm_real,Real.norm_eq_abs] using! hm.mul (A.price i j t)
lemma Ready.anyPackets (F:ι→Packet G N)(a _C:ℝ)(c:ι→ℝ)(h:Grade Λ c)(he:∀ i, SumBudget (fun j=>(F i j).budget a) (c i))(hz:0<a)(k:ℕ): Ready Λ (fun i n=> turnSeries (F i) (m:=n)) k:= by
 obtain ⟨u,M,hu,hM,H⟩:= orbit_cost G N k hz; choose L' hl hh using fun i=> H (F i) _ (he i); exact ⟨L',u,fun i=> c i*M,hu,h.mul (gia M hM),hl,hh⟩
variable [Nonempty ι] (hG:Grade Λ fun i=> |γ i|)
include hV hG hq
lemma caps (hs:G.Simple)(n:ℕ): memoir Λ (fun i=> Stipend p (V i) (γ i)) n:= by
 let g i:=V i; have hz:0<a:= (hV (Classical.arbitrary _)).width; obtain ⟨u,M,hu,hM,H⟩:=column_price G -- use ∀k not constant
      n C p.direct hz p.quadratic_pos.le; clear u M hu hM H
 let F₀ i c:= inputSeries p (V i) (m:=c); let F₁:= fun i c=> turnSeries (V i).cubic (m:=c); let F₂:= fun i c=> turnSeries (V i).quartic (m:=c); let F₃:= fun i c=>turnSeries (V i).loop (m:=c)
 have h0 i c:= stain_knit (m:=c) _ _ (hV i); have h1 i c:= stain_ink (m:=c) (V i).cubic hz (hV i).three (fun j=>(hV i).invariant j|>.2.1); have h2 i c:= stain_ink (m:=c) (V i).quartic hz (hV i).four (fun j=>(hV i).invariant j|>.2.2); have h3 i c:= stain_ink (m:=c) (V i).loop hz (hV i).two (fun j=>(hV i).invariant j|>.1)
 let f0 (i:ι)(c:Side):Config G c→ℝ:= mainTerm p (V i); let g0 (i:ι):=(clerk (f0 i) 2); let f1 (i:ι)(c:Side):= summer p (V i) (γ i) c
 have hu(k:ℕ): Ready Λ F₀ k:= by
    obtain ⟨u,B,hu,hM,H⟩:= column_price G k C p.direct hz p.quadratic_pos.le; choose F hF hv using fun i=> (H p (V i) _ _ _ le_rfl (hV i) (hV i).rows).2; exact ⟨F,u,fun _=>B,hu,gia _ hM,hF,hv⟩
 have he:0≤ C:= budget_nonneg (hV (Classical.arbitrary _)).three; let T:= fun c:Side=>input G c; have hg : ∀ i (c:Side),f0 i c ∘ T c= F₀ i c+F₁ i c+F₂ i c:= fun i c=> intent ..
 have hx(i:ι)(c:Side) : Stationary.Pointwise (f0 i c ∘ T c):= by rw [hg]; exact ((h0 i c).add (h1 i c)).add (h2 i c)
 have h: memoir Λ g0 n:= by
   refine Ready.clerk (k:=2) (G:=G) ?_ ?_ n le_rfl
   · intro i c; refine ⟨fun j hj he=> ?_, (hx i c).analytic.contDiffAt,fun U V=> mainTerm_gauge (hV i) ..,fun U s=> orbit_axis (fun g=> quadratic p (V i) g+uncut _ g+uncut _ g) U s⟩
     have hu := Project.still_one hs ((hx i c).stained) (hx i c).analytic; funext r; rw [jet,show j=1 by omega,hu]; simp
   intro k; let hp i c:= (h0 i c).analytic; have hF:= (Ready.anyPackets Λ (fun i=>(V i).cubic) a C _ (gia _ he) (fun i=>(hV i).three) hz k); let H:= ((hu k).joint hF hp (fun i c=>(h1 i c).analytic)).2; refine Ready.lined (H.joint (Ready.anyPackets Λ _ a C _ (gia _ he) (fun i=> (hV i).four) hz k) (fun i c=>(hp i c).add ((h1 i c).analytic)) (fun i c=>(h2 i c).analytic) |>.2) (fun i c=>?_); change _=iteratedFDeriv _ _ (f0 i c ∘ T c) _; rw [hg]
 refine memoir_plus h (show memoir Λ (fun i=>clerk (f1 i) 0) n from Ready.clerk ?_ ?_ n (by omega));
 · intro i c; refine ⟨by intros; omega, ((Stationary.Pointwise.add ((h0 i c).coin (γ i)) (h3 i c)).analytic).contDiffAt, fun v w=>?_,fun v s=> ?_⟩; · unfold f1 summer secondTerm; rw [loop_gauge (hV i)]; simp_rw [Patch.average, Work.F05.pull_gauge_zero, Work.F05.quadratic_gauge (hV i)]
   exact congr_arg₂ (·+·) (congr_arg ((γ i)*·) (orbit_axis _ v s)) (orbit_axis (uncut _) v s)
 intro k; exact ((Ready.scaleR Λ γ (hu k) (fun i c=>(h0 i c).analytic) hG).joint (Ready.anyPackets Λ (fun i=> (V i).loop) a C _ hq (fun i=>(hV i).two) hz k) (fun i c=> ((h0 i c).coin (γ i)).analytic) (fun i c=> (h3 i c).analytic)).2
end refund
end Coat
end YM.AllOrder.Haiku
