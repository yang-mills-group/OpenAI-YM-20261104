import YM.AllOrder.Haiku.Terrace
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

lemma Etiquette.adding {F G': ℕ→Ink.Money.Bills (Coarse G)} (h: Etiquette F n k)(H: Etiquette G' n k)(hA: Smooth k n F) (hB:Smooth k n G'): Etiquette (F+G') n k:= by
 have hx (x:ℝ→Link G n) (hp:ContDiffAt ℝ ω x 0): weigh x (fun i=>(F+G') i n) k= weigh x (fun i=> F i n) k+weigh x (fun i=> G' i n) k:= weigh_add hp (fun i hi=> (hA i hi).smooth.contDiffAt) (fun i hi=>(hB i hi).smooth.contDiffAt) le_rfl
 refine ⟨fun x y v w hv hw hQ hu=>((hx x hv).trans ((congr_arg₂ (fun a b:ℝ=>a+b) (h.stain x y v w hv hw hQ hu) (H.stain x y v w hv hw hQ hu)).trans (hx _ hw).symm)),fun x s hv=>?_⟩; exact ((hx x hv).trans ((congr_arg₂ (fun a b:ℝ=>a+b) (h.sign x s hv) (H.sign x s hv)).trans (hx _ ((orderTurn s).contDiff.contDiffAt.comp _ hv)).symm))
namespace Coat
open Project PertExtension.Series Radial
lemma memoir_plus {Λ:ι→ℝ}{F G':Theatre G ι} (H:memoir Λ F k)(h:memoir Λ G' k): memoir Λ (F+G') k:= by
 refine ⟨fun r hr i n=> ⟨(H.1 r hr i n).1.add (h.1 r hr i n).1, (H.1 r hr i n).2.adding ((h.1 r hr i n).2) (fun j hj=> (H.1 j (hj.trans hr) i n).1.read) (fun j hj=> (h.1 j (hj.trans hr) i n).1.read)⟩,fun r hr j=> ?_⟩; exact ((H.2 r hr j).joint (h.2 r hr j) (fun i n=> (H.1 r hr i n).1.read.smooth.contDiffAt.analyticAt) (fun i n=> (h.1 r hr i n).1.read.smooth.contDiffAt.analyticAt)).2

variable (A: (n:Side)→ Config G n→ℝ)
def clerk (A: (n:Side)→ Config G n→ℝ) (k:ℕ)(j:ℕ): Ink.Money.Bills (Coarse G):= fun n=>jet (A n∘ input G n) (j+k)
def Auditor (A:(n:Side)→Config G n→ℝ) (k:ℕ): Prop := ∀ n, (∀ i, i < k → 0 < i →  jet (A n ∘input G n) i=0) ∧ ContDiffAt ℝ ω (A n ∘input G n) 0 ∧ (∀ U V,A n (Lattice.gauge V U)=A n U) ∧ ∀ U s, A n (pull s 0 U)=A n U
variable (H:Auditor A k)
include H
lemma reads (v:ℝ→ Link G n)(hv:ContDiffAt ℝ ω v 0) (_hk:k=0 ∨ 0<k+N) : weigh v (fun i=> clerk A k i n) N= someJ (A n ∘ Haiku.life v) (N+k) := by
 let f:=A n ∘ input G n; change _=someJ (f ∘ echo v) _; rw [weigh_curved ((H n).2.1) hv]; unfold weigh; rw [show N+k+1=k+(N+1) from (by omega)]; conv_rhs => rw [Finset.sum_range_add]
 have hz : ∑ i∈Finset.range k,someJ (jet f i ∘ v) (N+k-i)=0:= Finset.sum_eq_zero fun i hi=> by
    let d:= N+k-i; have hd:0<d:= by unfold d; have he:= mem_range.mp hi; omega
    by_cases hh:i=0; subst i; rw [show jet f 0 ∘ v=(fun _=> f 0) from funext fun _=>jet_zero ..]; exact ((Act.static (f 0) (n:=N+k-0)).writes _ le_rfl).trans (if_neg (show _ from hd.ne'))
    rw [(H n).1 i (mem_range.mp hi) (by omega)]; exact ((Act.static (0:ℝ) (n:=d)).writes _ le_rfl).trans (by simp [d,just])
 rw [hz,zero_add]; exact Finset.sum_congr rfl (fun i hi=>by rw [show k+i=i+k from add_comm .., Nat.add_sub_add_right]; rfl)
lemma etiquette_clerk (n:Side) (j:ℕ): Etiquette (clerk A k) n j:= by
 have hi:k=0 ∨ 0<k+j:= by omega
 refine ⟨fun v w u x hV hW hQ hU => ?_,fun v s hV=> ?_⟩
 · let f:=A n; have hx:(f ∘ Haiku.life (G:=G) w) =ᶠ[𝓝 0] f ∘ Haiku.life (G:=G) v:= hU.mono fun i he=> (congr_arg f he).trans ((H n).2.2.1 ..); rw [reads A H v hV hi,reads A H w hW hi]; exact congr_arg (fun x:ℝ=> _* x) ((hx.iteratedDeriv _).eq_of_nhds.symm)
 let w:= orderTurn (G:=G) s ∘ v; have ht:ContDiffAt ℝ ω w 0:= (orderTurn s).contDiff.contDiffAt.comp _ hV
 have hx(t:ℝ) : A n (Haiku.life (G:=G) w t)=A n (Haiku.life (G:=G) v t):= by
     apply Eq.trans (b:=A n (pull s 0 (input G n (t• v t)))); · apply congr_arg; unfold Haiku.life; simp only [Function.comp_apply]; change Stationary.input G n (t• orderTurn _ _)=_; rw [← map_smul]; exact (flip_links ..).symm
     exact (H n).2.2.2 _ _
 rw [reads A H v hV hi,reads A H _ ht hi]; exact congr_arg (fun f=> someJ f _) (funext fun t=> (hx t).symm)
omit H in
lemma Ready.clerk {Λ:ι→ℝ}{A:ι→ ((n:Side)→ Config G n→ℝ)} (V:∀ i,Auditor (A i) k)(h:∀ k0, Ready Λ (fun i n=> A i n ∘ input _ _) k0) (j:ℕ)(hj:k≤2) : memoir Λ (fun i=>Coat.clerk (A i) k) j := by -- omit H
 refine ⟨fun j' _ i n=> ⟨(Project.maturity _ _).up (show j'+k ≤ j'+2 from by omega), etiquette_clerk (A i) (V i) n j'⟩,?_⟩; intro p hp r; by_cases he: r+1=p+k; · refine (h r).lined (fun i n=>?_) ; unfold Coat.clerk; dsimp only; rw [←he]; exact (Project.self _ (V i n|>.2.1) _).symm
 apply Ready.nought; intro i n; exact Project.other _ (Ne.symm he) -- Ne.symm he
end Coat
end YM.AllOrder.Haiku
