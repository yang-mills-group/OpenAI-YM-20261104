import YM.FormalOPE.RG10.Carryon.Respect
import YM.FormalOPE.RG10.Carryon.Cash

/-! Algebraic transformation `posture` under perturbative frame and coupling replacement
prior to comparing any limits. No control of the size of the nonlinear coefficients assumed or proved.
But zero-order positioning *is* local and cannot dispense with its hypothesis. -/
noncomputable section
set_option autoImplicit false
namespace YM.FormalOPE.RG10.Carryon
open Gazebo Position Position.Grade Function Finset Maxwell Labels Extraction Filter Extra.FD
open PertExtension MeasureTheory Topology Metric Matrix PertExtension.Position PertExtension.Physical Triangle
open scoped Topology BigOperators ContDiff Classical
open PowerSeries Peal
variable {G : Gauge} {F : Frames G} {d : ℕ}
local notation "K" d=> Matrix (Deck F d) (Deck F d) fps
local notation "L" d=> Matrix (Deck F d) (Deck F d) ℝ
local notation "V" d=> Mark (Deck F d) PertExtension.Physical.Profile.n
local notation "ins"=> PertExtension.Position.insert (Deck F d) PertExtension.Physical.Profile.n
variable (D:Stock F)

def post (u : (V d) →fps) := ins u (posture D u)

variable {D} (X : Matrix (Deck F d) (Deck F d) fps) (p : Warp) (h : Official D)
variable {u : Mark (Deck F d) PertExtension.Physical.Profile.n → fps}
namespace Warp
lemma untie (u:(V d)→fps) : ins (p.charge ∘ u) (X.map p.charge) = p.charge ∘ ins u X:= funext fun k=> Eq.symm (insert_alg (p.charge : fps→+*fps) _ _ k)
lemma degrees (u: Mark (Deck F d) PertExtension.Physical.Profile.n→fps): (fun v=> constantCoeff ((p.charge ∘ u) v)) =fun v=> constantCoeff (u v) := funext fun _=> p.smoothed _
lemma look : (fun i=> Stg (X.map p.charge) i) 0= Stg X 0 := by ext i j; simp [Stg,p.smoothed]
lemma starts (D: Stock F)(u:(V d)→fps) : crib D (p.charge ∘ u)= crib D u := by unfold crib; rw [p.degrees]
lemma approve (hh:Credible D u): Credible D (p.charge ∘ u):= by unfold Credible; rw [p.starts,p.degrees]; exact hh

lemma stated (hr: respects D u X) : respects D (p.charge ∘ u) (X.map p.charge) := by
 intro n; unfold TestSystem.response; rw [-- under bind
    untie]; simp only [Function.comp_apply,turning]; simp_rw [AlignSeries.subst_finite (p:=p.x) p.atOrigin]
 let f (k:ℕ): (D d).Parameter:= fun i=> coeff k (ins u X (markIn _ i)); let s (k:ℕ):= coeff n (p.x^k)
 have hw k: (D d).select (f k)= if k=0 then (D d).target else 0:= hr k
 rw [show (fun i=>∑ k∈range (n+1), f k i * s k)=∑ k∈range (n+1), s k • f k from by funext i; rw [Finset.sum_apply];exact sum_congr rfl fun _ _=>mul_comm _ _]
 simp_rw [_root_.map_sum, map_smul, hw]; simp [s]
include h
lemma uprightward (hw:Credible D u): posture D (p.charge ∘ u)= (posture D u).map p.charge := by
 symm; apply respects.unique h (p.approve hw) (worth _ p (installed u h)) _ (stated _ p hw.sure)
 rw [show Stg ((posture D u).map p.charge) 0= _ from look _ p]; ext i j;
 simp [Stg,posture,p.starts]
lemma publish (hw:Credible D u) : post D (p.charge ∘ u)= p.charge ∘ post D u:= by unfold post; rw [uprightward p h hw,untie]
end Warp
section filters
variable {α:Type*}{l : Filter α} (X: α → Matrix (Deck F d) (Deck F d) fps){b:α→Mark (Deck F d) PertExtension.Physical.Profile.n→fps}
include h
local notation "v" a => PertExtension.Position.insert (Deck F d) PertExtension.Physical.Profile.n (b a) (X a)
local notation "f" n=> post D (b n)
theorem loading (hb:listens (D:=D) (l:=l) b) (hx: ∀ a, Upright (X a)) (ht:Tendsto (fun a=> Stg (X a) 0) l (𝓝 (1:L d))) (hv : listens (D:=D) (l:=l) (fun a => v a)): ∀ᶠ a in l, post D (v a)= post D (b a):= by
 let k (a):= (posture D (v a) * X a: K d)
 have ha a: post D (v a)= ins (b a) (k a):= insert_twice ..
 have hr : ∀ᶠ a in l, respects D (b a) (k a):= by
   filter_upwards [credential h _ hv] with a ho t
   unfold TestSystem.response; rw [← ha]; exact ho.sure t
 have hz : Tendsto (fun a=> Stg (k a) 0) l (𝓝 (1:L d)):=by
   have hh a : Stg (k a) 0= Stg (posture D (v a)) 0 * Stg (X a) 0:= by ext i j; simp [k,Stg,Matrix.mul_apply,map_sum,map_mul]
   simp_rw [hh]; exact (show ((1:L d)*1)=1 from mul_one _) ▸ ((start_up h _ hv).mul ht)
 filter_upwards [respects.stays h k hb (fun a=>(installed _ h).mul (hx a)) hz hr] with a hu; rw [ha a, hu]; rfl
end filters
end YM.FormalOPE.RG10.Carryon
