import YM.Qlocal.Quipu.Luxury
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Eluder
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Turbin Sonnet Marker Kinetic Primitives.GCC.Anchor
variable {ι α :Type}[Fintype α][DecidableEq α] {G:Gauge} {n:Side} {k N :ℕ} {a b r :ℝ}{R:Marker.Census α}
open Ballad Dais Zora Lasso AnalyticNext.QuarticMatch Joint CubicMatch
open Album Exterior
namespace Incline
namespace Bookworm
open Macarons Tracks Tender Lagger Sonnet.Tern
local notation "S"=> Coarse G
local notation "Z"=> Coarse G ⊕α
local notation "Ω"=> rule (Coarse G) n
local notation "X"=> rule (Coarse G⊕α) n
local notation "E"=> fieldDir G n 1
-- seed: true cochain period F. need also legitimate & projection debt.Account.Provo. K total includes Fk slots/inertia. admissible grade tape κ. Body.Type shape. stamp coefficient lenses.
structure Anthem (ι:Type)(α:Type)(G:Gauge) [Fintype α] (n:ℕ)(Γ:ι→ℝ)(a:ℝ)(v:ℕ)(Ad:Side→Prop) (P:ℕ→ι→Ink.Money.Bills ((Coarse G) ⊕α)): Type where
   tune : ℕ→ι→ Tune ((Coarse G)⊕α)
   d : ℕ→ι→ℝ
   fund : ℕ→ι→Side→ℝ
   pays k (h:k≤ n) : CreditF Γ v (d k) ∧ Weight Γ v (fund k)
   story k (i:ι) : k ≤ n→ Ink.Money.Pert Ad (P k i) (tune k i|>.typeR) a (d k i) (fund k i) k
variable {Ad:Side → Prop} {Γ:ι→ℝ}{m k0 r':ℕ}
omit [DecidableEq α] in
lemma hired {V:ℕ→ι→Ink.Money.Bills ((Coarse G) ⊕α)} (W:∀ k≤N, License Ad Γ (V k) a k m) (ha: 0<a) : Nonempty (Anthem ι α G N Γ a m Ad V):=by
 choose F A C hf ht he using W; choose T hK1 hK using fun (k:ℕ) (h:k ≤ N) i=> Tune.tuned _ (he k h i).1 ha
 let ν : (0:ℕ) ≤ N:= Nat.zero_le _; let t(k:ℕ):= if h:k≤N then T k h else T 0 ν; let a0(k:ℕ):= if h:k≤N then A k h else 0; let f(k:ℕ):= if h:k≤N then C k h else 0
 refine ⟨t,a0,f,fun k h=>?_,fun k i h=>?_⟩; · unfold a0 f; rw [dif_pos h,dif_pos h]; exact ⟨hf ..,ht ..⟩ -- .. must h used by expected terms
 unfold f a0 t; rw [dif_pos h,dif_pos h,dif_pos h]; exact ⟨hK1 k h i, fun n hn=> by rw [hK]; exact (he k h i).2 n hn⟩
abbrev lap (V:α→ℕ)(s:Senses R)(e:ℕ):= e+Lagger.dues V s.val
abbrev lap_s (V:α→ℕ)(s:Senses R)(e:ℕ):= lap V s e+(essence s).card
abbrev warrant (k:ℕ)(s:Senses R)(V:α→ℕ) (N:ℕ) := lap_s V s k ≤ N
local notation "I"=> ι
variable {P:ℕ→ι →Ink.Money.Bills ((Coarse G) ⊕α)} (T: Anthem ι α G N Γ a m Ad P)
namespace Anthem
lemma charged (s:Senses R)(V:α→ℕ)(h:warrant k s V N)(hk:k0 ≤ k): warrant k0 s V N:= Nat.le_trans (Nat.add_le_add_right (Nat.add_le_add_right hk _) _) h
variable (W:Noon G N) (O:Lattice.Order) (Y: α→ℕ) (t:ℕ)(h:∀ s:Senses R,warrant k s Y N) (ha:0<a)
variable {e g:ℕ} (s:Senses R)
local notation "τ[" s "," n "]"=> lap_s Y s n
local notation "τ0[" s "," n "]"=> lap Y s n
variable (x:ι)
local notation "S[" s "," e "]"=> T.tune (lap_s Y s e) x
set_option quotPrecheck false
local notation "H0[" s "," e "]"=> (charged (k:=k) s Y (h s) (Nat.le_of_lt_succ (Fin.isLt e)))
def plan (O:Lattice.Order) (h:∀ s:Senses R,warrant k s Y N) (W:Noon G N) (x:ι): Stanza R G Y k:= fun s e n=> how (T.tune (lap_s Y s e.val) x) s W O (charged s Y (h s) (Nat.le_of_lt_succ (e.isLt))) (T.story (lap_s Y s e.val) x (charged s Y (h s) (Nat.le_of_lt_succ e.isLt))|>.1) n.val
abbrev stanza (x:ι)(t:ℕ):= Stanza.son (plan T Y O h W x) t
-- check order via errors
local notation "V"=> T.stanza W O Y h x t
variable (U:ℝ) (hU:0<U)(hx:U*(5*N:ℝ) ≤ a/2)
noncomputable abbrev bill0 (j:Fin (k+1))(l:ℕ):= postage W (lap_s Y s j) l U * T.d (lap_s Y s j) x
include hU ha hx
omit hx hU ha
lemma census (e:ℕ):lap_s Y s e-(essence s).card= lap Y s e:= Nat.add_sub_cancel ..
include ha hU hx h
local notation "F[" n "," t "]"=> Fin (lap Y n t+1)
lemma provided (j:Fin (k+1)): U*(5*lap_s Y s j:ℝ) ≤ a/2:= le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by exact_mod_cast H0[s,j]) (by norm_num)) hU.le) hx
lemma pride (j:Fin (k+1)): CreditF Γ m (fun x=> T.bill0 W Y s x U j e):= by
 have hp:= (T.pays (lap_s Y s j) H0[s,j]).1; simpa only [Nat.zero_add] using! (freeC _ (show 0≤Ballad.postage W (lap_s Y s j) e U from mul_nonneg (Dais.bill_pos ..) (Real.exp_pos _).le)).mul hp
lemma charging (j:Fin (k+1))(i: Fin (lap Y s j+1)) : Album.Health ((T.plan Y O h W x) s j i) U (T.bill0 W Y s x U j i):= Ballad.poem (S[s,j]) s W O (H0[s,j]) (T.story (lap_s Y s j) x H0[s,j]|>.1) hU (le_trans (provided Y h ha s U hU hx j) (half_le_self ha.le)) _
noncomputable def cost (U:ℝ):ι→ℝ:= fun x => ∑ s:Senses R,∑ i:Fin (k+1),∑ j:Fin (lap Y s i+1), T.bill0 W Y s x U i j.val
set_option quotPrecheck false
local notation "H"=> T.cost (k:=k) (R:=R) W Y U
lemma credit : CreditF Γ m (T.cost (k:=k) (R:=R) W Y U):= CreditF.sum (univ:Finset (Senses R)) fun i _=> CreditF.sum (univ:Finset (Fin (k+1))) fun j h0=> CreditF.sum _ fun n _=> T.pride W Y h ha i U hU hx j
lemma health : (Stanza.son (T.plan Y O h W x) t).Allows U ((T.cost W Y U (k:=k) (R:=R)) x) := by
 constructor; intro i j n; let f:= fun s:Senses R=> ∑ i: Fin (k+1), ∑ j:F[s,i], T.bill0 W Y s x U i j
 have ht(s:Senses R) (i:Fin (k+1))(r:Fin (lap Y s i +1)) : 0 ≤ T.bill0 W Y s x U i r:= (T.pride W Y h ha s U hU hx i).nonneg x -- e implicits
 let Z1:Fin ((lap Y i j)+1):=n; apply sumBudget_mono (T.charging W O Y h ha i x U hU hx j n) (fun j' => (T.charging W O Y h ha i x U hU hx j n).1 j') le_rfl; unfold cost; exact le_trans (le_trans (Finset.single_le_sum (f:=fun r:Fin ((lap Y i j)+1)=> T.bill0 W Y i x U j r) (fun _ _=> ht i j _) (mem_univ Z1)) (Finset.single_le_sum (f:=fun j:Fin (k+1)=>∑ r:Fin (lap Y i j+1), T.bill0 W Y i x U j r) (fun i _=> Finset.sum_nonneg fun j _=> ht _ _ _) (mem_univ j))) (Finset.single_le_sum (f:=f) (fun i _=>Finset.sum_nonneg fun i _=> Finset.sum_nonneg fun j _=> ht _ _ _) (mem_univ i))
end Anthem
end Bookworm
end Incline
end YM.Qlocal.Quipu.Eluder
