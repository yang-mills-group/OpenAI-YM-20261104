import YM.Qlocal.Harmony.Melody
import YM.Qlocal.Harmony.Press
/-!
 # Single mode Row for Stanza. Includes REAL analytic valuation, histories on cover.
     Foiling may maintain multiple marking conventions at once: do not reconstruct
     label from its numerical evaluation later.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Harmony
open Function Finset Filter Push Push.AbsoluteSums Lattice MeasureTheory Wilson Pressure RG Gauge
open Quipu Quipu.Sonnet Quipu.Sonnet.Tern
open Marker Dialect
open scoped BigOperators Classical ContDiff Topology Matrix.Norms.Frobenius
variable {V ι:Type} [DecidableEq V] {R:Census V} {G:Gauge} {s:Senses R}
    {n r m j k:ℕ} {c:Side} {g:V→ℕ}
set_option quotPrecheck false
namespace Motif
open Melody Shape Conductor
local notation "W"=> Lagger.dues g s.val
abbrev RangeJ (s:Senses R)(g:V→ℕ)(i:Fin (r+1)):= Fin (i.val+Lagger.dues g s.val+1)
local notation "P"=> Fin (r+1)
local notation "F[" i "]"=> RangeJ (s:=s) g i -- argument wrong?
abbrev Row (s:Senses R)(G:Gauge)(g:V→ℕ)(r:ℕ):= (i:Fin (r+1))→ (j:RangeJ s g i)→ Album ℕ s G j.val
abbrev Leaf (s:Senses R)(g:V→ℕ)(r:ℕ):= Σ i: Fin (r+1), RangeJ s g i
abbrev Ink (s:Senses R)(G:Gauge)(g:V→ℕ)(r:ℕ):= Σ p:Leaf s g r, Melody.Colors G p.2.val
abbrev Play (s:Senses R)(g:V→ℕ)(r:ℕ):= (i:Fin (r+1))→ (j:RangeJ s g i)→ℕ→Prop
-- Need cardinality independent of Ω.Signal.Frame.Scan contexts. Label sets countable
local notation "I"=> Ink s G g r
local notation "Q"=> Leaf s g r
local notation "R₀"=> Row s G g r
abbrev Labels (k:ℕ) : Type:= Melody.Colors G k
scoped instance : Countable (Ink s G g r) := inferInstanceAs (Countable (Σ p:Leaf s g r,Melody.Colors G p.2.val))
scoped instance : Nonempty (Ink s G g r):= by
 let i:P:=⟨0,Nat.succ_pos r⟩; let j: F[i]:=⟨0,Nat.succ_pos _⟩; let x:Q:= ⟨i,j⟩
 exact ⟨⟨x, (0, Fin.elim0)⟩⟩
open scoped YM.Qlocal.Harmony.Motif
variable (Y: Row s G g r)(Z:Play s g r) (o: V→Site c)(t:ℕ)
   {b C:ℝ}
abbrev permit (_Y:Row s G g r)(x:Play s g r) (p:Ink s G g r):Prop := x p.1.1 p.1.2 p.2.1
noncomputable abbrev foil (X:Album ℕ s G n)(Y:ℕ→Prop)(o:V→Site c)(t:ℕ) := Album.picture Y X o t
noncomputable def power (p:Leaf s g r):= p.1.val+Lagger.dues g s.val -p.2.val
noncomputable def lyric (q:ℝ)(U:Config G c):ℝ:= ∑ i:Fin (r+1), ∑ j:RangeJ s g i, q^(power (r:=r) (s:=s) (g:=g) ⟨i,j⟩)* Album.picture (Z i j) (Y i j) o t U
noncomputable def costs (p:Ink s G g r)(x:ℝ):ℝ:= Melody.coefficient (Y p.1.1 p.1.2) (Z p.1.1 p.1.2) p.2 x
structure Paid (a C:ℝ):Prop where
   bill(i:Fin (r+1))(j:RangeJ s g i): Album.Health (Y i j) a C

-- read without selecting other slots. either H.Post.auth or prior tear
lemma story (V:Stanza R G g r)(x:(Stanza.son V t).Decision) (s:Senses R) :
    Tale.markℓ (Stanza.son V t) x o s = lyric (V s) (x s) o t:= rfl
lemma chapters (F:Stanza R G g r) (t:ℕ) : (Stanza.son F t).Allows b C ↔ ∀ i,Paid (F i) b C:= ⟨fun h _=> ⟨fun _ _=>h.pay ..⟩,fun h=> ⟨fun i _ _ => (h i).bill ..⟩⟩
-- no rank bound needed for stencil geometry.T lease separate
noncomputable def footprint (_X:Row s G g r)(B:∀ i:(Fin (r+1)),RangeJ s g i→ ℕ→ℝ)(p: Ink s G g r):ℝ:= Melody.tagCost (B p.1.1 p.1.2) p.2
-- unused X but as type convenience to avoid s inference? adjust warnings
noncomputable def podPrice (s:Senses R)(G:Gauge)(g:V→ℕ)(r:ℕ)(c:ℝ):ℝ:= ∑ p:Leaf s g r, Melody.podCost G c p.2.val
lemma podPrice_pos (h: 0≤C) : 0 ≤ podPrice s G g r C:= by unfold podPrice; exact sum_nonneg (fun i _=> mul_nonneg h (sum_nonneg fun i _=>legend_pos i|>.le))
lemma economy (B:∀ i, RangeJ (r:=r) s g i→ ℕ→ℝ) (hb:∀ i j, SumBudget (B i j) C): SumBudget (Motif.footprint Y B) (Motif.podPrice s G g r C):= sigma_total (Motif.footprint (s:=s) Y B) _ (fun i=> Melody.tags _ (hb i.1 i.2)) (budget_finite (fun i=>budget_nonneg (Melody.tags (G:=G) (n:=i.2.val) _ (hb i.1 i.2))) le_rfl)
lemma costed (hp : Paid Y b C): SumBudget (fun i=> |costs Y Z i b|) (Motif.podPrice s G g r C):=
 budget_mono (economy Y (fun i j n=> (Y i j n).fare b) hp.bill) (fun _=> abs_nonneg _) (fun i=> payFactor (Y i.1.1 i.1.2) _ i.2 b)

-- elementary film
local notation "V0"=> fun i=>Vase.vac s G i
noncomputable abbrev vacant (s:Senses R)(G:Gauge)(g:V→ℕ)(r:ℕ): Row s G g r:= fun _ j _=> Vase.vac s G j.val
noncomputable abbrev silent (s:Senses R)(g:V→ℕ)(r:ℕ): Play s g r:= fun _ _ _=>False
noncomputable abbrev head (s:Senses R)(g:V→ℕ)(r:ℕ): Play s g r:= fun _ _ _=>True
noncomputable def dot (A: Vase s G n)(i:ℕ): Album ℕ s G n:= Function.update (fun _=> Vase.vac s G n) i A
noncomputable abbrev staccato (j:Ink s G g r)(w:ℝ):= dot (Melody.fundamental (Y j.1.1 j.1.2) j.2 w) j.2.1
noncomputable def motive (j:Ink s G g r)(w:ℝ): Row s G g r:= Function.update (vacant s G g r) j.1.1 (Function.update (vacant s G g r j.1.1) j.1.2 (staccato Y j w))
local notation "N[" i "]" => staccato Y i b
lemma vacotope : (Vase.vac s G n).fare b=0:=by unfold Vase.fare Vase.sizeC; simp [Vase.vac]
lemma saved (h:0≤C) : Album.Health (fun _ : ℕ=>Vase.vac s G n) b C:=by
 unfold Album.Health; simp_rw [vacotope]; exact budget_of_sum (fun _=>le_rfl) (by simp [h])
lemma empty (h:0 ≤ C) : Paid (vacant s G g r) b C:= ⟨fun _ _=>saved h⟩
lemma dormant (A:Vase s G n)(k:ℕ)(h:A.fare b≤C): Album.Health (Motif.dot A k) b C:=by
 let f (i:ℕ):=(dot A k i).fare b; have he : f= Pi.single k (A.fare b):= by
    ext i; unfold f dot; by_cases h:i=k
    · rw [h,Pi.single_eq_same, Function.update_self]
    rw [Pi.single_eq_of_ne h, Function.update_of_ne h, vacotope]
 have hh:HasSum f (A.fare b):= he.symm ▸ hasSum_pi_single ..
 exact ⟨fun i=>mul_nonneg (Vase.nn_size _) (Real.exp_nonneg _),hh.summable,hh.tsum_eq.le.trans h⟩
lemma camp (p:Ink s G g r): Paid (motive Y p b) b 1:=by
 constructor; intro i j; by_cases h:i=p.1.1
 · subst i; unfold motive; rw [Function.update_self]; by_cases h:j=p.1.2; · subst j; rw [Function.update_self]; exact dormant _ _ (Shape.freeTicket ..)
   rw [Function.update_of_ne h]; exact (empty zero_le_one).bill ..
 unfold motive; rw [Function.update_of_ne h]; exact (empty zero_le_one).bill ..

lemma solo_z (A: Config G c): solo (Vase.vac s G n) o t A=0:= by unfold solo; split; simp [Vase.vac,Vase.read,Vase.draw]; rfl
lemma nulled (Z:ℕ→Prop) (A:Config G c): Album.picture Z (fun _:ℕ=>Vase.vac s G n) o t A=0:= by
 unfold Album.picture Album.realize; refine Eq.trans (tsum_congr (g:=fun _=>0) fun i=>?_) tsum_zero; rw [Conductor.utt]; split; exact solo_z ..; rfl
lemma empty_lyric : lyric (vacant s G g r) Z o t= 0:= by funext q U; unfold lyric; simp_rw [show ∀ i (j:RangeJ (r:=r) s g i), Album.picture (Z i j) (vacant s G g r i j) o t U=0 from fun _ _=> nulled ..,mul_zero,sum_const_zero];rfl
-- metadata simplifications for elementary drivers
lemma alone (A:Vase s G n)(m:ℕ)(X:Config G c): Album.picture (fun _=>True) (dot A m) o t X= Conductor.solo A o t X:= by
 unfold Album.picture Album.realize; rw [tsum_eq_single m]
 · rw [Conductor.utt,if_pos trivial, dot, Function.update_self]
 intro j hj; rw [Conductor.utt, if_pos trivial,dot,Function.update_of_ne hj]; exact solo_z ..
lemma rendition (p:Ink s G g r) (z:ℝ) (U:Config G c): Motif.lyric (Motif.motive Y p b) (Motif.head s g r) o t z U= z^(power p.1)* Conductor.solo (Melody.fundamental (Y p.1.1 p.1.2) p.2 b) o t U:= by
 unfold lyric; rw [Finset.sum_eq_single p.1.1]
 · rw [Finset.sum_eq_single p.1.2]; unfold motive; rw [Function.update_self,Function.update_self]; exact congr_arg (z^(power p.1) * ·) (alone o t _ _ U)
   · intro b hb h; unfold motive; rw [Function.update_self,Function.update_of_ne h]; exact mul_eq_zero_of_right _ (nulled o t _ U)
   simp
 · intro i hi he; refine Finset.sum_eq_zero fun j _=>?_ ; unfold motive; rw [Function.update_of_ne he]; exact mul_eq_zero_of_right _ (nulled o t _ U)
 simp
end Motif
end YM.Qlocal.Harmony
