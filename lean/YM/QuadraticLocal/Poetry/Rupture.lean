import YM.QuadraticLocal.Poetry.Mast
/-!
# Algebra for publishing stamps before current photos. Resolution of Spectator role field. Width.
 Use with Φ.Document later. Mint Lumi.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Poetry
open Function Filter Lattice Laurent Wilson RG Gauge Precision Tree Exterior
open Matrix Finset Push Uniform
open AbsoluteSums AllOrder AllOrder.Ker AllOrder.Ker.Start AllOrder.Haiku AllOrder.Fire PertExtension.Series Radial
open AllOrder.Laplace AllOrder.Laplace.SigmaP Response AllOrder.Ink AllOrder.Ink.Method AllOrder.Ink.Field AllOrder.Ink.Money
open Primitives.TwoWave PositionX.Gauss Progress.ClassicalKin Progress.ClassicalKin.Tent RealSlice
open Sunrise Sunrise.Focus Sunrise.Aviary Stationary Picket
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius MeasureTheory
variable {V G0:Type} {ι α M: Type} [Nonempty ι] [Fintype M] [Fintype α][DecidableEq M] {G:Gauge} (H:Finset M)(q:M)(I:M→ Loan) {a C D b:ℝ} {n m:Side}{k d N l:ℕ}
local notation "Ω" => (Coarse G ⊕ M)
local notation "Z"=> Point M
local notation "E"=> Point (Coarse G⊕M)
namespace Agenda
variable {Γ:ι→ℝ}
local notation "J"=> Link G n
local notation "W"=> rule (Coarse G⊕M) n
-- V rank.Pay.PostPicture plus snapshot. Commercial audits.News.C.F. Along Vernal.
local notation "λ'" e:max=> guard I H e
variable (T: ℕ→ι→Ink.Field (Coarse G⊕M))(P:ℕ→ι→Roll G M)
variable (h:Marquis I Γ H a N l T)(hb:0<b)(hB:b ≤ a)
-- prefix grammar d.Live Outcome. No possible choosing R after-order because this uses ONLY Bank.
def lapse (v:ι)(x:rule (Coarse G⊕M) n)(d j:ℕ) : ℝ:=∑ i∈Finset.range d, ((P i v).folded i j).table n x
structure Shelled (H:Finset M)(q:M)(I:M→Loan)(T:ℕ→ι→Ink.Field (Coarse G⊕M))(P:ℕ→ι→Roll G M)(Γ:ι→ℝ) (l d:ℕ)(a:ℝ): Prop where
    booking i (hi:i<d): Booked H q I (P i) Γ i a l
    recollects i (hi:i<d) v n (A:Link G n)(w:rule M n) : (T i v).table n (mingle A w)=∑ j∈Finset.range d,((P j v).folded j i).table n (mingle A w)
variable (hh:k ≤ N)
variable (hx:Shelled H q I T P Γ l k b)
set_option quotPrecheck false
local notation "b'"=> descent b I H N
-- aggregate Field stack.N Using kernel of ONLY height k so specify Vernal predicate via P-array.Future.
def desk (k j:ℕ)(i:ι)(z:Option (Fin k)): Ink.Field (Coarse G⊕M):= z.elim (T j i) fun e:Fin k=> Field.scale ((P e.val i).folded e.val j) (-1)
def rupture (k:ℕ)(i:ι):= Field.sum (desk T P k k i)
local notation "M₀"=> rupture T P k
local notation "Op"=> Option (Fin k)
include hh hx h hb hB
lemma mirth (hq:q∈H): ∃ S:ι→Roll G M, Booked H q I S Γ k (Poetry.entry (descent b I H N) (guard I H k)) l ∧ ∀ i n (A:Link G n)(v:rule M n), (T k i).table n (mingle A v)=lapse P i (mingle A v) k k + (S i).total n A v:=by
 have he':= Agenda.day H I N hb; let b₁:=descent b I H N;
 obtain ⟨L,hL,hY⟩:= h.pay k hh; choose f hf hm using fun j:Fin k=> status H q I (P j.val) (show 0<b₁ from he'.1) (le_refl b₁) (le_trans (Nat.le_of_lt j.isLt) hh) (hx.booking _ j.isLt) hb
 let Q(u:Op)(x:ι):= u.elim (L x) (fun j=> f j k x); have hT(t:Op):CreditF Γ l (Q t):=by cases t <;> first | exact hL | exact hf _ k hh
 let V(i:ι):= ∑ t:Op,Q t i; let U i:= desk T P k k i; have hv i (v:Op): (U i v).Good b₁ (Q v i) (λ' k) ∧ ∀ e,Depicted H ((U i v).slip e) := by
    rcases v with _|v; · exact ⟨ (hY i).debt (he'.2.1.trans hB) le_rfl le_rfl, h.viewed k hh i⟩
    have ht:= hm v k hh i; let W₀:= ((P v.val i).folded v.val k)
    refine ⟨ (Field.scale_good W₀ ht.1 (-1)).debt le_rfl ?_ ?_,ht.2.1.tracked⟩; · simp only [abs_neg,abs_one,one_mul]; exact le_rfl
    unfold Agenda.guard plusK; omega
 have hR i: SumBudget (fun z:Op=> Q z i) (V i):= budget_finite (fun t=> (hT t).nonneg i) le_rfl; have hs i: (rupture T P k i).Good b₁ (V i) (λ' k):= Field.keep (U i) (fun x=> (hv i x).1) (hR i)
 let f0(i:ι)(n:Side)(v:rule M n): Book (Link G n):= fun j A'=> (T j i).table n (mingle A' v)
 let z (i:ι)(n:Side)(t:Fin k)(v:rule M n) : Book (Link G n):= fun j A'=> (((P t i).folded t j).table n) (mingle A' v)
 let g i n (v:rule M n):= ∑ t: Fin k,z i n t v; let W₁ i n (v:rule M n):= f0 i n v-g i n v
 have hz i n (v:rule M n)(j:ℕ)(x:Link G n):W₁ i n v j x=(T j i).table n (mingle x v)-lapse P i (mingle x v) k j:= by unfold W₁ g lapse f0 z; simp_rw [Pi.sub_apply,Finset.sum_apply,←Fin.sum_univ_eq_sum_range]; -- ambiguity
 have hX i n (v:rule M n)(x:Link G n):W₁ i n v k x=(rupture T P k i).table n (mingle x v):=by
    unfold W₁ g rupture; let t:ℝ:= 0; rw [Field.contribution _ (fun z=> (hv i z).1) (hR i) he'.1.le, Fintype.sum_option]; change (T k i).table n _- _=((T k i).table n+ _ ) (mingle x v); simp only [Finset.sum_apply,Pi.add_apply]; rw [sub_eq_add_neg,← Finset.sum_neg_distrib]; apply congr_arg; apply Finset.sum_congr rfl; intro s hs; unfold U desk z; simp only [Option.elim_some]; rw [Field.scale_table]; simp -- edit
 have hg i n (v:rule M n) : Vernal G n (W₁ i n v) k := by
    let f:= h.vernal n v k hh i; let P' := z i n
    have hf0:= v_pile (S:=Finset.univ) (F:=fun t:Fin k=> P' t v) (fun t _=> ((hm t k hh i).2.2 n v).1) (fun t _ j hj=> lamp_s ((hm t j (hj.trans hh) i).1) he'.1.le v); apply f.minus hf0.1 _ hf0.2; intro j hj; obtain ⟨ν,hu,h'⟩:= h.pay j (hj.trans hh); exact lamp_s (h' i) h.pos.le v
 have hW i n (v:rule M n)(j:ℕ)(he:j<k): W₁ i n v j=0:= funext fun u=>(hz i n v j u).trans (sub_eq_zero.mpr (hx.recollects j he i n u v))
 have hs' (i:ι)(n:Side)(A:Link G n)(v:rule M n)(p:BaseSites G n): (M₀ i).table n (mingle A v)= (M₀ i).table n (mingle (A-gradientA G n p) v):=by simp_rw [← hX i]; symm; exact (hg i n v).steady (fun j hj => by rw [hW i n v j hj]; exact fun _ _=>rfl) (p,A)
 have ht' (i:ι)(n:Side)(A:Link G n)(v:rule M n)(u:G.El) : (M₀ i).table n (mingle (stain u A) v)=(M₀ i).table n (mingle A v):=by simp_rw [← hX i]; exact (hg i n v).paints u A
 obtain ⟨S,f,hF,h'⟩:= Poetry.mirage H q (M₀) he'.1 (CreditF.sum _ (fun i _=>hT i)) hs (fun i (d : (M₀ i).Ty)=> (hv i d.fst).2 d.snd) hs' ht' hq -- N money param
 refine ⟨S, ⟨f,hF,fun i=> ⟨ (h' i).1,(h' i).2.1 ⟩⟩, fun i n A v=> ?_⟩; rw [(h' i).2.2 n A v,← hX i n v A, hz, add_sub_cancel]; -- add_sub

end Agenda
end YM.QuadraticLocal.Poetry
