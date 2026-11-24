import YM.RegulatorIR.Budget.TraceGap
import YM.RegulatorIR.Budget.Knot

/-!
# Formal conditional Wick operations

Time-graded Polchinski recursion (replace an arbitrary connected graph step
by its polynomial heat-flow computation). These operations are on coefficients
only. Heat arguments ambient X. `V` is the log-interaction entering the Wick
step, hence the **negative** of action vertices for action sign convention.
`W` describes one external insertion, which can already be a full joined
product. `logHeat ... false` discards extensive vacuum reads; not a way to
hear an infinite-cover scalar action. True computes it (for finite index).
We do not apply the mean-substitution/reset here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Diagram
open Budget Budget.Packet Budget.Tuple Budget.Layer Function
open scoped Topology BigOperators Classical

variable {I:Type}

abbrev Ranked (I:Type):= (r:ℕ) → Packet I r
abbrev Orders (I:Type):= ℕ→Ranked I
abbrev gradedSymmetric (V:Orders I):Prop:=∀ e r, Packet.IsSym (V e r)

def heating (K:Layer I I) (T:Ranked I)(r:ℕ) : Packet I r:=
    ((r+2:ℝ)*(r+1:ℝ)/2) • Packet.symmetry (loop (T (r+2)) K)

def matchTwo (K:Layer I I) (T S:Ranked I)(r:ℕ) (p:ℕ×ℕ) : Packet I r:=
  if h:p.1+p.2=r then h ▸ ((((p.1:ℝ)+1)*((p.2:ℝ)+1)) • Packet.symmetry (knot K (T (p.1+1)) (S (p.2+1)))) else 0

def force (K:Layer I I) (T S:Ranked I) : Ranked I:=fun r=>∑ p∈Finset.antidiagonal r, matchTwo K T S r p

def carry (K:Layer I I)(T S:Orders I): Orders I:=fun e r => ∑ p∈Finset.antidiagonal e, force K (T p.1) (S p.2) r

def drift (K:Layer I I)(T S:ℕ→Orders I) (k:ℕ) : Orders I:= fun e r=>∑ p∈Finset.antidiagonal k, carry K (T p.1) (S p.2) e r

lemma forcing_earlier {K:Layer I I}(k:ℕ)(T T' S S':ℕ→Orders I)(h:∀ i≤k,T i=T' i) (hh:∀ i≤k,S i=S' i) :
    drift K T S k=drift K T' S' k:=by
 funext e r
 exact Finset.sum_congr rfl fun i hi=>by have he:= Finset.mem_antidiagonal.mp hi; rw [h _ (by omega), hh _ (by omega)]

/-- connected unmarked operations taking the logarithm of the conditional weight.
table := bit telling whether to keep field-independent output at every step. -/
def logHeat (K:Layer I I)(V:Orders I)(table : Bool) (k:ℕ) : Orders I :=Nat.strongRecOn k fun i prev=>
  match i with
  | 0 => fun e r=> if r=0 ∧ table=false then 0 else V e r
  | j+1 =>
    let W v := if h:v≤j then prev v (by omega) else 0
    fun e r=> if r=0 ∧ table=false then 0 else ((j+1:ℝ)⁻¹) • (heating K (W j e) r + ((2:ℝ)⁻¹) • drift K W W j e r)

lemma logHeat_first (K:Layer I I) (V table e r): logHeat K V table 0 e r=if r=0∧ table=false then 0 else V e r:=by
 unfold logHeat; rw [Nat.strongRecOn_eq]
lemma logHeat_next (K:Layer I I)(V table k e r):
   let W:=logHeat K V table
   W (k+1) e r= if r=0∧table=false then 0 else ((k+1:ℝ)⁻¹) • (heating K (W k e) r + ((2:ℝ)⁻¹) • drift K W W k e r):= by
 let W:=logHeat K V table
 let Z j := if j≤k then W j else 0
 have H : ∀ i≤k,Z i=W i:=fun i h=> if_pos h
 change W _ _ _= _
 conv_lhs => rw [show W (k+1)=_ from rfl]; unfold W logHeat; rw [Nat.strongRecOn_eq]
 -- reduce dependent match
 change (if _ then 0 else ((k+1:ℝ)⁻¹) • (heating K (Z k e) r+ ((2:ℝ)⁻¹) • drift K Z Z k e r))=_
 rw [H k le_rfl, forcing_earlier k Z W Z W H H]

/-- Heat equation on a tested source including the evolving denominator. -/
def markHeat (K:Layer I I)(V:ℕ→Orders I)(F:Orders I)(k:ℕ) : Orders I:=Nat.strongRecOn k fun i prev=>
 match i with
 | 0=> F
 | j+1 =>
   let W v := if h:v≤j then prev v (by omega) else 0
   fun e r=> ((j+1:ℝ)⁻¹) • (heating K (W j e) r + drift K W V j e r)
lemma markHeat_first (K:Layer I I)(V F) : markHeat K V F 0= F:=by unfold markHeat; rw [Nat.strongRecOn_eq]
lemma markHeat_next (K:Layer I I)(V F k e r) :
    let W:=markHeat K V F
    W (k+1) e r= ((k+1:ℝ)⁻¹) • (heating K (W k e) r+ drift K W V k e r):=by
 let W:=markHeat K V F
 let Z j:= if j≤k then W j else 0
 have H : ∀ i≤k,Z i=W i:=fun i h=>if_pos h
 change W _ _ _= _
 conv_lhs => unfold W markHeat; rw [Nat.strongRecOn_eq]
 change ((k+1:ℝ)⁻¹) • (heating K (Z k e) r+drift K Z V k e r)= _
 rw [H k le_rfl, forcing_earlier k Z W V V H fun _ _=> rfl]

-- stop sums at heat time one (argument n paid by bound)
def heated (n:ℕ→ℕ)(S:ℕ→Orders I): Orders I:=fun e r=>∑ i∈Finset.range (n e+1), S i e r
def ceaseHeat (K:Layer I I)(V:Orders I)(b : Bool): Orders I := heated (fun e=>3*e) (logHeat K V b)
def endHeat (m:ℕ)(K:Layer I I)(V:ℕ→Orders I)(F:Orders I): Orders I:=heated (fun e=>m+3*e) (markHeat K V F)
end YM.RegulatorIR.Diagram
