import YM.RegulatorIR.Primitives.Hear

/-!
# Primitive packer from local Taylor charts to folded rotor

Build rooted interaction jets (positive coupling powers with rank≥one; gauge
will handle exact lowest rank) BEFORE Wilson Wick contractions. Untruncated
finite support tensors at each degree. Fold symmetry from uniqueness using
actual Ward equivariance at local patch germs. Output folds commute with root
orbit sum for positive-degree primitives (not graphs). -/
set_option autoImplicit false
noncomputable section
namespace YM.RegulatorIR.Prim
open Function Budget Budget.Layer Budget.Packet Budget.Deck Budget.Tuple Motion Set Filter Binding Diagram.Formal PertExtension Series Series.Radial Series.Tested MeasureTheory MvPolynomial Cluster Diagram Quadratic
open scoped Topology ENNReal BigOperators Classical PowerSeries ContDiff
variable {I J X Y:Type}{k a b r e:ℕ}
variable {P:ℝ}
-- root-local logs. $t_0$ explicit common coupling, scaled as (t,t A)
abbrev Micro (I:Type):= ℝ → (I→ℝ) → ℝ
def flank (F:Micro I)(x:I→ℝ)(t:ℝ):= F t (t • x)
/-- factor some finite coordinates without wrap. global chart may be measurable
extension in physical regulator calculation. -/
structure Run (F:Micro I) where
 J: Type
 fin : Fintype J
 inc : J↪I
 script : ℝ × (J→ℝ)→ℝ
 smooth : letI : Fintype J:=fin; ContDiffAt ℝ ∞ script 0
 reaches (t) x : F t x= script (t,x ∘ inc)
attribute [instance] Run.fin

variable {F G:Micro I}
namespace Run
variable (M: Run F)
lemma flank_v (x:I→ℝ) : tale (flank F x)= inscription M.script (1,x ∘ M.inc):=by
 rw [← lore M.smooth,show flank F x= fun t:ℝ=> M.script (t • (1,x ∘ M.inc)) from ?_]
 ext1 t; rw [flank,M.reaches]; apply congr_arg;exact Prod.ext (by simp) rfl
include M
lemma smooth_v (x:I→ℝ) : ContDiffAt ℝ ∞ (flank F x) 0:=by
 rw [show flank F x= fun t:ℝ=> M.script (t • (1,x ∘ M.inc)) from funext fun t=> (M.reaches t (t • x)).trans (congr_arg _ (show (t,(t • x) ∘ M.inc)= t • (1,x ∘ M.inc) from Prod.ext (by simp) rfl))]
 exact ContDiffAt.comp (f:=fun t:ℝ=> t • ((1:ℝ),x ∘ M.inc)) _ (show ContDiffAt ℝ ∞ M.script ((0:ℝ) • (1,x ∘ M.inc)) from by rw [zero_smul]; exact M.smooth) (contDiffAt_id.smul contDiffAt_const)
end Run

-- all-degree positive shifted primitive packets. exponent count distinct per root:
-- Haar multiplied at step t^0, Wilson cost t^-2. factor folded into C.
structure Lab (a:ℕ)(c:ℝ)(F:Micro I)(T:Orders I):Prop where
 figures x {i:ℕ} (h:0 < i) : drums (T i) (i+a) x=c*PowerSeries.coeff (i+a) (tale (flank F x))
 smooth : gradedSymmetric T
 scope_ : ∀ i,Within (i+a) (T i)
 sized : ∀ i r,Bounded (T i r)
 awake : T 0=0
namespace Run
variable (M:Run F) (c:ℝ)(a:ℕ)

-- existence and uniqueness mean any such prescription identifies the genuine kernels.
include M
lemma issues : ∃ T:Orders I,Lab a c F T:=by
 choose S hs hw hr using fun i:ℕ=> Mold.tilt (mold_jet M.script (i+a)) c
 let T(i:ℕ): Ranked I:= if i=0 then 0 else fun r=> offer M.inc (S i r)
 refine ⟨T,fun x i hi=>?_,fun i j=>?_,fun i=>?_,fun i r=>?_,if_pos rfl⟩
 · unfold T; rw [if_neg hi.ne', M.flank_v, inscription, PowerSeries.coeff_mk, flute]; exact (hr i _).symm
 · unfold T; split <;> first|exact Diagram.symmetric_zero|exact offer_symm _ _ (hs i j)
 · unfold T; split
   · intro r h; contradiction
   intro r h; apply hw i r; intro he; apply h; dsimp only; rw [he]; ext x;simp [offer,Stalk.collect]
 unfold T;split
 · exact Set.finite_empty.subset (fun i h=> (h rfl).elim)
 exact bound_offer ..
end Run

namespace Lab
variable {c:ℝ} {T U:Orders I}
lemma unique (h:Lab a c F T) (he:Lab a c F U) : T=U:=by
 ext1 i; cases Nat.eq_zero_or_pos i with
 | inl hi=> rw [hi,h.awake,he.awake]
 | inr hi=> exact guessed (h.scope_ i) (he.scope_ i) (h.smooth i) (he.smooth i) fun _=> by rw [h.figures _ hi, he.figures _ hi]
lemma no_altar (h:Lab a c F T)(H:∀ s,F s 0=0)(i:ℕ): T i 0=0:=by
 funext x; cases Nat.eq_zero_or_pos i with
 | inl hi=> rw [hi,h.awake];rfl
 | inr hi=> have hp:= h.figures 0 hi; rw [starts,show flank F 0=fun _=>0 by ext;simp [flank,H], tale_const,map_zero,map_zero,mul_zero] at hp; rw [Subsingleton.elim x Fin.elim0];exact hp
lemma form (h:Lab a c F T)(ht:a≤2):Vacuum T:=by
 intro i j hi; have hv:= h.scope_ i j hi; cases Nat.eq_zero_or_pos i with
 | inl t=> rw [t,h.awake] at hi; contradiction
 | inr t=> exact ⟨t,by omega⟩
end Lab

-- different valuations per primitive. lump nonlinear coefficients.
variable {A:Deck P I J}{B:Parade X Y}
-- all such F individually transforms, C and exponent follow motions

def toolP (A:Deck P I J)(d:Motion)(v:I→ℝ):=fun i:I=> d.sign*v ((A.wind d).symm i)
def Offset (A:Deck P I J)(B:Parade X Y)(F:X→ Micro I):Prop:=∀ d x t w,F (B.rips d x) t (toolP A d w)=F x t w
lemma tools {F:X→Micro I}(h:Offset A B F)(d x w): tale (flank (F (B.rips d x)) (toolP A d w))= tale (flank (F x) w):=by
 apply congr_arg;ext t; unfold flank; rw [show t • toolP A d w=toolP A d (t • w) from ?_,h d x]
 ext1 i; change t*(d.sign*_)=d.sign*(t*_); ring

section Flight
variable (F:X→Micro I) (T:X→ Orders I) (a:X→ℕ) (c:X→ℝ)
structure Flight (A:Deck P I J)(B:Parade X Y) : Prop where
 tier : Offset A B F
 value : ∀ u, Lab (a u) (c u) (F u) (T u)
 night : ∀ u,a u ≤2
 grade d v : a (B.rips d v)=a v
 cost d v : c (B.rips d v)=c v
 hollow : ∀ u t,F u t 0=0
namespace Flight
variable {F T a c}
variable (V : Flight F T a c A B)
include V
lemma paves (e i): Rot A B (fun x=>T x e i):=by
 cases Nat.eq_zero_or_pos e with
 | inl he=> subst e; intro d u x; simp only [(V.value _).awake]; simp only [dyed,Pi.zero_apply,zero_mul]
 | inr hg=>
    intro d u x
    let Q:=T (B.rips d u) e
    let τ (r:ℕ) := d.sign^r • (fun w: Tuple I r=>Q r (A.wind d∘ w))
    have hW: Within (e+a u) τ:=by
       intro r h; rw [← V.grade d u]
       apply (V.value _).scope_ e r;intro hp;apply h; ext1 w; simp [τ,Q,hp]
    have he' : τ=T u e:=by
       apply guessed hW ((V.value _).scope_ e) _ ((V.value u).smooth e)
       · intro v
         have he:= tools V.tier d u v
         have hh:= (V.value (B.rips d u)).figures (toolP A d v) hg
         rw [V.grade, he,V.cost,← (V.value u).figures v hg] at hh
         rw [←hh]; apply Finset.sum_congr rfl; intro j _; unfold τ; rw [strum_tilt]
         let U(j:ℕ)(w:Tuple I j):= Q j (A.wind d∘ w)
         change _=strum (Q j) _; rw [strum_perm (toolP A d v) (A.wind d) (Q j)]; change _= strum (U j) (toolP A d v∘ A.wind d)
         rw [show toolP A d v ∘ A.wind d= d.sign • v from funext (fun i=> by simp only [Function.comp_apply,toolP,Equiv.symm_apply_apply];rfl), strum_v]
       intro j; apply symmetric_scale; intro p x; exact (V.value _).smooth e j p (A.wind d∘ x)
    let z:=A.wind d∘ x; let s:=d.sign^i
    have hp:s*Q i z=T u e i x:= congr_fun (congr_fun he' i) x
    change Q i z * A.polish (A.wind d∘ x)= _; rw [A.polish_mov]; unfold dyed; unfold z s at hp; dsimp only; rw [← hp]; change _ = d.sign^i * Q i z * _; ring -- RHS unfold z mismatch
end Flight

def many (T:X→Orders I):Orders I:=fun i r=> massive (fun z=>T z i r)
namespace Flight
open PowerSeries
variable {F T a c} (V:Flight F T a c A B)
include V
lemma grammar:Vacuum (many T):=by
 intro e r he; have h : ∃ x,T x e r ≠0:=by
    by_contra! hp;apply he; unfold many massive; simp_rw [hp]; ext;simp
 obtain ⟨x,hx⟩:=h;exact (V.value x).form (V.night _) e r hx
lemma symm : gradedSymmetric (many T):=fun i j=> mass_sym fun x=>(V.value x).smooth i j
lemma novel (e r): A.Ready (many T e r):= mass_rot (V.paves e r)
def foldO (A:Deck P I J)(T:X→Orders I) : Orders J:= fun i r=>A.deckSum (many T i r)
lemma format : Vacuum (foldO A T):=by intro i r hi; apply V.grammar i r;intro he;apply hi;unfold foldO; rw [he]; ext1 z; unfold deckSum;split <;> simp [lodge,dyed]
lemma printed : gradedSymmetric (foldO A T):=by
 intro i j k w; apply Eq.trans (A.deck_perm _ k (V.novel _ _) w).symm; rw [show many T i j ∘ Budget.Tuple.perm I k=many T i j from funext (V.symm i j k)]; rfl
-- on output sums
variable [Fintype Y][Fintype J]
omit [Fintype J] in
lemma sprint e : foldO A T e=∑ u:Y, fun r=> A.scroll (T (B.bare u) e r):=by
 ext1 r; rw [Finset.sum_apply]; ext1 x; rw [Finset.sum_apply]; by_cases hr:r=0
 · subst r
   have hp v : A.scroll (T v e 0) x=0:= by rw [(V.value v).no_altar (V.hollow v)]; simp [scroll,Stalk.collect,dyed]
   simp_rw [hp]; simp [foldO, Deck.deckSum]
 exact rooting (V.paves _ _) (fun v=>bound_cost ((V.value v).sized _ _)) x ⟨0,Nat.pos_iff_ne_zero.mpr hr⟩
omit [Fintype Y] in
lemma heritage (u:Y)(w:J→ℝ){e:ℕ}(he:0<e):
 let p:=B.bare u; MvPolynomial.eval w (packed (fun r=> A.scroll (T p e r)) (e+2))= c p*PowerSeries.coeff (e+a p) (tale (flank (F p) (bridge A w))):=by
 intro p; let Q:= V.value p
 have hx: e+a p≤ e+2:= add_le_add_right (V.night p) e
 have hh: Within (e+a p) (fun r=>A.scroll (T p e r)):=by intro r h; apply Q.scope_ e r; intro hz; apply h; dsimp only; rw [hz]; ext1 x; simp [scroll,Stalk.collect,dyed]
 rw [← pack_extends hh hx, high_ink w A _ (Q.sized e)]; exact Q.figures _ he
lemma transit (w:J→ℝ){e:ℕ}(h:0<e): PowerSeries.coeff e (flavor 2 w (foldO A T)) = ∑ v:Y, let p:= B.bare v; c p*PowerSeries.coeff (e+a p) (tale (flank (F p) (bridge A w))) := by
 rw [flavor_lo,V.sprint e, Diagram.pack_sum,map_sum]; apply Finset.sum_congr rfl; intro u _; exact V.heritage _ _ h
omit [Fintype Y] in
lemma zero_transit (w:J→ℝ) : PowerSeries.coeff 0 (flavor 2 w (foldO A T))=0:= flavor_dark _ (vacuum_lo _ V.format) _
end Flight
end Flight
end YM.RegulatorIR.Prim
