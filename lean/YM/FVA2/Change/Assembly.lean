import YM.FVA2.Change.Clock

/-!
# Multilinear change of coupling and source basis at any finite regulator

Finite physical marks, any arity. Each w an insertion from the indicated linear space of
stamps; take finite sums with scalar g-series and evaluate LPT moments. *Full* moment,
not connected. Below `convertSources` is a concrete nested finite sum with c_{w,a} of the
respective inserted fields and a full-product reader. It applies the new scale/coupling only on
the real independent Wilson coefficient system produced by the Landau `relative` / `sumBody`
calculation in `FVA2.Slice`. Thus weights outside are in the NEW coupling, not the bare Wilson
coupling.

No term rewriting of ghosts in the statement. Still finite meshes, all hypotheses pairing
these marks with analytic Landau body Prescriptions supplied explicitly. Later (e.g. `Prescription.lean`,
`Arrival/Top.lean`) apply this calculation on cover stencils. -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Change
open Function Set Filter Finset Lattice MeasureTheory
open MS MS.Koszul MS.Plane MS.Orbit Cog Orbit.LogReal MS.Swirl MS.Book Convolve Program
open MS.Puff MS.Puff.Mom MS.Puff.Engine MS.Puff.Actors
open MS.Swirl.Near MS.Native Wilsonian Slice
open FormalOPE.RG10.MultiGauge Splice
open Wick.Formal (overlay)
open scoped BigOperators Topology ContDiff
variable {G:Gauge}{n:Side}{W J A:Type}
local notation "F" => FixedMode G n
local notation "N" => Master G n true
local notation "Ω" => Ticket (Transverse G n)
local notation "p" => σbranch (G:=G) (n:=n)
local notation "M" => PermV p
local notation "Δ" => ℕ → Raw F ℂ
local infixl:70 " ★ " => overlay p
local infixl:70 " ⋅ " => Actors.core Trunk

variable {ι: W→Type}
local notation "P" => Sigma ι

-- explicit list formulation useful for repeated labels also when marks are given by integer copies
variable [LinearOrder W] [∀ w,Fintype (ι w)]
def convertSources (fees : P→Ser) : List W → (List (Sigma ι)→Ser) → Ser
  | [], read=> read []
  | w::l, read=> ∑ i : ι w, fees ⟨w,i⟩ ⋅ convertSources fees l (fun us => read (⟨w,i⟩::us))

def positions (items: Sigma ι → Ticket (Transverse G n))(l:List (Sigma ι)) := (l.map items).prod
omit [LinearOrder W] [(w : W) → Fintype (ι w)] in
lemma positions_cons (items:P→Ticket (Transverse G n)) (w:W)(i : ι w)(l:List (Sigma ι)) : positions items (⟨w,i⟩::l) = items ⟨w,i⟩ * positions items l:=rfl

variable (t:Team) (x:ℝ)
local notation "κ" => Program.shift t x
local notation "Y" => NRG (Stripped t) x n G true

-- source recipes
abbrev mixed (s: Team)(x:ℝ)(fees:P→Ser)(v : P→ Wick.Formal.Table F) (w:W) :=
    ∑ i:ι w, scale (Raw _ ℂ) (fees ⟨w,i⟩) (substitute (shift s x) (v ⟨w,i⟩))

def pack (f:W→Wick.Formal.Table F) : List W → Wick.Formal.Table F
    | []=> (M).unit
    | w::u=> (f w) ★ pack f u
variable [Fintype A][DecidableEq A][Fintype J][DecidableEq J]
variable (a:Axes G n A J)(μ : Measure (Transverse G n))[Measure.IsAddHaarMeasure μ]
variable {v: Sigma ι→ Wick.Formal.Table (FixedMode G n)}
variable (fees: Sigma ι → Ser) (X: Sigma ι→ Ticket (Transverse G n))
local notation "H" => (mixed t x fees v)
local notation "C" => (Wick.Boson.bills (J:=J) a.X)
local notation "Φ" => substitute («P»:=Raw (FixedMode G n) ℂ) κ
local notation "λₛ" => substitute («P»:=ℂ) κ
local notation "Ψ" => promote (Wick.pull a.R)

variable (hz:∀ i,v i∈ Wick.Formal.OK σbranch)
variable (hb:∀ i,promote (Wick.pull a.R) (v i) = Wick.Boson.bills (J:=J) a.X (X i))
include hz hb
omit [LinearOrder W] in
lemma mul_oil (l : List W) (u:Wick.Formal.Table (FixedMode G n))(P' : Ticket (Transverse G n))(hp:u∈Wick.Formal.OK p)(hy:Ψ u=C P') :
    Endμ N p Y (Φ u ★ pack H l) (convertSources fees l (fun s=> λₛ (record (a.sumBody μ (P' * positions X s))))) := by
  induction l generalizing u P' with
  | nil=>
    rw [convertSources, show Φ u ★ pack H []= Φ u from (M).identityR _, show positions X []=1 from rfl,mul_one]; exact end_clock _ _ (a.End_sumBody μ u _ hp hy)
  | cons i l ih =>
    have h (j:ι i) := ih (u ★ v ⟨i,j⟩) (P' * X ⟨i,j⟩) ( Wick.Formal.overlay_ok hp (hz _) ) (by
      rw [Wick.Boson.tab_mul, ← hy, ← hb]; funext k; simp only [Wick.Formal.coeff_prod,promised,map_sum]; exact Finset.sum_congr rfl fun _ _=> Wick.pull_product a.tieR _ _)
    let U:=Φ u; let Q(j:ι i) := v ⟨i,j⟩; let R':=pack H l
    rw [pack, ← Wick.Formal.assoc, convertSources]
    change Endμ N p Y ((U ★ ∑ j:ι i, scale (Raw F ℂ) (fees ⟨i,j⟩) (Φ (Q j))) ★ R') _
    rw [map_sum,map_sum,LinearMap.sum_apply]; apply End_tab_sum; intro j _
    rw [scale_slot_r, scale_slot, ← show Φ (u ★ Q j)= U ★ Φ (Q j) from sub_core κ p u (Q j) (Program.share ..)];
    apply End_scale p N; convert h j using 1; congr! 3; funext l; rw [positions_cons, mul_assoc]

omit [LinearOrder W] in
lemma ami (l:List W) : Endμ N p Y (pack H l)
    (convertSources fees l (fun s=> λₛ (record (a.sumBody μ (positions X s))))) := by
  obtain h:= mul_oil t x a μ fees X hz hb l (M).unit 1 (show Wick.Formal.tab (coin (A:=F) (1:ℂ))∈ Wick.Formal.OK p from Wick.Formal.tab_good (Swirl.feeUnit («p»:=p))) (by rw [Wick.Formal.tab_unit,Wick.Formal.promote_tab, Wick.pull_coin, Wick.Boson.tab_one]; rfl)
  rw [(sub_tether κ (Program.share ..) p).unit,(show (M).unit ★ pack H l= _ from (( M ).identityK _))] at h
  simpa only [one_mul] using h

variable {z: W→Actor G}{q:Cover}{d:W→Cover}
variable (hQ:∀ i,promote (Mark_T G n q (d i)) (z i x) = mixed t x fees v i)
include hQ
variable (hZ:∀ i,v i∈ Wick.Formal.even σbranch)
omit μ [Measure.IsAddHaarMeasure μ] hz hb in
lemma market (hZ:∀ i,v i∈ Wick.Formal.even p)(l:List W)(he:l.Nodup) :
    Font p (Marks z x n q d) l.toFinset=pack H l := by
  let V:= Marks z x n q d; let P₁:= Puff.SplitP.marked W
  have hs (u:W) : V {u}=H u := Eq.trans (mark_me (V:=z) x n q d u) (hQ u)
  have ho (i : Finset W)(h:i.card≠1) : V i=0:= mark_off h ..
  have heven(s:Finset W): V s∈(M).guard:= by
    by_cases hp:s.card=1; swap; · rw [ho s hp]; exact (M).guard.zero_mem
    obtain ⟨i,rfl⟩:=Finset.card_eq_one.mp hp; rw [hs]; exact (M).guard.sum_mem fun j _=> scale_module (Center p) (sub_module _ (Center p) (hZ _))
  induction l with
  | nil=> exact Stencil.simple_E (M) _ P₁ (ho ∅ (by simp))
  | cons i l ih=>
    rw [List.toFinset_cons]; change (M).Cheer P₁ V (insert i l.toFinset)=_; rw [Stencil.cheers M heven ho, hs]; rw [show (M).Cheer P₁ V l.toFinset=_ from ih (List.nodup_cons.mp he).2]; rfl
    simpa using (List.nodup_cons.mp he).1

include hZ
lemma evaluated (s:Finset W) : Fleet.PhysicalSum G t x n true s d q z
   (convertSources fees s.toList (fun l=> λₛ (record (a.sumBody μ (positions X l))))) := by
    unfold Fleet.PhysicalSum;
    rw (occs:=.pos [1]) [← Finset.toList_toFinset s]
    rw [market t x fees hQ hZ s.toList s.nodup_toList]; exact ami t x a μ fees X hz hb _
end YM.FVA2.Change
