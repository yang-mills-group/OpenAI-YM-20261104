import YM.OPE.Compatible.Traces.Dispatch
set_option linter.unusedSectionVars true
/-!
# Output cashbook and mandatory commitments

Immediately after every regrouping, no virtual matching for later
regroupings required (path segments may overlap arbitrarily).
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Allot
open Function Filter Lattice RG Wilson MergeProof Source Accent Spec Ribbons
open PhysicalNext.Repeat.Legato Bandage Ribbons.ManyCopies Ribbons.ManyCopies.Stem MergeProof.Float
open Push Marker Local Extra.Histories Extra.Trajectories MeasureTheory Extra.Multi
open scoped Topology Classical BigOperators
variable {G:Gauge} {C:Family G}(A:Allot C){V I J Z :Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
    [Fintype J][DecidableEq J] [Fintype Z][DecidableEq Z](P:Ensemble V)
variable {N p i b H l:ℕ}
namespace Lights
variable {F:Fibers (I⊕Z) J}{o:I→Track C.path V p} {o':J→Track C.path V p}
    {A P} {E:Track C.path V p} {k:I→ℕ}{k' j:J→ℕ}
    (L:Lights A P N p k (i+1) b E o) {S:Lights A P N p k' i b E o'}
    {χ:Guard (Names V I)} {χ':Guard (Names V J)}
variable {Y:Config G (C.S.side (i+1) p)→Marker.Poly (Names V I)}
lemma LitUp.event (h: LitUp L χ Y)(hA:C.Makes)(hg:G.Simple)(hn:i<N)(hm:C.ref 0 < i)(hC: (C.path.levels.clock.op i p).ratio.embed ∘ E i= E (i+1))
    (M: Incoming A F o o' i H l)(D: Bind C P E F o o' i k k' j)
    (ht:∀ a,χ'.safe a→χ.safe (assembly F a)):
    ∃ S':Lights A P N p k' i b E o', S'.LitUp χ' (reunion F∘(C.path.levels.clock.op i p).push (C.path.rep N p (i+1)).beta Y) ∧ Issues L l H F S' j:=by
    have hx(x:J):k' x ≤ i:= by
       by_cases he:F.SingleFiber x
       · obtain ⟨a,-,hy,-⟩:= D.elder x he; exact hy ▸ D.fell a
       exact (D.ahead x he).1.trans (D.ahead x he).2
    obtain ⟨U,hU,hL,hY,hZ,hX⟩:= LitUp.inlet L χ χ' M h hA D.fell hn hm hC (fun x=>D.authorized x i (hx _) le_rfl) ht
    obtain ⟨S',hP,hT,hQ⟩:= commission L D U hg hA hn.le M.sizeP hm hU (Owned.known _ hY) hZ hX
    refine ⟨S',⟨hL,?_⟩,hQ⟩; rw [show S'.tips=U from funext hP]; exact Owned.inhibit _ hY (fun i=> S'.asks_pos i) hT
-- exact purchase lower limit. recursive real, all positive.
variable (V I J Z) in
-- not all needed
omit [Fintype V]
private def goods (a:I→ℝ) := ∏ i,a i
omit [Fintype V][DecidableEq V] in
lemma bill_solo {V I J Z : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype Z] [DecidableEq Z]
    {P : Ensemble V} {N p i b H l : ℕ} {F : Fibers (I ⊕ Z) J}
    {o : I → Track C.path V p} {o' : J → Track C.path V p} {E : Track C.path V p}
    {k : I → ℕ} {k' j : J → ℕ} (L : Lights A P N p k (i+1) b E o)
    {S : Lights A P N p k' i b E o'} {x:J}{a:I}(h:Issues L l H F S j)(hs:F.SingleFiber x)(ht:F.twig x=.inl a)(he:k' x=k a): S.bottom x= valve C H b l i *L.bottom a:=by
   change (S x).w _=_; rw [(h.inherited x hs a ht).2,he]; rfl
def tender (C:Family G)(H b l i:ℕ)(F:Fibers (I⊕Z) J)(k' j : J→ℕ)(w:I→ℝ)(x:J):ℝ:=
   if F.SingleFiber x then ∏ a∈F.contents x,valve C H b l i*Sum.elim w 1 a
   else Run.Below C.path (sash C i * grouped C.path (renal C.path.levels) H l i (Sum.elim (fun u=>w u / β C (i+1)^b) 1) F x/2) (j x) (k' x)
omit [Fintype V][DecidableEq V] in
lemma tender_pos (C:Family G)(A:Allot C) (F:Fibers (I⊕Z) J)(k' j:J→ℕ)(u:I→ℝ)(hK:0 < H)(hb:C.ref 0 ≤ i)(hp:∀ a,0<u a)(x:J) : 0 < tender C H b l i F k' j u x:=by
    unfold tender; split
    next h=> rw [h,Finset.prod_singleton]; refine mul_pos (valve_pos C A b l hK hb) ?_; cases F.twig x; exact hp _; exact zero_lt_one
    next h=>
       have hF(a:I⊕Z): 0 < Sum.elim (fun u' => u u'/ β C (i+1)^b) 1 a:=by
            cases a; exact div_pos (hp _) (pow_pos (β_pos ..) _); exact zero_lt_one
       have h:= grouped_pos (A:=C.path) H l F (A.arcPars hb|>.funs.1) hK hF x
       exact Run.below_fee _ (div_pos (mul_pos (sash_pos ..) h) zero_lt_two)
lemma bill {V I J Z : Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype Z] [DecidableEq Z]
    {P : Ensemble V} {N p i b H l : ℕ} {F : Fibers (I ⊕ Z) J}
    {o : I → Track C.path V p} {o' : J → Track C.path V p} {E : Track C.path V p}
    {k : I → ℕ} {k' j : J → ℕ} (L : Lights A P N p k (i+1) b E o)
    {S : Lights A P N p k' i b E o'} (h : Issues L l H F S j)(hH:0<H)(hm:C.ref 0 ≤ i)(hB:Bind C P E F o o' i k k' j)(u:I→ℝ)(hω:∀ a,0<u a)(he:u≤ L.bottom): tender C H b l i F k' j u ≤ S.bottom:=by
    intro x; have ht:= hB; unfold tender; split
    next hs=>
       obtain ⟨a,hq,hV,-⟩:= ht.elder x hs; rw [bill_solo L h hs hq hV.symm,hs,Finset.prod_singleton,hq]; exact mul_le_mul_of_nonneg_left (he _) (valve_pos _ A _ _ hH hm|>.le)
    next hs=>
       rw [h.fresh x hs]; unfold Run.Below
       apply mul_le_mul_of_nonneg_right _ (pow_nonneg (le_of_lt (div_pos (C.S.a_pos _) (C.S.a_pos _))) _)
       apply div_le_div_of_nonneg_right _ zero_le_two; apply mul_le_mul_of_nonneg_left _ (sash_pos ..|>.le)
       have h':= license_pos (A:=C.path) H l (A.arcPars hm|>.funs.1) hH
       apply Finset.prod_le_prod; intro j _; refine mul_nonneg h'.le ?_; cases j; exact (div_pos (hω _) (pow_pos (β_pos C _) _)).le; exact zero_le_one
       intro a ha; apply mul_le_mul_of_nonneg_left _ h'.le; cases a
       next a=>
           let v:= β C (i+1)^b; refine (div_le_iff₀ (pow_pos (β_pos ..) _)).2 ((he a).trans ?_)
           have hj:= hB.embers a (by rw [(F.focuses ..).1 ha]; exact hs); exact (congr_arg (L a).w hj).trans_le ((L a).guard' i hj.le i.lt_succ_self)
       next=> exact le_rfl
end Lights
end YM.OPE.Allot
