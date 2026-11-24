import YM.OPE.Compatible.Assemblage.Width
/-!
# One seam propagation with separately named continuations

Assembly before the refill or grouping. Only the `Stem`s need be
prepared/marched/reassigned by the construction, these lemmas pay for
moving all sectors together at the Arsensal step. Remember *actual few*
 
copy permissions separately: use with even repeatedly folded partial
moments via `Dispatch`. Exact spiller accounting even when the marker
paths later involve differences with primary columns.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars true
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I J : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]{G:Gauge}{n n':Side}
    {A:History G}{N p i : ℕ} {R:Rep G n}{R':Rep G n'}{m d e c a t u φ χ w : ℝ} -- remove
structure Ensemble (V:Type) where
   v:V
   move : V→Motion
   perms : V→Equiv.Perm V
   to_ref i : perms i v=i
   spring : move v=(1,false)
variable (P:Ensemble V)
def Ensemble.echo (a:ℂ) (i:V):= scalar (P.move i) a
lemma Ensemble.origin {V:Type} [Fintype V] [DecidableEq V] (P:Ensemble V) (z:ℂ): P.echo z P.v=z:=by unfold Ensemble.echo; rw [P.spring]; rfl
lemma Ensemble.price {V:Type} [Fintype V] [DecidableEq V] (P:Ensemble V) (z:ℂ) (j:V): ‖P.echo z j‖=‖z‖:=by unfold echo Motion.scalar;split <;> simp
structure Stem (V:Type)(G:Gauge)(n:Side) where
   home: V→Site n
   oil: V→ Config G n→ℂ
   gas: V→ℕ→ Config G n→ℂ
namespace Stem
variable (M:Stem V G n)(X:I→Stem V G n)
def tags (i:V×I) := (X i.2).home i.1
def lights (i:V×I) := (X i.2).oil i.1
def color (i:V×I) := (X i.2).gas i.1
def ink (R:Rep G n)(i:V×I) : Res G n:= profile R.activities (color X i)
def sub (R:Rep G n)(i:V)(U:Config G n):= coin R (M.oil i) (M.gas i) U
def quota (_V:Type) (W:I→ℝ) (i:_V×I):= W i.2
def spices (P:Ensemble V)(z:I→ℂ) (i:V×I):=P.echo (z i.2) i.1
structure Marked (R:Rep G n) (E:V→Site n) (P:Ensemble V) (X:Stem V G n) : Prop where
   sym i:i≠P.v→X.home i=affine (P.move i).1 (E i) (X.home P.v)
   shine i:i≠P.v→X.oil i=stepUp (P.move i) (E i) (X.oil P.v) ∧
      profile R.activities (X.gas i)=floatUp (P.move i) (E i) (profile R.activities (X.gas P.v))
   spends i:Dominated (X.gas i)
lemma linked {V I:Type} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    {G:Gauge} {n:Side} {R:Rep G n} (P:Ensemble V) (X:I→Stem V G n) {E:V→Site n} (h:∀ i,Marked R E P (X i)) (z:I→ℂ) : May P.v P.move E P.perms (lights X) (ink X R) (spices P z):=by
   intro i hi; refine ⟨P.to_ref i, fun j=> ⟨((h j).shine _ hi).1,((h j).shine _ hi).2,?_⟩⟩
   simp_rw [spices]; rw [P.origin]; rfl
variable {Y:Config G n→Poly (Names V I)}{E:V→Site n}{W W':I→ℝ} (χ:Guard (Names V I))
-- typ Core contains the extension but just existential in consumers.
structure Owns (R:Rep G n)(E:V→Site n)(P:Ensemble V)(X:I→ Stem V G n)(w:I→ℝ)(d:ℝ)
    (Q:Config G n→ Poly (Names V I)): Prop where
   earned : ∀ i,Marked R E P (X i)
   way : ∀ i,0< w i
   ship : Serves R (lights X) (ink X R) Q P.v P.move E P.perms (tags X) (quota V w) d 1
variable {P X}
lemma Owns.scaleSlot (h:Owns R E P X W e Y) (hv:∀ i,0<W' i)(ht:W'≤ W): Owns R E P X W' e Y:=by
   refine ⟨h.earned,hv,?_⟩
   exact h.ship.prune (fun i=>h.way i.snd) (fun i=>hv i.snd) (slighter (fun i=>h.way i.snd) (fun i=>hv i.snd) (w:=1) (fun i=>(ht i.snd).trans_eq (one_mul _|>.symm)) zero_le_one le_rfl) (le_rfl.trans zero_le_one) (le_of_eq (add_zero _)) (by norm_num)
variable {D:GaugeDoor R R'}{S:StepData n' n} (X': I→Stem V G n')
structure Journey (D:GaugeDoor R R') (S:StepData n' n)(P:Ensemble V) (X:Stem V G n) (X':Stem V G n') (w:ℝ) (c:ℂ):Prop where
   site : S.ratio.parent ∘ X.home=X'.home
   keeps j : X'.sub R' j=S.push R.beta (X.sub R j)
   permits : ∃ p:Set Wing, p.Finite∧ ∃ s t:ℝ, 2*w*s≤1∧ w*t≤1 ∧
     Tale p (X.home P.v) (X'.home P.v) 1 (X.oil P.v) (profile R.activities (X.gas P.v)) (profile R'.activities (X'.gas P.v)) c s t D
   carries : w*‖c‖≤1 -- enough for the grouping at output.
-- shrink J for slots waiting catch. T/s sign from Story? use mul inequality cases.
lemma Journey.cheaper {V:Type} [Fintype V] [DecidableEq V] {G:Gauge} {n n':Side}
    {R:Rep G n} {R':Rep G n'} {c t w:ℝ} {P:Ensemble V} {D:GaugeDoor R R'}
    {S:StepData n' n} {X:Stem V G n} {X':Stem V G n'} (h:Journey D S P X X' w c)(he:t≤w)(hδ:0<t): Journey D S P X X' t c:=by
    refine ⟨h.site,h.keeps,?_,(mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans h.carries⟩
    obtain ⟨p,hp,s,u,hX,hU,hY⟩:= h.permits; refine ⟨p,hp,s,u,?_,?_,hY⟩
    · by_cases hh:0 ≤ s
      · exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he zero_le_two) hh).trans hX
      exact le_trans (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg zero_le_two hδ.le) (le_of_not_ge hh)) zero_le_one
    by_cases hh:0≤ u; · exact (mul_le_mul_of_nonneg_right he hh).trans hU
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos hδ.le (le_of_not_ge hh)) zero_le_one
end Stem
open Stem
variable {r:ℕ→ℕ}{ρ: ℕ}
variable {D:GaugeDoor (A.rep N p (i+1)) (A.rep N p i)}
set_option quotPrecheck false
local notation "O"=> A.levels.clock.op i p
local notation "R"=> A.rep N p i -- replace naming shadow
local notation "R1"=> A.rep N p (i+1)
local notation "Y'" => A.levels.budget
local notation "Θ"=> A.S.side (i+1) p
local notation "Z"=> A.S.side i p
structure Admits {G:Gauge} {A:History G}{N p i:ℕ} (D:GaugeDoor (A.rep N p (i+1)) (A.rep N p i)) (r:ℕ→ℕ)(d t u : ℝ):Prop where
   staff : Duty A r i d t u
   range' : Volant (A.levels.clock.op i p) D (r i) ((A.levels.budget (i+1)).supportExponent-4) t ((A.levels.budget i).supportExponent+1/2) ((A.levels.budget i).supportExponent+1) 1 u
   unite : Unites (A.levels.clock.op i p) D (r i) ((A.levels.budget (i+1)).supportExponent-4) t ((A.levels.budget i).supportExponent+1/2) ((A.levels.budget i).supportExponent+1) 1 u
variable {E:V→ Site (A.S.side i p)}{X:I→ Stem V G (A.S.side (i+1) p)}{X':I→Stem V G (A.S.side i p)}{W W':I→ℝ}{C:I→ℂ}{Y:Config G (A.S.side (i+1) p)→Poly (Names V I)}
def dropFunds (d:ℝ)(W:I→ℝ)(i:I):= d*W i
variable (hY:Owns (A.rep N p (i+1)) (fun j=>(A.levels.clock.op i p).ratio.embed (E j)) P X W e Y)
   (hI: Integrable Y (prior G _))(hA:A.Selected)(hn:i<N)(hr:Admits D r d t u)
   (he: (A.levels.budget (i+1)).supportExponent-4≤e)(hp:∀ j,Marked (A.rep N p i) E P (X' j)) -- adjust
local notation "Y*" => (O).push (R1).beta Y
variable (hf:∀ j,Journey D (A.levels.clock.op i p) P (X j) (X' j) (W j) (C j))
   (hV:Occupancy (tags X) (r i))(hV':Occupancy (tags X') (r i))
include hY hI hA hn hr hp hf hV hV' he
set_option maxHeartbeats 200000 in
lemma spring_step : Arc (R) (lights X') (color X') (Y*) P.v P.move E P.perms (tags X') (quota V (dropFunds d W)) ((Y' i).supportExponent+1/2) ((Y' i).supportExponent+1) 1 u d (spices P C)∧ ∀ j U, ((Y*) U).part ((Names V I).fire j)=coin (R) (lights X' j) (color X' j) U:=by
    have hew := hA.represents N p (i+1) hn; have hj:= hA.represents N p i hn.le
    have hl:=linked P X hY.earned C; have hl':=linked P X' hp C
    have hE: (O).ratio.parent ∘ tags X=tags X':= funext fun i=> congr_fun (hf i.2).site i.1
    constructor
    · choose b hb s κ hb' hK hS using fun i=> (hf i).permits
      have hc: chimes P.v P.move E P.perms (tags X) ((O).ratio.parent ∘ tags X) (lights X) (fun j=>profile (R1).activities (color X j)) (fun j=>profile (R).activities (color X' j)) (spices P C) O:=
         chimes_parent A (o:=tags X) (L:=color X) (fun i hi j=> (hY.earned j).sym _ hi) hl (fun i hi j=> ((hl' i hi).2 j).2.1)
      have ha(j:I): let x:V×I:=(P.v,j); ∃ p':Set Wing,p'.Finite ∧ Tale p' (tags X x) (((O).ratio.parent ∘ tags X) x) 1 (lights X x) (ink X (R1) x) (profile (R).activities (color X' x)) (spices P C x) (s j) (κ j) D:=by
         intro v; rw [hE,spices]; change ∃ p', _ ∧ Tale _ _ _ _ _ _ _ (P.echo (C j) P.v) (s j) (κ j) _; rw [P.origin]; exact ⟨b j,hb j,hS j⟩
      rw [← hE]; refine freshArc A N i p r hA hn hr.staff hr.range' hr.unite (θ:=Y) (P:=P.move) (v:=P.v) (E:=E) (B:=P.perms)
         (w:=e) (δ:=spices P C) (I:=quota V W) (D:=D) (F:=lights X) (F':=lights X') (L:=ink X (R1)) (L':=color X') (o:=tags X) (fun i=>hY.way i.2) ?_ he hV (hE.symm ▸ hV') (fun _ _ _=>rfl) (s:=s) (r:=κ) (fun j=> hb' j.2) (fun j=> hK j.2) ha hc (fun i=> hew.good.labels.moves _ _)
      exact hY.ship
    rintro ⟨j,x⟩ U; let M:= (Names V I).fire (j,x)
    have he: (fun U=> (Y U).part M)= (X x).sub (R1) j:= funext fun U=>Served.relay (J:=Names V I) («R»:=R1) (g:=color X) (hY.ship.sold) (fun i=>(hY.earned i.2).spends i.1) hew.good.labels U|>.1 (j,x) -- adjust
    have hvc:(fun U=> (((O).push (R1).beta Y U).part M)) = (O).push (R1).beta (fun U=>(Y U).part M):= push_get (Ss:=O) (A.levels.transition_mass i p (R1).beta) hI M
    rw [he,← (hf x).keeps j] at hvc
    exact congr_fun hvc U

end YM.MergeProof.Ribbons.ManyCopies
