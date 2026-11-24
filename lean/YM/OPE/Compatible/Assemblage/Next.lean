import YM.OPE.Compatible.Assemblage.Walking
/-! Track purchased capacities through a step with no group. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float Stem
open scoped Topology BigOperators Classical
variable {V I J : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I][Fintype J][DecidableEq J]{G:Gauge}{n:Side}
    {A:History G}{N p i : ℕ} {W W':I→ℝ}{C:I→ℂ}{R:Rep G n}{t e d u φ : ℝ}{b:ℕ→ℕ}
variable (P:Ensemble V)
structure Owned (χ:Guard (Names V I)) (R:Rep G n)(E:V→Site n) (P:Ensemble V)(X:I→Stem V G n)(w:I→ℝ)(d:ℝ)
    (Q:Config G n→ Poly (Names V I)): Prop where
   issues : ∃ Z:Config G n→ Poly (Names V I), Integrable Z (prior G _) ∧ χ.Filtered Q Z ∧ Owns R E P X w d Z
namespace Owned
variable {P} (χ:Guard (Names V I)) {E:V→Site n}{X:I→Stem V G n}{w:I→ℝ} {Q:Config G n→ Poly (Names V I)}
lemma known (h: Owned χ R E P X w d Q)(j:I): Marked R E P (X j):= by obtain ⟨X,-,-,hx⟩:=h.issues; exact hx.earned j
lemma budgets (h:Owned χ R E P X w d Q)(i:I):0<w i:=by obtain ⟨X,-,-,hx⟩:=h.issues; exact hx.way _
lemma inhibit {w':I→ℝ}(h:Owned χ R E P X w d Q)(hv:∀ i,0<w' i)(ht:w'≤ w): Owned χ R E P X w' d Q:=by
    obtain ⟨X,a,b,p⟩:=h.issues; exact ⟨X,a,b,p.scaleSlot hv ht⟩
end Owned
section
variable (χ:Guard (Names V I)) {E:V→ Site (A.S.side i p)}{X:I→ Stem V G (A.S.side (i+1) p)}{X':I→Stem V G (A.S.side i p)}{Y:Config G (A.S.side (i+1) p)→Poly (Names V I)}
    {D:GaugeDoor (A.rep N p (i+1)) (A.rep N p i)}
variable (hY:Owned χ (A.rep N p (i+1)) (fun v=>(A.levels.clock.op i p).ratio.embed (E v)) P X W e Y)
    (hl: Integrable Y (prior G _))(hA:A.Selected)(hn:i<N)(hr:Admits D b d t u)
    (he:(A.levels.budget (i+1)).supportExponent-4 ≤ e)
    (hp:∀ j,Marked (A.rep N p i) E P (X' j))(hf:∀ j,Journey D (A.levels.clock.op i p) P (X j) (X' j) (W j) (C j))
    (hV:Occupancy (tags X) (b i))(hV':Occupancy (tags X') (b i))
include hY hp hf hr hV hV' he hn hA hl
local notation "op" => A.levels.clock.op i p
local notation "mon" => A.levels.budget i
local notation "old" => A.rep N p (i+1)
-- avoid use inside independent variable headers
set_option maxHeartbeats 200000 in
lemma refill (hχ: χ.Chordal P.v P.perms)(hw:∀ i,0<W' i)(hW:χ.Gates (tags X') (A.levels.budget i).B (quota V (dropFunds d W)) (quota V W') 1) : Owned χ (A.rep N p i) E P X' W' ((A.levels.budget i).supportExponent-3) ((A.levels.clock.op i p).push (A.rep N p (i+1)).beta Y):=by
   obtain ⟨Y',hy,hx,h⟩:=hY.issues
   obtain ⟨ha,hz⟩:= spring_step P h hy hA hn hr he hp hf hV hV'
   let f:=(A.levels.clock.op i p).push (A.rep N p (i+1)).beta
     (fun U=>Y' U)
   let r':= quota V (dropFunds d W); let σ:= (A.levels.budget i).supportExponent
   have hH := hA.represents N p i hn.le; have hC : Repegs (tags X') (A.levels.budget i).B r' r' (1/2) 1 (Names V I):=by
      intro x hx y hh; rw [one_mul]; refine le_mul_of_one_le_right (Poly.worth (w:=r') (fun i=> mul_pos hr.staff.hats.1 (h.way i.snd)) x|>.le) (Real.one_le_exp (by positivity))
   have hC' := hC; rw [← hH.vac] at hC'
   have hk j: Dominated (color X' j):= (hp j.2).spends j.1
   have hb U: (A.rep N p i).eval U≠0:= (Tour.bright A hA N p i hn.le U).ne'
   have he'r(j): 0 < r' j := mul_pos hr.staff.hats.1 (h.way j.2)
   obtain ⟨h1,h2⟩:= kindly ha hH.good.labels hb hk hz
   have hσ:=hr.staff.exp.1
   have hm : Serves (A.rep N p i) (lights X') (ink X' (A.rep N p i)) f P.v P.move E P.perms (tags X') r' σ 1:=
      thru ha hH.good.labels he'r hr.staff.hats.1.le hV' (by linarith only [hσ]) (by rw [hH.vac]; exact hr.staff.stakes.1.trans_eq (by ring)) he'r hC' zero_le_one (by simp) (by rw [hH.vac,one_mul]; exact hr.staff.stakes.2) hz hk hb
   have hρ:= χ.brought (T:=A.levels.clock.op i p) hx hl hy (A.levels.transition_mass i p (A.rep N p (i+1)).beta)
   have hu: Repegs (tags X') (A.rep N p i).p.B r' r' 0 1 (Names V I):=by simp [Repegs]
   obtain ⟨κ,hκ,hκ',hz'⟩:= χ.memorial (hm.prune he'r he'r hu zero_le_one (show σ-3+1+0≤σ by linarith only) (le_of_eq (one_mul _))) hχ hH.good h1 h2 he'r (fun i=>hw i.2) (hH.vac.symm ▸ hW)
   exact ⟨κ,hκ,fun U j hj=> (hρ U j hj).trans (hκ' U j hj),hp,hw,hz'⟩
end
end YM.MergeProof.Ribbons.ManyCopies
