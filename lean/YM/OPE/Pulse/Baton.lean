import YM.OPE.Pulse.Lamp
/-!
# Hand over the full array at the event
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Patrol
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I J T : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
  [Fintype J][DecidableEq J]{G:Gauge}{n:Side}
variable {A:History G}{N p k i j:ℕ}
    {δ φ σ χ:ℕ→ℝ}{r:ℕ→ℕ}{D:∀ N p m:ℕ,m<N→GaugeDoor (A.rep N p (m+1)) (A.rep N p m)}
set_option quotPrecheck false
local notation "R" => A.rep N p
local notation "f" => A.S.side (i+1) p
local notation "c" => A.S.side i p
local notation "a" => (R i)
local notation "A*" => (R (i+1))
local notation "Z" => (A.levels.clock.op i p)
local notation "e" => (A.levels.budget i).supportExponent
local notation "Γ" => (A.levels.budget i).B
local notation "Ψ" => Names V I
variable {s:Config G (A.S.side (i+1) p)→Poly (Names V I)} {o:I→Site (A.S.side (i+1) p)}
    {P:Brigade (A.S.side i p) V} {w:I→ℝ} {X:I→Lamp G (A.S.side (i+1) p)}
local notation "B*" => (P.climb A p)
local notation "o'" => ((Z).ratio.parent ∘ o)
local notation "Q" => ((Z).push (A.rep N p (i+1)).beta s)
variable (Y:I→Lamp G (A.S.side i p)) (hA:A.Selected) (hi:i<N) (ht:Thor A δ r D σ χ k) (hk:k ≤ i)
    (h:Fleet (P.climb A p) (A.rep N p (i+1)) s o X w)
    (hv: Occupancy (P.place ((A.levels.clock.op i p).ratio.parent ∘ o)) (r i))
    (hz:∀ j, Debt A N p (D N p i hi) (w j) (o j) (X j) (Y j))
include hA hi ht hk h hv hz
lemma Fleet.bids : ∃ u:I→ℂ,∃ K:V×I→ℕ→ Config G (A.S.side i p)→ℂ, (∀ j,w j.snd * ‖P.quotes u j‖ ≤ 1) ∧ (∀ j,Dominated (K j))∧
      (∀ j,profile (a).activities (K j)=P.ray (a) Y j) ∧ (∀ j,K (P.head,j)=(Y j).sparks) ∧ (∀ j U, (Q U).part ((Names V I).fire j)=coin (a) (P.lamp Y j) (K j) U) ∧
       Arc (a) (P.lamp Y) K Q P.head P.spin P.center P.roll (P.place o') (fun j=>δ i*(w ∘ Prod.snd) j) (e+1/2) (e+1) 1 (χ i) (δ i) (P.quotes u):=by
    choose μ u x y hm hx hy hM hW using fun j=>(hz j).votes; obtain ⟨K,hK,hK',hK0⟩:= (P).candle A N p Y hA hi.le; obtain ⟨K',hL,hL',hL0⟩:= (B*).candle A N p X hA hi
    have hI:Integrable Q (prior G c) := StepData.push_integrable (A.levels.transition_mass ..) _ h.pay -- unused
    have hL0 (j): K' (P.head,j)=(X j).sparks:= hL0 j; have ho: Occupancy ((B*).place o) (r i) := by
       intro x; refine le_trans (card_le_card ?_) (hv ((Z).ratio.parent x)); intro j hj; apply mem_filter.mpr; rw [← P.pegs A p]; exact ⟨mem_univ _,congr_arg (Z).ratio.parent (mem_filter.mp hj).2⟩
    have hp: May P.head P.spin (B*).center P.roll ((B*).lamp X) (fun j=> profile (A*).activities (K' j)) (P.quotes u):=by simp_rw [hL']; exact (B*).may (fun j=>(X j).watch) (fun j=> (X j).rays (A*)) u
    have he': May P.head P.spin P.center P.roll (P.lamp Y) (fun j=>profile (a).activities (K j)) (P.quotes u):=by simp_rw [hK']; exact P.may (fun j=>(Y j).watch) (fun j=>(Y j).rays (a)) u
    have hS:Serves (A*) ((B*).lamp X) (fun j=> profile (A*).activities (K' j)) s P.head P.spin (fun j=>(Z).ratio.embed (P.center j)) P.roll ((B*).place o) (w ∘ Prod.snd) ((A*).p.supportExponent-3) 1:= by simp_rw [hL']; exact h.sem
    have he:= ht.moon N p i hk hi; have ha:=(hA.represents N p (i+1) hi); have hb:= hA.represents N p i hi.le
    refine ⟨u,K,fun j=>?_,hK,hK',hK0,?_,?_⟩
    · unfold Brigade.quotes; split; exact hW _; rw [norm_scalar]; exact hW _
    · have hξ(j):(fun U=>(s U).part ((Ψ).fire j))=coin (A*) ((B*).lamp X j) (K' j):=funext fun U=> hS.sold.relay hL ha.good.labels U|>.1 j
      rintro ⟨j,u'⟩; apply congr_fun («f»:=fun U=>(Q U).part ((Ψ).fire (j,u'))); rw [show (fun U=>(Q U).part ((Ψ).fire (j,u'))) = (Z).push (A*).beta (coin (A*) ((B*).lamp X (j,u')) (K' (j,u'))) from (push_get (A.levels.transition_mass ..) h.pay _).trans (by rw [hξ])] -- under binder issue
      have hw : (Z).push (A*).beta (coin (A*) ((B*).lamp X (P.head,u')) (K' (P.head,u'))) = coin (a) (P.lamp Y (P.head,u')) (K (P.head,u')):= by
         simp only [Brigade.lamp,Brigade.calls,Brigade.climb,if_pos rfl,hL0,hK0]; exact (hz u'|>.arrives).symm
      by_cases hh:j=P.head; subst j; exact hw
      have hO:= opals (P.spin j) A hA hi (B*|>.center j) ((B*).lamp X (P.head,u')) (ha.good.labels.moves _ _).some (hL _) (hL _) (((hp j hh).2 u').2.1); have hT:= opals (P.spin j) A hA hi.le (P.center j) (P.lamp Y (P.head,u')) (hb.good.labels.moves _ _).some (hK _) (hK _) (((he' j hh).2 u').2.1)
      rw [((hp j hh).2 _).1, ((he' j hh).2 _).1,hO,hT,← hw]; have hQ: Integrable (coin (A*) ((B*).lamp X (P.head,u')) (K' (P.head,u'))) (prior G f):=by rw [← hξ]; exact ((Poly.get ((Ψ).fire (P.head,u'))).restrictScalars ℝ).integrable_comp h.pay
      simpa only [blast,pow_zero,one_smul] using! unison (P.spin j) A i N p 0 (P.center j) _ hQ
    rw [← P.pegs A p]; refine freshArc A N i p r hA hi (ht.suns i hk) he.1 he.2 (fun j=>h.secure j.2) hS (by rw [ha.vac]; linarith only) ho (by rw [P.pegs A p]; exact hv) (fun _ _ _=>rfl) (s:=x) («r»:=y) (fun j=>hy j.2) (fun j=> hM j.2) ?_ ?_ (fun i=>ha.good.labels.moves _ _)
    · intro j z; refine ⟨μ j,hm j,?_⟩; unfold z; simp only [Brigade.lamp,Brigade.calls,Brigade.climb,Function.comp_apply, Brigade.place,hL0,hK0,Brigade.quotes,if_pos rfl]; exact hx j
    exact chimes_parent A ((B*).pointed o) hp (fun i hi b=> ((he' i hi).2 b).2.1)
lemma Fleet.steady {w':I→ℝ} (hf:∀ j,0<w' j)
    (he:Repegs (P.place ((A.levels.clock.op i p).ratio.parent ∘ o)) (A.levels.budget i).B (fun j=>δ i*(w ∘ Prod.snd) j) (w' ∘ Prod.snd) (1/2) 1 (Names V I)) : Fleet P a Q o' Y w':=by
    obtain ⟨u,K,hK,hF,hC,hK0,hT,hR⟩:= Fleet.bids Y hA hi ht hk h hv hz; let x:= (Z).ratio.parent ∘ (B*).place o; have hP:= P.pegs A p o
    have hZ: Serves (a) (P.lamp Y) (fun j=>profile (a).activities (K j)) Q P.head P.spin P.center P.roll x (w' ∘ Prod.snd) e 1:= descended A N i p r hA hi (ht.suns i hk) (fun j=> h.secure j.2) (fun j=>hf j.2) (hP.symm ▸ hv) (hP.symm ▸ he) (hP.symm ▸ hR) hF hT; unfold x at hZ; rw [hP] at hZ; simp_rw [hC] at hZ
    refine ⟨(hZ.prune (fun j=>hf j.2) (fun j=> hf j.2) (slighter (fun j=>hf j.2) (fun j=>hf j.2) (w:=1) (fun j=>(one_mul _).symm.le) zero_le_one le_rfl) zero_le_one (by rw [(hA.represents N p i hi.le).vac]; linarith only) (by norm_num)), StepData.push_integrable (A.levels.transition_mass ..) _ h.pay,hf⟩
variable (H l:ℕ) (L:Fibers I J) (C:J→Prop)
local notation "Q'"=> (fun U=> Fibers.reap (partialGroup V L) (Q U))
local notation "w*"=>grouped A δ H l i w L
lemma Fleet.collect (hC:∀ j,C j→ L.Only j)(hf: Arsenal (A.rep N p i)) (hr:ClusterPars A δ χ r i) (hV:0<H)(hh:Fintype.card I≤H)
     (hx:∀ z:V×I, coverNumber (A.levels.budget i).B ({P.place ((A.levels.clock.op i p).ratio.parent ∘ o) (z.1,L.twig (L.bunch z.2)),P.place ((A.levels.clock.op i p).ratio.parent ∘ o) z}:Support _) ≤ l) :
     ∃ Y':J→ Lamp G c, (∀ j,C j→ Y' j=Y (L.twig j))∧ (∀ j,¬C j→ (Y' j).Flex (a) (o' (L.twig j)) (4*(1/w* j))) ∧ Fleet P a Q' (o' ∘ L.twig) Y' (w*):=by
    obtain ⟨u,K,hK,hF,hτ,hK0,hT,hR⟩:= Fleet.bids Y hA hi ht hk h hv hz
    obtain ⟨F,K',hk',hY,hV',h',hR'⟩:=regroups H l L hA hi.le hr (ht.suns i hk) hR hF (by simp_rw [hτ]; exact P.may (fun j=>(Y j).watch) (fun j=>(Y j).rays (a)) u) hT (P.pointed _) C hC h.secure hK hf hV hh hv hx
    let F'(j) : Lamp G c:=⟨F (P.head,j),K' (P.head,j),hV' _⟩; obtain ⟨hs,hF'⟩:= Brigade.lamp_eq (P:=P) h' F' (fun _=>rfl) (fun _=>rfl)
    refine ⟨F',fun j hj=>?_,fun j hj=> ?_,?_⟩
    · have he:=(hk' (P.head,j) hj); cases hX : Y (L.twig j); unfold F'; congr; exact he.1.trans (by simp [Brigade.lamp,Brigade.calls,hX]); exact he.2.trans ((hK0 _).trans (congr_arg Lamp.sparks hX))
    · have ht:= hY (P.head,j) hj; unfold Function.comp at ht; change Blade .. at ht; simp [partialGroup, Brigade.place] at ht; rw [one_div]; exact ht
    rw [← (hA.represents N p i hi.le).vac, hF',hs, show P.place o' ∘ (partialGroup V L).twig=P.place (o' ∘ L.twig) from rfl] at hR'
    have hu : Integrable (Q) (prior G c):= StepData.push_integrable (A.levels.transition_mass ..) _ h.pay
    exact ⟨hR',((partialGroup V L).reap.restrictScalars ℝ).integrable_comp hu,grouped_pos H l L hr.funs.1 hV h.secure⟩
end YM.MergeProof.Ribbons.ManyCopies.Patrol
