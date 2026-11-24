import YM.OPE.Compatible.Sear.Merd
/-! # Omission and tilt cumul. Character placement not involved. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Cinders
open Function Filter Set MeasureTheory Finset
open scoped Topology BigOperators Classical ContDiff ENNReal
variable {I:Type*}{s t c:ℝ}{i j k:ℕ}{T d:I→ℝ}{l:Filter I}
open PertExtension Series Libra GaussianScore Jargon
section
abbrev Hang (X:I→Type*) := (i:I)→ X i → Token
variable {X:I→Type*} {S:∀ i,Set (X i)} {p q:PayR X}{Y P:Hang X}
abbrev Cs (_X:I→Type*) (s:I→ℝ): PayR _X:=fun i _=>s i
abbrev run_H (P:Hang X)(i:ℕ): PayR X:=fun v z=> (P v z).seq i
def TallT (S:∀ i,Set (X i))(l:Filter I)(T:I→ℝ)(Y:Hang X):Prop:=∀ i:Fin 3, Large S l T (run_H Y i.val) 0
abbrev aftD (P:Hang X)(d:I→ℝ): PayR X:=fun i z=> (P i z).atK (d i)
lemma pivot (h:TallT S l T Y)(hp:TallT S l T P)(hT:Tendsto T l atTop):TallT S l T (Y*P):=by
        let e:=fun (_:ℕ)=>h 0; have h0:=h 0; have h1:=h 1; have h2:=h 2; have he:=hp 0; have hg:=hp 1; have ht:=hp 2; intro i; fin_cases i
        · exact (h0.times he).grow (le_of_eq (zero_add _))
        · exact ((h0.times hg).added (h1.times he) hT).grow (le_of_eq (zero_add _))
        exact (((h0.times ht).added (h1.times hg) hT).added (h2.times he) hT).grow (le_of_eq (zero_add _))
lemma league (h:TallT S l T Y)(hT:Tendsto T l atTop)(hd:RateLE l T d 0): Large S l T (aftD Y d) 0:=by
        exact ((h 0).added (((Large.fromR _ hd).times (h 1)).grow (le_of_eq (zero_add _))) hT).added (((Large.fromR _ (hd.pow 2 hT)).times (h 2)).grow (by norm_num)) hT
structure Playbook (S:∀ i,Set (X i))(l:Filter I)(T:I→ℝ)(P:Hang X)(d:I→ℝ)(p:PayR X)(t:ℝ):Prop where
        Size: TallT S l T P
        wears : Large S l T (p-aftD P d) t
lemma rested (h:Playbook S l T P d p t)(hv:Playbook S l T Y d q t)(ht:RateLE l T d s)(hs:s < 0)(hj:t < 0) (hz:s*3 ≤ t) (hT:Tendsto T l atTop): Playbook S l T (P*Y) d (p*q) t :=by
        refine ⟨pivot h.Size hv.Size hT,?_⟩; have hp:=h.wears; have hh:=hv.wears; have hg:= league h.Size hT (ht.mono hs.le); have hu:=league hv.Size hT (ht.mono hs.le); have hx:Large S l T q 0:=by rw[←sub_add_cancel q (aftD Y d)]; exact (hh.grow hj.le).added hu hT
        let A:=aftD P d; let B:=aftD Y d; rw [show p*q-_= ((p-A)*q+A*(q-B)) + (A*B-aftD (P*Y) d) by ring]; refine (((hp.times hx).grow (le_of_eq (add_zero _))).added ((hg.times hh).grow (le_of_eq (zero_add _))) hT).added ?_ hT
        rw [show A*B-aftD (P*Y) d = Cs X (fun i=>d i^3)*(run_H P 1*run_H Y 2+run_H P 2*run_H Y 1)+Cs X (fun i=> d i^4)*(run_H P 2*run_H Y 2) from funext fun i=>funext fun x=>turnC (P i x) (Y i x) (d i)]
        have ha:=h.Size 1; have hb:=h.Size 2; have he:=hv.Size 1; have hd:=hv.Size 2
        have h3 := ((Large.fromR _ (ht.pow 3 hT)).times ((ha.times hd).added (hb.times he) hT))
        have h4 := ((Large.fromR _ (ht.pow 4 hT)).times (hb.times hd))
        exact (h3.grow (by push_cast;linarith)).added (h4.grow (by push_cast;linarith)) hT
end
end YM.OPE.Cinders
