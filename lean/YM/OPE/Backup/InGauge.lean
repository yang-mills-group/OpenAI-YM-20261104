import YM.OPE.Backup.Hamlet
import YM.OPE.Log.PaidMove
/-!
# Keep back, held Manuscript lease

Mask propagated by pushing all monomials, honoring non-spacing for supplementary
names on the *true* propagation. Uses Census in the form of a mask with downward
closure; pass a stronger mask at the phase of regrouping.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies.Muster
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil Source
open Extra.Trajectories MergeProof.Float OPE.Backup
open scoped Topology BigOperators Classical
variable {V I : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]{G:Gauge}{f c n:Side}{R:Rep G f}{R':Rep G c}
local notation "X"=>Names V I
set_option quotPrecheck false
variable {o:V×I→Site f}{w w':V×I→ℝ}{q:V→Site f}
    {E:V→Motion}{v:V}{A:V→ Equiv.Perm V}{u x e : ℝ}
    {Y:Config G f→Poly (Names V I)}{K:(V×I)→Res G f}{F:(V×I)→ Config G f→ℂ}

/-- Mask copy across mirrors -/
def Trial (L:Ward X) := ∀ (a:Equiv.Perm V) (p:(X).Mode), L.ready p ↔ L.ready (drum a p)
variable {L:Ward (Names V I)}
lemma studs_mask (h:Trial L){p q:Poly X}{a:Equiv.Perm V}{m:Motion}(hp:Harm v a m p q) : Harm v a m (L.clear p) (L.clear q):= by
    intro i hi; by_cases he:L.ready i; · rw [L.clears _ i he,L.clears _ _ ((h a i).1 he)]; exact hp i hi
    rw [L.zero_off _ he,L.zero_off _ (mt (h a i|>.2) he),scalar_z]
lemma horns_mask (H:Trial L){F:Support f→ Config G f→Poly X}{K:Box f→ Config G f→Poly X}(hp:Horn v E q A F K): Horn v E q A (fun i U=>L.clear (F i U)) (fun i U=>L.clear (K i U)):=fun i hi=> ⟨(hp i hi).1,fun U=> ⟨fun p=>studs_mask H ((hp i hi|>.2 U).1 p),fun p=>studs_mask H ((hp i hi|>.2 U).2 p)⟩⟩

structure Bard (R:Rep G f)(L:Ward X)(v:V)(E:V→Motion)(A:V→ Equiv.Perm V)(q:V→ Site f)(o:V×I→Site f)(F:(V×I)→ Config G f→ℂ)(K:(V×I)→Res G f)(Y:Config G f→ Poly X)(w:V×I→ℝ)(u:ℝ) : Prop where
   grants : ∃ Y':Config G f→Poly X, Serves R F K Y' v E q A o w u 1 ∧ ∀ U, L.Writes (Y U) (Y' U)
variable (h:Bard R L v E A q o F K Y w u)
lemma Bard.of_serves (L: Ward X)(h : Serves R F K Y v E q A o w u 1) : Bard R L v E A q o F K Y w u:=⟨_,h,fun _=> Ward.reflex L _⟩ -- etc unfold hp
lemma Bard.care (h:Bard R L v E A q o F K Y w (u+e))(hp:Trial L)(hw:∀ i,0<w i)(hx:∀ i,0<w' i)(hφ:L.Cares o R.p.B w w' e):Bard R L v E A q o F K Y w' u:=by
   obtain ⟨Y',g,hh⟩:=h.grants; obtain ⟨F',K',hT,hF,hK,hS,hE⟩:=g
   refine ⟨restore R F K (fun i U=>L.clear (F' i U)) (fun i U=>L.clear (K' i U)),⟨_,_, L.carton hT,?_,?_,horns_mask hp hS,rfl⟩, ?_⟩
   · exact L.towed_clear hF (fun i=> (hT.exp i).1.toBorne) (fun i=> (hT.exp i).2) hφ hw hx
   · exact L.towed_clear hK (fun i=> (hT.flag i).1.toBorne) (fun i=> (hT.flag i).2) hφ hw hx
   subst Y'; exact fun U=>(hh U).seq (L.restore_clear R F K _ _ U) -- syntax
lemma Bard.shrinks (h:Bard R L v E A q o F K Y w u)(hw:∀ i,0<w i)(hx:∀ i,0<w' i)(he:w' ≤ w)(hr:x ≤ u) : Bard R L v E A q o F K Y w' x:=by
   obtain ⟨Y',hh,hP⟩:=h.grants
   exact ⟨Y',hh.prune hw hx (slighter hw hx (w:=1) (fun i=> (he i).trans_eq (one_mul _|>.symm)) zero_le_one le_rfl) zero_le_one (by simp [hr]) (one_mul _|>.le),hP⟩
lemma Bard.fire (h:Bard R L v E A q o F K Y w u)(U:Config G f){k:(V×I)→ ℕ → Config G f→ℂ}(hr:R.activities.Valid R.p x e)(hk:K=fun i=>profile R.activities (k i))(hd:∀ i,Dominated (k i))(j:V×I): (Y U).part ((X).fire j)=coin R (F j) (k j) U:=by
   subst K; obtain ⟨Y',H,hr'⟩:=h.grants; exact ((hr' U) _ (L.fire j)).trans (H.sold.relay hd hr U|>.1 j)
lemma Writes_push (S:StepData c f)(hK:S.IsKernel R.beta G) {Y':Config G f→Poly (Names V I)}(hi:Integrable Y (prior G f))(he:Integrable Y' (prior G f)) (hr:∀ U,L.Writes (Y U) (Y' U))(U:Config G c) : L.Writes (S.push R.beta Y U) (S.push R.beta Y' U):=fun i hp=> by
   rw [show (S.push R.beta Y U).part i=_ from congr_fun (push_get hK hi i) U, show (S.push R.beta Y' U).part i= _ from congr_fun (push_get hK he i) U]; exact congr_arg (fun q : Config G f→ℂ=> S.push R.beta q U) (funext fun U=> hr U i hp)

-- Once-step fake income is integrable for push ANY expense, not inferred from
-- integrability of the true birth product on matched monomials.
lemma unabridged {D:GaugeDoor R R'}{S:StepData c f}{E':V→Site c}{p:(V×I)→ℂ}{b d t:ℝ}{a s:I→ℝ}{k':(V×I)→Res G c}
    (hξ:Serves R F K Y v E (fun i=> S.ratio.embed (E' i)) A o w u t)
    {a' x y z r:ℝ}{N:ℕ}
    (hD:Tunes D)(hs:SoundDoor S D)(hC:chimes v E E' A o (S.ratio.parent ∘ o) F K k' p S)(hr:R.Lawful x y z r a')
    (hw:∀ i,0<w i)(hm:∀ i,i≠v→∀ j:I,w (i,j)=w (v,j))(hh:∀ i:I,let y:V×I:=(v,i);∃ l:Set Wing,l.Finite∧Tale l (o y) (S.ratio.parent (o y)) 1 (F y) (K y) (k' y) (p y) (a i) (s i) D)
    (hP:Occupancy o N)(hy:0≤ b)(hb:0≤u)(ha:u+1≤R.p.supportExponent)(hk:∀ i:V×I,2*w i*a i.snd≤b)(hx:∀ i:V×I,w i*s i.snd≤d)(hX:Arsenal R): Integrable Y (prior G f):=by
   obtain ⟨J,hJ,M,hM,-,ψ,hψ,-,-,hΦ⟩:= propels (x:=d) (e:=R'.p.supportExponent) hD hs hC (fun i=> (hr.labels.moves _ _).some) hw hm hh hP hy ha hk hx (by linarith only) hr hξ hb hX
   let u':=Poly.pass (Mach X p); let L':Poly X →ₗ[ℂ] Poly X:=⟨⟨(u'*·),fun a b=>mul_add ..⟩,fun c p=> mul_smul_comm ..⟩
   rw [funext hΦ]; exact ((L'.restrictScalars ℝ).toContinuousLinearMap).integrable_comp (heat M S w hr)
end YM.MergeProof.Ribbons.ManyCopies.Muster
