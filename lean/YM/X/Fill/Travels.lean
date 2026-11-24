import YM.X.Fill.Case
import YM.X.Shelf.Corn
/-!
# Motion annular rays on all physical points including on central. Supply from Tide.
-/
noncomputable section
set_option autoImplicit false
namespace YM.PositionX.Friend
open Lattice Wilson Next.Rank Normal MvPolynomial PertExtension LatticePT MeasureTheory Metric Filter Set Function Asymptotics Reed Braid Fielding Haze Clove Interval CellsInt Shelf Size
open Ocean
open Stems hiding X
open scoped Topology ContDiff Classical BigOperators
variable {G: Gauge}
variable {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]
variable {q:ℕ+} (hq:1<q.val){k m:ℕ}{a b n : ℤ}{R r:ℝ}{f g:Mist ℂ}{w:Floor R}
namespace Chase
lemma lonely {f:ℕ→V}{m:ℤ}(h:∀ R:ℝ,0≤R→ R<r→ Visa q R m 0 (Once f)) : Chase q r m (Once f) := by
   constructor; intro l T ht hv; cases l with
   | nil=> rw [List.length_nil,Nat.cast_zero,add_zero];exact h T ht hv
   | cons i l=>
      have he(n:ℕ):Interval.differ i (Once f n)=0:= by funext; unfold Interval.differ Once;simp
      have hx(l:List Axis): Interval.grads l (0:Cover→V)=0:= by clear he hv; induction l with| nil=> rfl| cons i l IH=> funext; rw [Interval.grads, IH,differ]; simp
      simp_rw [downtick,he,hx]; exact Visa.zero
lemma alone {f:ℕ→V}(h:Released (fun i=> epsilon q i ^(-n) • f i)) : Chase q r n (Once f):= lonely (fun R _ _=> Visa.once f h)
lemma quiet (x:V): Chase q r 0 (Once (fun _=>x)):=lonely (fun _ _ _=> Visa.fix x)
lemma base: Chase q r a (0:Mist V):= alone (f:=0) (by simp only [Pi.zero_apply, smul_zero]; exact Released.zero)
lemma smultC (c:ℂ)(h:Chase q r a f): Chase q r a (c • f):= Chase.moves (L:= (ContinuousLinearMap.lsmul ℂ ℂ c).restrictScalars ℝ) h
lemma com {g:Mist ℝ}(h:Chase q r a (g:Mist ℝ)): Chase q r a (fun i z=> Complex.ofReal (g i z)):= moves (L:=Complex.ofRealCLM) h -- g type binder
lemma vary {x y:Mist ℂ}(hx:Chase q r a x)(hy:Chase q r b y)(i:Axis): forward i (x*y)= alter (Lattice.step i) x* forward i y + forward i x * y:= by ext1 t; ext1 z; simp only [forward,Pi.sub_apply,Pi.add_apply,Pi.mul_apply,alter]; ring -- no h use
include hq in
lemma mulC (h: Chase q r a f)(hp:Chase q r b g): Chase q r (a+b) (f*g) := by
    constructor; intro L S hs hv; induction L generalizing f g a b with
    | nil=> let ha := Visa.mulC (h.visa hs hv) (hp.visa hs hv); simpa [Interval.grads] using! ha -- grads simpl?
    | cons i L IH=>
       have he(x:Mist ℂ)(k:ℕ): Interval.grads (i::L) (x k)=Interval.grads L (forward i x k):=downtick ..
       simp_rw [he,vary h hp]; rw [hikes]; apply Visa.add
       · rw [show a+b+(i::L).length=a+(b+1)+L.length from by simp; ring]; exact IH (h.alts hq _) (hp.step _)
       rw [show a+b+(i::L).length=a+1+b+L.length from by simp;ring]; exact IH (h.step _) hp
lemma power (n:ℤ): Chase q r n (Once (fun i=> epsilon q i ^ n)):=lonely (fun _ _ _=> Visa.powR)
include hq in
lemma fore (w:Floor R) : Chase q r 0 (relabel (Floor.maskL q w)):= ⟨fun L T ht hv=> by rw [zero_add]; exact Floor.derivative_visa hq w L T ht⟩
include hq in
lemma late_pay {f:ℕ→ℂ}(h:Vanished q f) (n:ℤ): Chase q r n (Once f):= alone (late hq (eps_supp h))
include hq in
lemma root_pay {A:ℕ→Brush G}(h:Tide q r A)(f:Fan G)(hf:f∈Reed.grads G k)(b:Bool): Chase q r (k+1:ℕ) (cuppa b A f):= by
    cases b
    · refine lonely (f:=fun i=> flatL (A i) (leadsL 0 f)) (fun R hr hp=>?_); exact footprint_field hq false hr hp.le h f hf
    constructor; intro l T ha ht; induction l generalizing k f with
    | nil=> rw [List.length_nil,Nat.cast_zero,add_zero];exact footprint_field hq true ha ht.le h f hf
    | cons i l IH=>
       let u:= leadsL (Lattice.step i) f-f; have he(t:ℕ): Interval.differ i (cuppa true A f t) = cuppa true A u t:= by ext1 z; change flatL (A t) (leadsL (z+Lattice.step i) f) -flatL (A t) (leadsL z f)= _; unfold cuppa u; simp_rw [map_sub]; rw [leads_comp]; rfl
       simp_rw [downtick,he]; rw [show ((k+1:ℕ):ℤ)+(i::l).length=(↑(k+1+1:ℕ):ℤ)+l.length from by simp; ring]; exact IH u (fan_triangle f hf i ) -- inspect
end Chase
end YM.PositionX.Friend
