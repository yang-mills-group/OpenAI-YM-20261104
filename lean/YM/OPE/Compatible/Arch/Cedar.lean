import YM.OPE.Compatible.Arch.Pines
/-!
# Footprints. Finite cone price
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Libra
open Function Filter Set Lattice Laurent Tree Woody Weir Cascade MeasureTheory LinearMap
open scoped Topology BigOperators ComplexConjugate Classical ContDiff ENNReal
open PertExtension Series GaussianScore Asymptotics
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
local notation "Lf" => Tested.germ
abbrev ScriptJ (E:Type*) := E→ JetS ℝ
namespace ScriptJ
def quitt (p: ScriptJ E)(t:ℝ)(x:E):= (p x).atK t
protected abbrev B (p:ScriptJ E): Prop:=∀ k, Bond (fun x:E=>(p x).seq k)
variable {p s: ScriptJ E}
lemma bondX (hp:p.B):Bond (fun i=>(p i).s) ∧ Bond (fun i=>(p i).l) ∧ Bond (fun i=>(p i).h) := ⟨hp 0,hp 1,hp 2⟩
lemma Xbond (h1:Bond (fun i=>(p i).s))(h2: Bond fun i=>(p i).l)(h3:Bond fun i=>(p i).h):p.B:= by intro k; match k with 
 | 0=>exact h1 
 | 1=>exact h2 
 | 2=>exact h3 
 | _+3=> exact Bond.keep 0
lemma height (h:p.B)(x:s.B): (p*s).B:= by
     obtain ⟨r,t,v⟩:= bondX h; obtain ⟨a,b,c⟩:= bondX x
     exact Xbond (r.mul a) ((r.mul b).add (t.mul a)) (((r.mul c).add (t.mul b)).add (v.mul a))
lemma key (h:p.B)(x:s.B): (p+s).B:=by
     obtain ⟨r,t,v⟩:= bondX h; obtain ⟨a,b,c⟩:= bondX x; exact Xbond (r.add a) (t.add b) (v.add c)
def low (u:E→ℝ): ScriptJ E:=fun x=>⟨u x,0,0⟩
lemma lower {u:E→ℝ}(hp:Bond u) : (low u).B:= Xbond hp Bond.zero Bond.zero
end ScriptJ
open ScriptJ Zone
local notation "R" => Radial.zone (E:=E)
structure Bears (u:E→ℝ)(A:ℝ→ E →ℝ)(p:ScriptJ E): Prop where
    toll : p.B
    slope : (R).Fits u 3 (A-quitt p)
namespace Bears
variable {A C:ℝ→ E →ℝ}{p s: ScriptJ E}{u v:E→ℝ}
lemma stale (h:Bears u A p)(x:E): Reads (fun t:ℝ=> A t x) (p x):=by
   obtain ⟨e,d,k,he,hd,hK⟩:=h.slope.cost; unfold Reads; rw [Reads.isTariff]; let w:=(R).w x; have hw:0<w:=lt_of_lt_of_le zero_lt_one ((R).high x); refine ⟨d*w^k*u x,mul_nonneg (by positivity) (zero_le_one.trans (h.slope.envelope x)),?_⟩; filter_upwards [Tested.eventually_small (show 0< e/w from div_pos he hw)] with t ht; exact hK x t ht.1 ((le_div_iff₀ hw).mp ht.2.le)
lemma equiv (h:Bears u A p)(hk:∃ a>0,∀ x t,0<t→ t* (R).w x ≤ a → A t x=C t x): Bears u C p:= by
    obtain ⟨a,ha,hx⟩:=hk; refine ⟨h.toll,h.slope.lift_dominate ha fun x t ht h=>?_⟩; simp [hx x t ht h]
lemma piled (h:Bears u A p)(t:Bears u C s): Bears u (A+C) (p+s):=by
    refine ⟨key h.toll t.toll,?_⟩; convert! h.slope.add t.slope using 1; funext y x; change A y x+_-(p x+s x).atK _=(A y x-(p x).atK _)+(C y x-(s x).atK _); rw [JetS.rates_add, Pi.add_apply]; ring
variable [FiniteDimensional ℝ E]
private lemma banquet (h:p.B): (R).Fits (fun _:E=>1) 0 (quitt p) := by
    have he : quitt p = Zone.eval (fun i x=>(p x).seq i) 2:=funext fun t=> funext fun x=> ((p x).atK_seq t).symm
    rw [he]; exact Fits.power_eval (fun j _=>(h j).cost) (fun _=>le_rfl)
lemma savory (h:Bears u A p): (R).Fits u 0 A:=by
    rw [← sub_add_cancel A (quitt p)]; exact (h.slope.degrade (Nat.zero_le _)).add ((banquet h.toll).widen (h.slope.envelope))
omit [FiniteDimensional ℝ E] in
lemma grade (h:p.B)(hv:∀ i,1≤u i): Bears u (quitt p) p:=⟨h,by rw [sub_self]; exact Fits.zero hv (R) _⟩
lemma ascent (h:Bears u A p)(t:Bears v C s): Bears (u*v) (A*C) (p*s):=by
    have ht:= h.slope.mul t.savory
    have hh:=(Fits.widen (banquet h.toll) h.slope.envelope).mul t.slope; rw [zero_add] at hh; refine ⟨height h.toll t.toll,?_⟩; rw [show A*C-quitt (p*s)=(A-quitt p)*C+quitt p*(C-quitt s)+(quitt p*quitt s-quitt (p*s)) by ring]
    apply (ht.add hh).add; let f:E→ℝ:=fun i=>(p i).l*(s i).h+(p i).h*(s i).l; let w:E→ℝ:=fun i=>(p i).h*(s i).h
    obtain ⟨h1,h2,h3⟩:= bondX h.toll; obtain ⟨h4,h5,h6⟩:= bondX t.toll; have hb : (quitt p *quitt s - quitt (p*s))=(fun (t:ℝ) x=> t^3 * f x)+(fun t x=> t^4*w x):=by
       funext t x; let a:=p x; let b:=s x; change a.atK _*b.atK _-(a*b).atK _= _; unfold JetS.atK; simp only [smul_eq_mul, Pi.add_apply]; change (p x).s |> fun e=> (e+t*_+_)*_ -(e*b.s+t*(a.s*b.l+a.l*b.s)+t^2*(a.s*b.h+a.l*b.l+a.h*b.s))= _; unfold f w a b; ring
    rw [hb]; exact (Fits.power ht.envelope (show (R).Invoice f from (((h2.mul h6).add (h3.mul h5))).cost) 3).add ((Fits.power ht.envelope (show (R).Invoice w from (h3.mul h6).cost) 4).degrade (by decide))
end Bears
end YM.OPE.Libra
