import YM.FVA2.O.Dust.Moods
/-!
# Short distance — negative real log time in MS continuum evolution

`Known`, `Safe`, `Nilp`: `Here` cost bounds (not the rough, size-only estimates).
`Nilp`: suppression at every power of the scale. Does not mean nilpotent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Cool
open MS Function Filter Set Finset MS.Plane MS.Koszul Flux MeasureTheory MS.Heat MS.Book Convolve Signal
open MS.Breeze MS.Latch MS.Osc MS.Osc.Snap MS.Fiddle MS.Garment MS.Garment.Wick MS.Rock MS.Rock.Path MS.City MS.Rake MS.Tone Momentum MS.Landau Detect MS.Color Real MS.Tide
open Ward Job Wire MS.Local.Physical MS.Land Lives Puff Serve Rake.Geo Vane Actors Fuse Job.Belt
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type} {F H:Glade G I}{U:Planet G I}{z p:I→ QP}{q b:ℤ}{v:ℝ}{u i:ℕ}{P:Geo I}{B:Deck G}{K: Booked B}{M: MS_Data G K}{X:Rake.Dance G I W}
abbrev Below (P:Geo I): Belt I:= east P false
abbrev Lower (P:Geo I):= (Below P).price
local notation "Qx"=> (east P false)
local notation "m0"=> (fun _:I=>planeF)
local notation "K0"=> Geo.constantP G I (PlanetD G)
abbrev Safe (P:Geo I) (F:Glade G I)(v:ℤ): Prop:= Here false false (Below P) F ( stamp (Lower P) v )
abbrev Nilp (P:Geo I)(F:Glade G I): Prop:= ∀ k:ℤ,Safe P F k
abbrev Known (P:Geo I)(F:Glade G I): Prop:= ∃ k:ℤ, Safe P F k
lemma safe_raise (h:Safe P F b)(ht:q≤b): Safe P F q := Latch.Lease.sticks h (fun i=> zpow_le_zpow_right_of_le_one₀ ((Lower P).pos i) ( b_le P i ) ht)
lemma safe_input {F:Pearl.Flats G}(h:Emit.Host F u): Safe P ( Rake.nameR ( Outlook.four u F ) P.η ) (-(u:ℤ)):= by intro E _ _ w hx ht; exact Rake.nameD (b:=false) (c:=false) (S:=Lower P) h ( a:=tstart ) (fun i=>( coldE P i ).symm) ( η:=fun i=>P.η i.1 ) (fun i=> LightY P _ _ _ i) E w hx ht
lemma safeB : Safe P ( approach P M i ) (-4):= safe_input (Emit.Host.host (Dock.gang (M.bulkOK i)))
lemma safeM (u:Rake.Label B): Safe P (rowM P M u i) (-(u.h:ℤ)):= safe_input ( Emit.Host.host ( Dock.gang ( M.markOK u.h u.item i )))
lemma Nilp.known (h:Nilp P F): Known P F:= ⟨0,h 0⟩
lemma Nilp.zero : Nilp P (0:Glade G I):= Thin.zero
lemma Nilp.add (h:Nilp P F)(he:Nilp P H): Nilp P (F+H) := Thin.add (h:=h) he
lemma Nilp.sum {J:Type}(s:Finset J){f:J→Glade G I}(h:∀ i∈s,Nilp P (f i)): Nilp P (∑ i∈s,f i):= by classical induction s using Finset.induction_on with| empty=> rw [Finset.sum_empty]; exact Nilp.zero | insert i s hi ih=> rw [ Finset.sum_insert hi ]; exact (h i (by simp)).add ( ih fun j hj=> h j (mem_insert_of_mem hj) )
lemma Nilp.lonely (he:Nilp P H): Nilp P (expJ K0 (approach P M i) H):= by
    intro k; have hp:= Geo.masterD G I P; -- syntax
    apply Latch.Lease.sticks ( trunks hp.market ( Latch.Lease.highp ( Latch.Lease.snow (show Safe P (approach P M i) (-4) from safeB))) ( Latch.Lease.highp (he k)) (fun _=>zero_le_one) (fun _=>posS _|>.le) (fun _=>posS _|>.le) ); intro j; simp only [ positive, stamp, Pi.one_apply,Pi.mul_apply, one_mul ]; apply le_of_eq; field_simp [ ( ( Lower P ).pos j).ne' ]; -- maybe defin K stuck
section
variable {D:ℤ}
-- `credit` R exponent sheet (odd included)
lemma region_P (hs:P.θ=0)(h:Sheet (Lower P) ( stamp (Lower P) D ) (plug U))(hx:CoverSep P p)(he: Safe P F q)(hp:Safe P H b): Nilp P (regionC m0 p U F H):= by
    obtain ⟨⟨a,ha,hv⟩,c,hc,hC⟩:= hx; have hr(i:I):roots P i=1:= by simp [roots,hs]
    intro k; let K:= (k-(D+q+b)).toNat; let S:=Lower P; let x(i:(east P false).time):= p i.1;
    obtain hx:= Latch.PulseQ h (Latch.Lease.highp he) (Latch.Lease.highp hp) (fun _=>posS _|>.le) (fun _=>posS _|>.le) (fun _=>posS _|>.le) (A:=x) (v:=1) ( fun i=>zero_lt_one ) (T:=c) (fun i=>(by rw [Pi.one_apply,← hr i.1] ; exact hC _)) (fun i=> b_le P i) ⟨a,ha,0,fun i=> by simp only [ Pi.one_apply,pow_zero,mul_one ]; exact ( hv i.1 ).trans_eq ( by rw [hr,mul_one] )⟩ hc K; -- Le syntax/g messed
    refine Latch.Lease.sticks hx (fun i=>?_); simp only [ stamp,Pi.one_apply,div_one ]; rw [ ← zpow_natCast,← zpow_add₀ ( S.pos i ).ne', ← zpow_add₀ ( S.pos i ).ne', ← zpow_add₀ ( S.pos i ).ne' ]; exact zpow_le_zpow_right_of_le_one₀ ( S.pos i ) ( b_le P _ ) (by unfold K; omega) -- ordering
lemma regionA (hs:P.θ=0)(hp: CoverSep P p)(h:Known P F)(he:Known P H): Nilp P (regionC m0 p K0 F H):= by obtain ⟨q,h⟩:= h; obtain ⟨b,he⟩:= he; exact region_P hs (by have hh:Sheet (Lower P) 1 (plug K0):= ( Geo.masterD G I P ).well ; simpa [stamp] using hh : Sheet (Lower P) (stamp (Lower P) 0) (plug K0) ) hp h he
end
end YM.FVA2.O.Cool
