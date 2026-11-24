import YM.FVA2.Recall.Step
import YM.FVA2.Hearth.Posed
/-!
 # Every coefficient, every clock through a new coupling usage on log-link frames

 Same regulator family & common witness. Algebraic identities only.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Recall.Move
open Function Set Filter Finset MeasureTheory FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open StationaryMarks MultiGauge.Stack PowerSeries MarkovChain Warp Splice OpenSlots
open Paint Euler PertExtension PertExtension.Series Radial GaussianScore Facade Lattice RG
open Tested OpenSlots.Quadratic Precision Chart BlockGauge MultiGauge.Blocking Fabric Papers Line Roof Router Hearth
open scoped Classical Topology BigOperators ContDiff
variable {G:Gauge}{c f n:Side}{J:ChartRatio G}(hj:LocalRatio J)
variable (m:Move)

namespace Frames

-- actual eliminated dimension count for this walk
 def depth {n:Side}{L:Fabric G n}(T:Cloth L)(k:ℕ) : ℕ:= match T with
 | .floor _ _ _=> k
 | .inLayer (S:=S) P C=> depth C (k+ Module.finrank ℝ (Cross (G:=G) S P))
variable {L:Fabric G n}

include hj
lemma reaches {n:Side}{L:Fabric G n}(T:Cloth L){U V:Unmasked G n}(k:ℕ)(u:Frames m k U V)(A:Ticket (Flats G n))(z:L.Cost→PowerSeries ℝ)(b:Commission J T U z)(b':Commission J T V (m.weight∘z))(h:incline U.W) :
 let x:= Facade.drive T z U A J b
 let y:= Facade.drive T (m.weight ∘ z) V (m.walk _ A) J b'
 Frames m (depth T k) x.1 y.1 ∧ y.2=m.walk (Flats G (Bottom L)) x.2:= by
 cases T with
 | floor=> exact ⟨u,rfl⟩
 | @inLayer c f S H t hf L P C=>
    intro x y; let q:= Exists.choose b; let q':= Exists.choose b'; let p:= z none; let U':= Update P t J p U q; let A':= Broadcast P t J p U q (boost (blankRight P) A); let V':= Update P t J (m.weight p) V q'; let C':= Exists.choose_spec b'; let B':= Exists.choose_spec b; let σ:= m.walk (Flats G c)
    have h': σ A'= Broadcast P t J (m.weight p) V q' (boost (blankRight P) (m.walk (Flats G n) A)):= by
       unfold A' σ; rw [projects m H t P k u p q q' ( boost (blankRight P) A ) h hj,boots]
    obtain hx:= reaches C (k+_) (tomorrow m H t P k u p q q' (J:=J)) A' (z∘some) B' C' (funded hj _ h q) -- m hj recursion implicit? inspect
    dsimp only at hx; rw [h'] at hx; exact hx
termination_by structural T
end Frames

section Era
variable {L: Fabric G n}(T: Cloth L)(w:L.Accounts→ PowerSeries ℝ)(h:∀ i,0<term (w i) 0)
local notation "r"=> Move.weight m ∘ w
include h
lemma still (i): 0<term ( r i ) 0:= (m.lead _) |>.symm ▸ h i
omit h
lemma born_l : Frames m 0 (headquarters (L:=L) w) (headquarters r) := ⟨ Hearth.quads ( m.tenure _ firstBill ), by
    change twist m (genesis (w none) firstBill) 0 * m.walk _ (chip (w none) firstBill) = chip (m.weight (w none)) _; unfold twist extra; rw [pow_zero,map_one,one_mul, m.renew _ _ first_held]⟩
local notation "X1"=> drive T (w ∘ some) (headquarters w)
local notation "X2"=> drive T (( r ) ∘ some) (headquarters ( r ) )
local notation "P"=> collared T w hj h
local notation "Q"=> collared T r hj (still m w h)
local notation "u"=> Flats G n
local notation "v"=> Flats G (Bottom L)
local notation "τ"=> m.walk u
local notation "ρ"=> m.walk v
include h hj
lemma epoch (A:Ticket (Flats G n)) :
    Frames m (Frames.depth T 0) (X1 A J P).1 ( X2 ( τ A ) J Q).1 ∧ (X2 (τ A) J Q).2=ρ (X1 A J P).2:= Frames.reaches hj m T 0 (born_l m w) A (w∘some) P Q ( OpenSlots.restores .. ) -- syntax verify

open OpenSlots Facade
variable (A:Ticket (Flats G n))
local notation "d"=> Frames.depth T 0
local notation "E"=> Field ( Cloth.choose (Hearth.finish T) )
local notation "f"=> (flat T w h hj)
local notation "π"=> (quiet T w h hj)
local notation "w0"=> ( still m w h )
local notation "κ"=> (Move.weight m ∘ w)
lemma nest : quiet T κ w0 hj A=π A:= by
 have hx:= (epoch hj m T w h A).1.top; rw [ any_state T T κ w0 hj hj (τ A) A ] at hx;
 let Y:= drag (castAt (Hearth.finish T)) (X1 A J P).1.Q; let S:= drag (castAt (Hearth.finish T)) (X2 A J Q).1.Q; have he: Y=S:= congr_arg (drag ( castAt (finish T))) hx
 unfold quiet; congr 2; exact hx.symm
lemma stop_w : flat T κ w0 hj A= extra («E»:=E) m d * m.adjust ((π A).P) * m.walk E ( f A ):= by
 let U:=(X1 A J P).1; let R':=finish T; let y:=castAt R'; rw [← show flat T κ w0 hj (τ A)= _ from (flat_one T κ w0 hj (τ A)).symm.trans (flat_one T κ w0 hj A)]
 unfold flat; rw [ ←(epoch hj m T w h A).1.wage ]; unfold inclineX; rw [ map_mul (boost _), dragT, map_mul (m.walk _), light, boots ]; unfold twist; rw [mul_assoc, show (π A).P=(drag y U.Q).P from decided (drag y U.Q) (permissions T _ _ _ P) ]

set_option quotPrecheck false
local notation "μ"=> tangent G (( Hearth.finish T ).choose.Bulk)
local notation "Δ"=> d+Module.finrank ℝ ( Blocking.Field (Hearth.finish T).choose )
local notation "hL"=> quiet T w h hj 1
local notation "T'"=> m.p^(Δ)
local notation "t"=> (vacuum T w h hj)
local notation "s"=> (vacuum T κ w0 hj)

lemma now_link (x:Ticket (Blocking.Field (Hearth.finish T).choose)) : input ( quiet T κ w0 hj 1 ) μ ( flat T κ w0 hj 1 * ( m.walk E x ) ) = T' * m.sponsor (input hL μ ( flat T w h hj 1 * x )):= by
 rw [nest hj m _ _ h, stop_w hj m _ _ h]
 rw [mul_assoc (extra _ _), mul_assoc (extra _ _), mul_assoc (adjust _ _), ←map_mul (m.walk _), extra,Book.secured,adjust, Book.night, pow_add ]; ring

lemma scalar : vacuum T κ w0 hj=m.p^(Frames.depth T 0+ Module.finrank ℝ (Blocking.Field (Hearth.finish T).choose))* m.sponsor (vacuum T w h hj):= by
 obtain ht:=now_link hj m T w h (1:Ticket E); simp only [ _root_.map_one,mul_one] at ht; exact ht
lemma totals : tally T κ w0 hj (τ A)= T'*m.sponsor (tally T w h hj A):= by
 unfold tally current; rw [ ( epoch hj m T w h A ).2, ← m.boots]; apply now_link hj

lemma credit : purchase T κ w0 hj (τ A) = m.sponsor (purchase T w h hj A):= by
 rw [←sold T κ w0, ←sold T w h]; simp only [_root_.map_mul];
 have he:s*s⁻¹=1:= PowerSeries.mul_inv_cancel _ (fun h=> one_ne_zero ((vacuum_ok ..).symm.trans h)); have ht: (t:PowerSeries ℝ)*(t)⁻¹=1:= PowerSeries.mul_inv_cancel _ (fun h=> one_ne_zero ((vacuum_ok ..).symm.trans h));
 have H':s ≠0:=fun hz=> by rw [hz,zero_mul] at he; exact zero_ne_one he
 apply mul_left_cancel₀ H'; rw [mul_left_comm (s), he,mul_one, totals hj m _ _ h, scalar hj m _ _ h];
 let y:=tally T w h hj A
 have hp:m.sponsor t*m.sponsor ((t)⁻¹)=1:= by rw [ ←map_mul,ht,m.sponsor.map_one ];
 linear_combination -(T'*m.sponsor y)*hp -- algebra.Y
end Era
end YM.FVA2.Recall.Move
