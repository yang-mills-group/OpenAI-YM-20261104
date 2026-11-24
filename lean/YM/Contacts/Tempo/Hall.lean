import YM.Contacts.Tempo.Cover
import YM.Contacts.Harrier.Origin
namespace YM.Contacts.Tempo
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
open Harrier Harrier.Transfer Parcel Planned.PrimaryIntegral295
open Cartons Tensor Place Carrier MultiNext.SignedSource Pattern Barrage Barrage.Reserve.Oasis Analysis
variable {A: Ink G h M} {S:Boom} {e:Parcel G}{s:Parcel.Step}{K j':ℕ}
structure Grounds (A:Ink G h M)(e:Parcel G)(S:Boom) (s:Parcel.Step) (K k D:ℕ)(ζ:ℝ≥0) :Prop where
   lic : e.License S ζ
   steps : s∈S
   amount : enough (Banked e M K h k D) S
   count : h+3 ≤ e.J
   cap : h+1≤k
   market : h+1 ≤ D
namespace Grounds
variable (T: Grounds A e S s K k D ζ)
local notation "Γ" => terrain ζ (Dye G)
local notation "Η" => terrain (2*ζ) (Dye G)
local notation "η" => bath ζ k (Dye G)
abbrev round (s:Parcel.Step)(n:ℕ):Word:= List.replicate n s
abbrev hop (e:Parcel G)(s:Parcel.Step)(M h n:ℕ): Sketch G → Sketch G := Transfer.mean e (round s n) s M h
variable (e s M h)
def play (V:Sketch G):ℕ→Sketch G
   | 0=> V
   | n+1=> hop e s M h n (play V n) -- arg order?
variable {e s M h}
local notation "τ" => hop e s M h
local notation "R" => play (M:=M) (h:=h) e s
include T
lemma south :Demand S e M K:= tickets T.amount
lemma in_path (n:ℕ): OK S (round s n):= by induction n with|zero=>exact OK.nil|succ n ih=> exact ih.cons T.steps
lemma home : h ≤ e.J:= le_trans (Nat.le_add_right ..) T.count
lemma center : h≤ D:= le_trans (Nat.le_add_right ..) T.market
lemma ready : 0 < (2*ζ:ℝ≥0):= lt_of_lt_of_le T.lic.light T.lic.down
variable {x:Dye G} {F P V:Sketch G} (hp:Living x M D F (2*ζ))(hq:Living x M D P (2*ζ)) (hz:Living x M D V (2*ζ))
lemma roof (hv:Living x M D F ζ): Living x M D (τ n F) (2*ζ):=cenacle T.lic (T.in_path n) T.steps hv h
lemma own (hv:Living x M D F (2*ζ)) (n:ℕ): Living x M D (R F n) (2*ζ):= by induction n with|zero=>exact hv|succ n ih=> exact T.roof (ih.lower T.lic.down)
variable (x)
include x
lemma hop_zero : τ n 0=0:= means_zero T.lic (T.in_path n) T.steps x ..
lemma play_blank : R 0 n=0:= by induction n with|zero=>rfl|succ n ih=>rw [play,ih]; exact T.hop_zero x

variable {x}
lemma hop_pay (h: Living x M D F (2*ζ))(he: Living x M D V (2*ζ)): τ n (b • F+V)=b • τ n F+τ n V:= mean_tilt T.lic (T.in_path n) T.steps _ _ (h.lower T.lic.down) (he.lower T.lic.down)
include hp
lemma play_pay (hz:Living x M D V (2*ζ))(n:ℕ)(b:ℝ): R (b • F+V) n=b • R F n+ R V n:= by induction n with|zero=>rfl|succ n ih=> rw [play, ih,T.hop_pay (T.own hp n) (T.own hz n)]; rfl
lemma play_add (hz: Living x M D V (2*ζ)) : R (F+V) n=R F n+R V n:= by simpa only [one_smul] using T.play_pay hp hz n 1
lemma play_sub (hz: Living x M D V (2*ζ)) : R (F-V) n= R F n-R V n:= by apply eq_sub_of_add_eq; rw [← T.play_add (hp.sub hz) hz,sub_add_cancel]
lemma play_scale : R (b • F) n=b • R F n:=by simpa only [T.play_blank x,add_zero] using T.play_pay hp (Living.zero x ..) n b
omit hp
lemma pre_echo (hi:i ≤ K) (hp:Living x M D F (2*ζ)) (hX:Harrier.Before η D x F i r 0): Harrier.Before η D x (R F n) i r 0:= by
   induction n with|zero=>exact hX|succ n ih=>
   obtain ⟨b,hb,B⟩:= prior_consumed (r:=r) (D:=D) T.lic T.steps x T.south hi h; let P:=R F n; have hb:= (B P ((T.own hp _).lower T.lic.down) 0 le_rfl ih.lower).1 (round s n) (T.in_path n); intro u v hu; have ht:Enroll Η D x (τ n P) u v 0:= mul_zero b ▸ hb u v hu; apply w_raise (spa_weight (k:=k) T.lic.light ht); simp only [mul_zero,le_refl] -- maybe explicit
variable {Z: Pulse.Range (Node (Dye G))}
omit T
lemma issued_mon (ht:Issued Z D x F i r b)(h:b≤c) : Issued Z D x F i r c:= ⟨ht.1.mon h,w_raise ht.2 h⟩
lemma issued_down (ht:Issued η D x F i r b) : Issued Γ D x F i r b:= ⟨ht.1.lower,w_upped ht.2 le_rfl (fun _=>bath_terrace _)⟩
lemma before_add (h: Harrier.Before Z D x F i r b)(ht:Harrier.Before Z D x V i r c): Harrier.Before Z D x (F+V) i r (b+c):= fun i j hx=>w_add (h i j hx) (ht i j hx)
lemma before_sum {P:ι→Sketch G}{b:ι→ℝ}(W:Finset ι)(H:∀ i'∈W,Harrier.Before Z D x (P i') i r (b i')):Harrier.Before Z D x (∑ i∈W,P i) i r (∑ i∈W,b i):= by intro a k h; rw [Enroll,sum_sail]; exact w_sum (fun i h'=> H i h' a k h)
lemma before_scale (b:ℝ)(h:Harrier.Before Z D x F i r c):Harrier.Before Z D x (b • F) i r (‖b‖*c):= fun a k hx=> w_scale (h a k hx) _
include T
variable (x)
lemma graph_bill (u v:Badge A.prism)(ht:u.slot=v.slot): let f p:= graph e p s A u v;
    ∃ a≥(0:ℝ),(∀ p,OK S p→‖f p‖≤ a)∧∀ p q v,OK S p→OK S q→OK S v→ ‖f (v++p)-f (v++q)‖ ≤ a*mileage v:= by
   intro f; let r:= v.slot; obtain ⟨a,ha,A'⟩:= key_bill T.lic T.steps (D:=D) x T.south (Nat.zero_le K) h u (second A u);
   let hv: Living x M D (A.purse v) ζ := A.life v T.center; obtain ⟨b,hb,B⟩:= hv.budget 0 v.slot; let Z:= A' _ hv b hb (by rw [ht]; exact ⟨(Transfer.stop x A v (ζ:=ζ) (D:=D) le_rfl).mon hb,B⟩); exact ⟨a*b,mul_nonneg ha hb,Z⟩
end Grounds
end
end YM.Contacts.Tempo
