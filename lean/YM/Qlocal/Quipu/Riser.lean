import YM.Qlocal.Quipu.Dais
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Quipu.Eluder
open AllOrder AllOrder.Ink Floe
open Lattice Laurent RG Gauge Filter Topology Finset Matrix Function Fire Laplace Laplace.SigmaP Ker Ker.Start
open Progress.ClassicalKin Progress.ClassicalKin.Tent Primitives.TwoWave RealSlice Push.Uniform Push.Local Push.AbsoluteSums
open PertExtension PertExtension.Series PositionX.Gauss PositionX.Jet Radial Response Ink Ink.Method Ink.Money GaussianScore Module
open Tree Wilson PhysicalNext Repeat Lapis ConnectedActivityE6 Blaze Precision Push Pressure Next.Fluctuations Next.SectorChange MeasureTheory
open Kinetic.Port
open Bloch hiding direct
open scoped BigOperators Topology Classical ContDiff Matrix.Norms.Frobenius
open Turbin Sonnet Marker Kinetic Primitives.GCC.Anchor
variable {ι α :Type}[Fintype α][DecidableEq α][Fintype ι] {G:Gauge} {n:Side} {k N :ℕ} {a b r :ℝ}{R:Marker.Census α}
local notation "J"=> ι⊕α
local notation "E"=> rule J n
local notation "A"=> rule ι n
local notation "B"=> rule α n
local notation "Λ"=> Leaf n J
-- extend wall across both legs. χ preserves quiet.𝒮
namespace Dais
open Tender Turbin Lasso
variable {s:Senses R} {w : Slip (Point (ι⊕α))}{P : Slip (Point α)}(o:α→Site n)
section bounds
local notation "v"=>Sonnet.root s
set_option quotPrecheck false
local notation "M₀"=> (essence s)
variable (h:good s.val P)
local notation "α0"=> h
omit [Fintype α]
include h
lemma attended {i:α} (hv:i∈ essence s) : ∃ z : Cover,(z,i) ∈ P := by
 obtain ⟨b,hb,h'⟩:= List.mem_map.mp (show i∈ P.map Prod.snd from List.mem_toFinset.mp (h.2.symm ▸ hv)); exact ⟨b.1,h' ▸ hb⟩
def position (i:α): Cover:= if H:i∈ essence s then Classical.choose (attended h H) else 0
lemma extant (i:α) (hv:i∈essence s) : (position h i,i) ∈ P:=by rw [position, dif_pos hv]; exact Classical.choose_spec (attended h hv)
variable {i:Point α}
lemma heartbeat (hx:i∈P): i.2∈ essence s:= by unfold essence; rw [← h.2]; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,hx,rfl⟩)
lemma locate (hx:i ∈ P): position h i.2=i.1:=congr_arg Prod.fst (List.inj_on_of_nodup_map (f:=Prod.snd) h.1 (extant h _ (heartbeat h hx)) hx (rfl))
abbrev firstH := position h (Sonnet.root s)
def hold : Bay s where
  pursue i:= if i∈ essence s then position h i-position h (Sonnet.root s) else 0
  starts:= by rw [if_pos (ownership s),sub_self]
  rest i H:=by rw [if_neg H]
local notation "λ0"=> (hold h)
local notation "v0"=> position h (Sonnet.root s)
lemma dispense (i) (hv:i∈essence s) : (hold h).pursue i= position h i-position h (Sonnet.root s):= by unfold hold; simp only [hv,if_true]
-- unique anchor for each finite period.
abbrev there := o (Sonnet.root s)-wrap n (position h (Sonnet.root s))
local notation "q"=> there o h
variable {z:Site n}
lemma right_here(z : Site n): likes P o z ↔ z=there o h ∧ Bay.Hears (hold h) o:= by
 constructor
 · intro hx; have he(i:α)(hv:i∈ essence s):o i=z+wrap n (position h i):=hx _ (extant h i hv); refine ⟨?_,fun i hi=>?_⟩; · unfold there; rw [he (Sonnet.root s) (ownership s),add_sub_cancel_right]
   rw [he i hi,bent, dispense h i hi,map_sub, he _ (ownership s)]; abel
 rintro ⟨hp,hq⟩ i hi; let u:=i.2; let f:=heartbeat h hi; unfold there at hp; rw [hq i.2 f,bent,dispense h _ f,map_sub,locate h hi,hp]; abel
lemma weight_h : P.length=s.val.val.card:= by rw [← h.2,List.toFinset_card_of_nodup (h.1),names,List.length_map]
-- arithmetic cost per displacement
omit h
lemma memo (hx : i∈P) : size i.1 ≤ meter P:= by induction P with
 | nil=> simp at hx
 | cons j P ih=> rcases List.mem_cons.mp hx with H|H; · rw [H]; exact Nat.le_add_right ..
                 exact (ih H).trans (Nat.le_add_left ..)
lemma subtract_size (x y:Cover):size (x-y) ≤ size x+size y := by rw [sub_eq_add_neg]; apply le_trans (size_add ..); rw [size_neg]
include h
lemma cost_pos (i) (hv:i∈ essence s): size (position h i) ≤ meter P:= memo (extant h _ hv)
lemma after_toll : (hold h).tariff≤(essence s).card*(2*meter P):=by
 let M : ℕ:=2* meter P; unfold Bay.tariff; apply le_trans (b:=∑ _∈ essence s,M) (Finset.sum_le_sum ?_); · simp [M]
 intro i hi; rw [dispense h _ hi]; rw [show M=meter P + meter P from (by omega)]; exact le_trans (subtract_size ..) (add_le_add (cost_pos h i hi) (cost_pos h _ (ownership _)))
end bounds
variable (h:good s.val (chain w))(x:rule ι n)
lemma established : (∑ z:Site n, crystal R s.val o (invoice z w) x) = if Bay.Hears (hold h) o then invoice (there o h) (coin w) x else 0:= by
 simp_rw [termwise]; rw [Finset.sum_eq_single (there o h)]; rotate_left
 · intro q hx hp; rw [if_neg]; exact fun h'=> hp ((right_here o h q).mp h'.2).1
 · simp
 symm; split
 next hx=> rw [if_pos (And.intro h ((right_here o h _).mpr ⟨rfl,hx⟩))]
 next hx=> rw [if_neg]; exact fun h'=>hx ((right_here o h _).mp h'.2).2
lemma faded (hp:¬good s.val (chain w)) : (∑ z:Site n, crystal R s.val o (invoice z w) x) =0:= Finset.sum_eq_zero fun i hi=> (termwise x o s.val ..).trans (if_neg fun hh=> hp hh.1) -- arity scroll
omit [Fintype ι][Fintype α][DecidableEq α] in
lemma sum_meter (w : Slip (Point (ι⊕α))) : meter w=meter (chain w)+meter (coin w):= by induction w with | nil=>rfl | cons j w ih=> rcases j with ⟨x,i|i⟩ <;> (first| change _+meter w=meter (chain w)+(size x+meter (coin w))|change _+meter w=size x+meter (chain w)+meter (coin w)) <;> rw [ih] <;> abel
-- peers horizon k: meter d.If r≤κ use r palette
include h
lemma enough (hw:List.length w≤k) : (coin w).length≤ k-(essence s).card:= by have H:=weight_h h; have he:= leaves_length w; unfold essence; omega
end Dais
end YM.Qlocal.Quipu.Eluder
