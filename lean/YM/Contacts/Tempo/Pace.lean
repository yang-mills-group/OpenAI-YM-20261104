import YM.Contacts.Tempo.Hopscotch
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
namespace Grounds
variable (T:Grounds A e S s K k D ζ) {x:Dye G}
local notation "Γ" => terrain ζ (Dye G)
local notation "Η" => terrain (2*ζ) (Dye G)
local notation "η" => bath ζ k (Dye G)
local notation "τ" => hop e s M h
local notation "R" => play h M e s
variable {F P:Sketch G}{V:Badge A.prism→Sketch G}{v:Badge A.prism}
abbrev fixed : Unit→ℕ:=fun _=>0 -- not abbreviation? wrapper
abbrev Course (p:ℕ→ℝ→Prop):=Tempo.Road fixed (fun _=>p)
abbrev Soles [NormedAddCommGroup X](f:ℕ→X):=Tempo.Rates fixed (fun _=>f)
abbrev placed (e:Parcel G)(s:Parcel.Step)(A: Ink G h M) (p:Sketch G)(i:ℕ)(v:Badge A.prism) :ℕ→ℝ := fun n=> v.key (play h M e s p n) M i
-- frame force expression shout depends FULL series V & recurrence
abbrev grindStep (e:Parcel G)(s:Parcel.Step)(A: Ink G h M) (p:Sketch G)(i:ℕ)(v: Badge A.prism):ℕ→ℝ := fun n=> Grounds.shout e s A i n (play h M e s p n) v
abbrev Advance (e:Parcel G)(s:Parcel.Step)(M h D k:ℕ)(ζ:ℝ≥0)(x:Dye G)(p:Sketch G)(i r:ℕ) := Course (fun n=>Harrier.Before (bath ζ k _) D x (play h M e s p n) i r)
structure Graded (e:Parcel G)(s:Parcel.Step)(A:Ink G h M)(D k:ℕ)(ζ:ℝ≥0)(x:Dye G)(p:Sketch G)(i r w:ℕ): Prop where
   living : Living x M D p (2*ζ)
   past' : Advance e s M h D k ζ x p i r
   ready (v:Badge A.prism): v.slot = r→ v.win<w→ Soles (placed e s A p i v)
include T

lemma tollRuns (x:Dye G)(F:Sketch G)(v:Badge A.prism) : Runs (power s A v) (fun _:Unit=>grindStep e s A F i v) (fun _=>placed e s A F i v):= fun _ n=> T.runs x v _ i n -- defeq play
-- preserve lower values on changing fees anywhere with Earlier silence and rank-v keys all zero
lemma shout_shift {z:ℕ}(hp:Living x M D P (2*ζ))(h:Living x M D F (2*ζ))(he:Harrier.Before η D x F i r 0)(hq:i≤K)(hc:∀ v:Badge A.prism,v.slot=r→v.win<z→v.key P M i= v.key (P+F) M i)(hu:v.slot=r)(hv:v.win≤z): shout e s A i n (P+F) v=shout e s A i n P v:= by
    rw [shout,discount_add T x v _ _ h hp] -- argument order check F binder, discount_add hv first!
    rw [show discount e (round s n) s A F i v=0 from T.poor x v h (by rw [hu]; exact he) hq,add_zero,shout]; congr 1; exact (over_eq (e:=e) v (fun w hw=> have ht:= (stress_mem v w).mp hw; hc w (ht.1.trans hu) (lt_of_lt_of_le ht.2 hv))).symm
lemma silences (h:Living x M D F (2*ζ))(he:Harrier.Before η D x F i r 0)(hi:i≤ K) (hq:∀ (v:Badge A.prism), v.slot=r→ v.win< l→ v.key F M i=0)(hp:Living x M D P (2*ζ)) : ∀ n, ∀ (v:Badge A.prism),v.slot=r→v.win< l→ placed e s A P i v n=placed e s A (P+F) i v n:= by
   intro n; induction n with| zero=> intro v hx ht; change v.key P M i=v.key (P+F) M i; rw [v.key_add hp T.ready h,hq v hx ht,add_zero]|succ n ih=>
   intro v hu hv; change v.key (τ n (R P n)) M i = v.key (τ n (R (P+F) n)) M i; rw [T.runs x,T.runs x, show v.key (R P n) M i=v.key (R (P+F) n) M i from ih v hu hv]; congr 1; rw [T.play_add hp h, T.shout_shift (z:=l) (T.own hp _) (T.own h _) (T.pre_echo hi h he) hi ?_ hu hv.le]; intro p ht hw; rw [← T.play_add hp h]; exact ih p ht hw
lemma shout_equal (h:Living x M D F (2*ζ))(he:Harrier.Before η D x F i r 0)(hi:i≤ K) (hq:∀ (v:Badge A.prism), v.slot=r→ v.win< l→ v.key F M i=0)(hp:Living x M D P (2*ζ))(hu:v.slot=r)(hv:v.win ≤ l):grindStep e s A (P+F) i v n = grindStep e s A P i v n:= by unfold grindStep; rw [T.play_add hp h]; exact T.shout_shift (T.own hp _) (T.own h _) (T.pre_echo hi h he) hi (fun v h' ht=> Eq.trans (T.silences h he hi hq hp n v h' ht) (congr_arg (fun V=>v.key V M i) (T.play_add hp h))) hu hv
-- estimating force by Earlier and lower weights consumption.Solve one grade.
lemma Graded.pylon {F:Sketch G}(v:Badge A.prism)(h:Graded e s A D k ζ x F i r l)(hq:v.slot=r)(hv:v.win≤l)(hi:i≤K):Soles (grindStep e s A F i v):= by
    apply T.road_run x v (hi:=hi) (W:=fun _:Unit=>R F) (fun _ i=>T.own h.living _) (by rw [hq]; exact h.past'); intro w hw; obtain ⟨hw,h'⟩:= (stress_mem v w).mp hw; exact h.ready w (hw.trans hq) (lt_of_lt_of_le h' hv)
lemma advanceRide (h':Advance e s M h D k ζ x P i r)(hx:Living x M D F (2*ζ))(hy:Living x M D P (2*ζ))(hz:Harrier.Before η D x F i r 0) (hi:i≤ K):Advance e s M h D k ζ x (P+F) i r:= by
   refine Road.fall h' fun _ n b hb hn=>?_ ; change Harrier.Before η D x (R (P+F) n) _ _ b; rw [T.play_add hy hx]; exact (add_zero b) ▸ before_add hn (T.pre_echo hi hx hz)
end Grounds
end
end YM.Contacts.Tempo
