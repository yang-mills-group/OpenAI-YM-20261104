import YM.Contacts.Tempo.Hall
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
variable (u:Badge A.prism) (v:Badge A.prism→ℝ) {F V:Sketch G}
def stress (u:Badge A.prism): Finset (Badge A.prism):=(Transfer.points A u.slot).filter (fun w:Badge A.prism=>w.win<u.win)
abbrev power (s:Parcel.Step)(A:Ink G h M)(u:Badge A.prism): ℝ:= (s.L.val:ℝ) ^ (h-u.win)
def overdrive (e:Parcel G)(s:Parcel.Step)(A: Ink G h M)(n:ℕ)(u:Badge A.prism)(f:Badge A.prism→ℝ) := ∑ i∈stress u, f i*graph e (round s n) s A u i
-- overwrite of coordinate at index i charge, key excludes higher weights. Cast serials later.
def shout (e: Parcel G)(s:Parcel.Step)(A: Ink G h M)(i n:ℕ)(F:Sketch G)(u:Badge A.prism):ℝ := overdrive e s A n u (fun w=>w.key F M i)+Transfer.discount e (round s n) s A F i u
lemma stress_mem (w:Badge A.prism) : w∈stress u ↔ w.slot=u.slot ∧ w.win<u.win:= by rw [stress,mem_filter,Transfer.points,mem_filter]; simp [Finset.mem_univ]
lemma stress_cut (s:Parcel.Step)(u:Badge A.prism)(he:u.win < h):1< power s A u:= one_lt_pow₀ (by exact_mod_cast (show 1 < s.L.val from by have h:=s.prod; omega)) (by omega)
lemma bright (s:Parcel.Step)(h':u.win=h):power s A u=1:= by unfold power; rw [h',Nat.sub_self,pow_zero]
include T
variable (x)
include x
lemma row (n:ℕ): pushMatrix e (round s n) s A v u=power s A u * v u + overdrive e s A n u v := by
   let U:= Transfer.points A u.slot; let p:= round s n; let W(w:Badge A.prism):=graph e p s A u w; let f(w:Badge A.prism):= v w*W w; let X(w:Badge A.prism):= w.win < u.win; let P:=U.filter X; let Q:=U.filter (fun i=> ¬ X i); have he:(∑ i∈P,f i)+(∑ i∈Q,f i)=∑ i∈U,f i:=Finset.sum_filter_add_sum_filter_not ..; have ha:= T.in_path n; have hx (w:Badge A.prism)(hw:w∈Q): W w=if u=w then power s A w else 0:= triangle T.lic ha T.steps x A u w T.south T.home T.center ((mem_filter.mp (mem_filter.mp hw).1).2.symm) (not_lt.mp (mem_filter.mp hw).2)
   change (∑ i∈U,f i)=_ + (∑ i∈P,f i); rw [←he,add_comm]; congr 1; have hu:u∈Q:= mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,rfl⟩,lt_irrefl _⟩; rw [Finset.sum_eq_single u]; rotate_left; · intro w hw h'; unfold f; rw [hx w hw,if_neg (Ne.symm h'),mul_zero]
   · intro w; exact (w hu).elim
   unfold f; rw [hx u hu,if_pos rfl,mul_comm]
omit T x
lemma over_eq {P Q:Badge A.prism→ℝ}(hx:∀ w∈stress u,P w=Q w): overdrive e s A n u P= overdrive e s A n u Q:= by unfold overdrive; exact Finset.sum_congr rfl fun w hw=> by rw [hx w hw]
include T x
lemma runs (F:Sketch G) (i n:ℕ): u.key (τ n F) M i=power s A u*u.key F M i+shout e s A i n F u:= by rw [shout,discount,T.row x u]; unfold hop; ring
lemma discount_add (n i:ℕ)(hv:Living x M D V (2*ζ))(he:Living x M D F (2*ζ)): Transfer.discount e (round s n) s A (F+V) i u= Transfer.discount e (round s n) s A F i u + Transfer.discount e (round s n) s A V i u:= by
    let w:= round s n; let H:= he.lower T.lic.down; let P:= hv.lower T.lic.down; unfold Transfer.discount; rw [means_add T.lic T.steps x h (T.in_path n) H P,u.key_add (T.roof H) T.ready (T.roof P)]; unfold pushMatrix; simp_rw [Badge.key_add _ he T.ready hv,add_mul,Finset.sum_add_distrib]; abel
lemma poor (he:Living x M D F (2*ζ))(hp:Harrier.Before η D x F i u.slot 0)(hi:i≤ K) : Transfer.discount e (round s n) s A F i u=0:= by obtain ⟨c,hc,C⟩:= Transfer.depression T.lic T.steps x A u T.south hi T.center T.home; have hv:= C (round s n) (T.in_path n) F (he.lower T.lic.down) 0 le_rfl hp.lower; rw [mul_zero,norm_le_zero_iff] at hv; exact hv
variable {W:κ→ℕ→Sketch G}{m:κ→ℕ} (hi:i≤ K)
include hi
lemma road_run (h':∀p j, Living x M D (W p j) (2*ζ))(hq:Road m (fun p j b=> Harrier.Before η D x (W p j) i u.slot b))(he:∀ w∈stress u, Rates m (fun p j=>w.key (W p j) M i)):Rates m (fun p j=>shout e s A i j (W p j) u):= by
   refine Rates.add (Rates.sum (stress u) ?_) ?_; rotate_left; · obtain ⟨c,hc,C⟩:=Transfer.depression T.lic T.steps x A u T.south hi T.center T.home; exact hq.up (fun p j b hb h=> C _ (T.in_path j) _ ((h' p j).lower T.lic.down) b hb h.lower) hc
   intro p hp; obtain ⟨c,hc,C,Z⟩:= T.graph_bill x u p ((stress_mem u p|>.mp hp).1.symm); exact (he p hp).mul (Rates.constant hc (fun _ j=> C (round s j) (T.in_path j)))
end Grounds
end
end YM.Contacts.Tempo
