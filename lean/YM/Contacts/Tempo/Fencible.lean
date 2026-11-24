import YM.Contacts.Tempo.Eraser
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
namespace Prospect
variable (H:Prospect A D x (2*ζ) V)
variable {K':ℕ}{z f g:Grant A} (hi:i ≤ K)(he:i≤K')(hc:Critical e s M h D k ζ x (F+Edited A V K' z) K)
include T
omit H hi he hc in -- not included yet?
lemma nail {u:Badge A.prism}(hn: Living x M D F (2*ζ))(hx:u.slot=r)(hy:Issued η D x F i r 0) : u.key F M i=0:= by
    obtain ⟨a,ha,A'⟩:= Pocket.key_exp i r (D:=D) u T.lic.light hx (hx ▸ second A u); have hv:= A' x F (hn.lower T.lic.down) 0 le_rfl (issued_down hy); rwa [mul_zero,norm_le_zero_iff] at hv
include H hi he hc
lemma fence (hF:Living x M D F (2*ζ))(hX: Harrier.Before η D x F i r 0)(hq:∀ v:Badge A.prism,v.slot=r→v.win<h→ v.key F M i=0)(hu:Former z i M) (hk:r≤M): Former z i r ∧ ∀ v:Badge A.prism,v.slot=r→v.win<h→z v i=0:= by
    have ht(j:ℕ)(hj:j+r ≤ M) : Former z i (M-j):= by
        induction j with| zero=>exact hu|succ j ih=>
        let m:= M-j; have hh:r< m:= (by unfold m; omega); have hs:m-1=M-(j+1):= (by unfold m; omega); have hM:Former z i m:= ih (by omega); let Q:= hX.earlier (show Past i r i m from Or.inr ⟨rfl,hh⟩); let Y:= roundVoid T H hM F hF Q.1 (fun _ h _=> Prospect.nail T hF h Q) hc hi he; intro v hv i' ht; by_cases ha:i'=i ∧ v.slot=m; · obtain ⟨hp,h'⟩:=ha; rw [hp]; exact Y v h' hv
        exact hM v hv i' (by unfold Past at *; omega)
    have hv:Former z i r:= (show M-(M-r)=r from by omega) ▸ ht (M-r) (by omega); exact ⟨hv, roundVoid T H hv F hF hX hq hc hi he⟩
omit hi he hc
-- uniqueness works also through different overall horizons provided same means defined and enough at requested lease
lemma edits (hs: Critical e s M h D k ζ x (Edited A V K' z) K)(hi:i≤K)(he:i≤K'):∀ v:Badge A.prism, v.win<h→ z v i=0 := by -- shadows h
   induction i using Nat.strong_induction_on with| h i ih=>
   have hx: Former z i M:= fun v hv j hj=> by have hh: j< i:= (by have he:= second A v; unfold Past at hj; omega); exact ih _ hh (le_trans (le_of_lt hh) hi) (le_trans (le_of_lt hh) he) v hv; -- might parse scope
   intro v hv; refine (fence T H hi he ((zero_add (Edited A V K' z)).symm ▸ hs) (F:=0) (Living.zero x M D) (r:=v.slot) (fun _ _ _=> w_zero) ?_ hx (second A v)).2 v rfl hv; intro u hu hh; exact fill_null A.prism x ..
lemma unique (hc: Critical e s M h D k ζ x (F+Edited A V K' f) K) (ht: Critical e s M h D k ζ x (F+Edited A V K' g) K) (hi:i≤K)(he:i≤K') :∀ u:Badge A.prism,u.win<h→f u i=g u i:= by
   let v:= Edited A V K'; have he': v (f-g)=(F+v f)-(F+v g):= by rw [show v (f-g)=v f-v g from Edited.minus]; abel
   intro p hp; exact sub_eq_zero.mp (edits T H (he'.symm ▸ Critical.both_sub T hc ht) hi he p hp)
-- B candidate neutral leading purity and consequent edit vanishing at leading ranks. CP script.
variable {y:Badge A.prism}(hq:y.win=h)
omit T in
lemma leading : Harrier.Before η D x (V y) 0 y.slot 0:= by
    intro i j hi; rw [Enroll,show Harrier.sail (V y) i j=0 from funext (fun p=>?_ )]; exact w_zero; unfold Harrier.sail; rw [show i=0 from by unfold Past at hi; omega]; exact H.thin y j (by unfold Past at hi; omega) p
omit T in
lemma from_zeroEd (hu:Former z 0 r)(hg:∀ u:Badge A.prism,u.slot=r→u.win<h→z u 0=0) : Issued η D x (Edited A V K' z) 0 r 0 := by
    refine ⟨past_ed H hu,?_⟩; rw [Enroll,Edited,sum_sail,show (∑ v∈ground A,Harrier.sail (∑ i∈Finset.Iic K',z v i • surge (V v) i) 0 r)=0 from ?_]; exact w_zero; apply Finset.sum_eq_zero; intro v hv; rw [sum_sail]; apply Finset.sum_eq_zero; intro i hi; by_cases he:i=0
    · subst i; by_cases ht:v.slot<r; · funext φ; change z v 0 • shiftA 0 (V v φ) 0 r=0; unfold shiftA; rw [if_pos le_rfl,Nat.sub_self,H.thin v _ ht,smul_zero]
      by_cases hh:v.slot=r; · rw [hg v hh (mem_filter.mp hv).2,zero_smul]; rfl
      rw [hu v (mem_filter.mp hv).2 0 (.inr ⟨rfl,by omega⟩),zero_smul]; rfl
    funext φ; change z v i • shiftA i (V v φ) 0 r=0; unfold shiftA; rw [if_neg (by omega)]; exact smul_zero _
include hq
theorem drawn (h':Critical e s M h D k ζ x (V y + Edited A V K' z) K) :
     let Y:=play h M e s (V y+ Edited A V K' z);
     (∀ n,Harrier.Before η D x (Y n) 0 y.slot 0) ∧ ∀ n,∀ v: Badge A.prism, y.slot ≤ v.slot→ v.key (Y n) M 0= if v=y then 1 else 0:= by
   intro Y; let F:= Edited A V K' z; let p:= V y+F; have hz:∀ u:Badge A.prism,u.slot=y.slot→u.win < h→ u.key (V y) M 0=0:= fun u he hx=> by rw [H.push y u he.symm (by omega),if_neg]; intro ht; rw [ht] at hx; omega; -- parse
   obtain ⟨hp,hX⟩:= fence T H (K':=K') (Nat.zero_le K) (Nat.zero_le K') h' (H.home y) (H.leading (y:=y)) hz (fun u h i he=> by have hh:= second A u; unfold Past at he; omega) (second A y); have hc: Issued η D x F 0 y.slot 0:= from_zeroEd H hp hX; have hC:Harrier.Before η D x p 0 y.slot 0:= add_zero (0:ℝ) ▸ before_add H.leading hc.1; let H' n:= T.pre_echo (n:=n) (Nat.zero_le K) (F:=p) h'.life hC; refine ⟨H',fun n v hv=>?_⟩; by_cases he:y.slot=v.slot;
   · have he':v.win≤y.win:= v.win_le.trans_eq hq.symm; by_cases hu:v.win=h; · rw [show v.key (Y n) M 0=v.key p M 0 from Critical.solo T h' (Nat.zero_le K) hC v he.symm hu n, v.key_add (P:=F) (H.home y) T.ready (H.financed (show Held A V K' F from ⟨z,rfl⟩)), Prospect.nail T (H.financed (show Held A V K' F from ⟨z,rfl⟩)) he.symm hc, H.push y v he he',add_zero]
     have hh:v.win < h:= lt_of_le_of_ne v.win_le hu; exact (Critical.hush T h' (Nat.zero_le K) hC v he.symm hh n).trans (if_neg (fun h:v=y => hu ((congr_arg Badge.win h).trans hq))).symm
   rw [if_neg (fun h=> he (congr_arg Badge.slot h.symm))]; exact Prospect.nail T (T.own h'.life _) rfl ((H' n).earlier (Or.inr ⟨rfl,lt_of_le_of_ne hv he⟩))
end Prospect
end Grounds
end
end YM.Contacts.Tempo
