import YM.Contacts.Tempo.Blues
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
def Former (g:Grant A)(i r:ℕ):Prop:= ∀ (u:Badge A.prism),u.win<h→∀ j:ℕ, Past i r j u.slot→ g u j=0
include H
variable {K':ℕ}{z: Grant A}(hx:Former z i r)
lemma sector_thin (he:i<j)(u:Badge A.prism) : Harrier.Before η D x (surge (V u) j) i r 0:= by
   intro p n hp; rw [Enroll,show Harrier.sail (surge (V u) j) p n=0 from ?_]; exact w_zero; funext φ; unfold Harrier.sail surge shiftA; rw [if_neg (by unfold Past at hp; omega)]; rfl
include hx
lemma past_ed : Harrier.Before η D x (Edited A V K' z) i r 0:= by
   refine (before_sum (b:=fun _=> ∑ _∈Finset.Iic K',(0:ℝ)) (ground A) (fun v hv=>before_sum (Finset.Iic K') (?_))).mon (by simp only [Finset.sum_const_zero,le_refl]); intro j hj; by_cases hc:Past i r j v.slot; · rw [hx v (mem_filter.mp hv).2 j hc,zero_smul]; exact fun p n h=> w_zero
   refine mul_zero ‖z v j‖ ▸ before_scale _ (?_); by_cases ht:j=i; · rw [ht]; exact H.past_blank (by unfold Past at hc; omega)
   exact sector_thin H (by unfold Past at hc; omega) v
variable {v u:Badge A.prism}(ht:v.slot=r)(hu:v.win<h) -- include hx?
include T ht
lemma key_blank (he:r > u.slot) : v.key (surge (V u) i) M i=0:= by
    obtain ⟨a,ha,A'⟩:= Pocket.key_exp i r (D:=D) v T.lic.light ht (ht ▸ second A v); have hh:=H.home u;
    have hV:= A' x (surge (V u) i) ((hh.surgeM i).lower T.lic.down) 0 le_rfl (issued_down ((H.past_blank (ζ:=ζ) (k:=k) le_rfl).earlier (Or.inr ⟨rfl,he⟩)));
    rw [mul_zero,norm_le_zero_iff] at hV; exact hV
include hu
lemma dust_atom (hi:i≤K') (he:∀ u:Badge A.prism,u.slot=r→u.win<v.win→z u i=0) : v.key (Edited A V K' z) M i=z v i:= by
    let U (v:Badge A.prism)(j:ℕ):=z v j • surge (V v) j; let X:= Finset.Iic K'; let P(v):=∑ j∈X,U v j; let Y(w:Badge A.prism)(j:ℕ):= v.key (surge (V w) j) M i; have H₁(v j): Living x M D (U v j) (2*ζ):=((H.home v).surgeM _).scale _; have hQ (w: Badge A.prism)(hv:w∈ground A): v.key (P w) M i=z w i*Y w i:= by
       unfold P; rw [v.key_many T.ready _ (fun j _=> H₁ w j)]; rw [Finset.sum_eq_single i]; rotate_left;
       · intro k hk he; unfold U; rw [v.key_scale ((H.home w).surgeM _) T.ready]; by_cases hc:k< i; · rw [hx w (mem_filter.mp hv).2 k (.inl hc),zero_mul]
         rw [show v.key (surge (V w) k) M i=0 from (by unfold Badge.key surge; rw [fill_shift _ ((H.home w).lineage v.phi) T.ready,if_neg (by omega)]),mul_zero]
       · simp [X,hi]
       exact v.key_scale ((H.home w).surgeM _) T.ready _
    unfold Edited; rw [v.key_many T.ready (ground A) (fun j _=> Living.sum X (fun p _=> H₁ j p)),Finset.sum_eq_single v]; rotate_left;
    · intro p hp hh; change v.key (P p) M i=_; rw [hQ p hp]; by_cases h:p.slot=r;
      · by_cases hk:p.win<v.win; · rw [he p h hk, zero_mul]
        rw [show Y p i=0 from (blink T H v p (ht.trans h.symm) (not_lt.mp hk)).trans (if_neg (Ne.symm hh)),mul_zero]
      rcases lt_or_gt_of_ne h with he|he; · rw [show Y p i=0 from (key_blank T H hx ht he),mul_zero]
      rw [hx p (mem_filter.mp hp).2 i (.inr ⟨rfl,he⟩),zero_mul]
    · simp [ground,hu]
    change v.key (P v) M i= _; rw [hQ v (mem_filter.mpr ⟨mem_univ _,hu⟩), show Y v i=1 from (blink T H v v rfl le_rfl).trans (if_pos rfl),mul_one]
-- general inversion condition, compatible with $top-V$ purity at the rank via silence Lemma.Cp.
omit hu ht
lemma roundVoid (B:Sketch G) (hB: Living x M D B (2*ζ)) (hB':Harrier.Before η D x B i r 0) (hq:∀ u:Badge A.prism,u.slot=r→u.win<h→u.key B M i=0)(ht:Critical e s M h D k ζ x (B + Edited A V K' z) K) (he:i ≤ K)(hv:i≤K'):∀ u:Badge A.prism,u.slot=r→u.win<h→z u i=0:= by
    let Y:= Edited A V K' z; have he':Harrier.Before η D x (B+Y) i r 0:= add_zero (0:ℝ) ▸ before_add hB' (past_ed H hx); have ht' (u:Badge A.prism)(hp:u.slot=r)(hh:u.win<h) : u.key (B+Y) M i=0:= Critical.hush T ht he he' u hp hh 0; let X(l:ℕ):=∀ u:Badge A.prism,u.slot=r→u.win=l→ l<h→ z u i=0; suffices hx':∀ l,X l by exact fun u hu hv=> hx' u.win u hu rfl hv
    intro l; induction l using Nat.strong_induction_on with|h l ih=>
    intro u hp hQ hh; have hg:= hQ.trans_lt hh; have h₀:= ht' u hp hg; rw [u.key_add hB T.ready (H.financed (show Held A V K' Y from ⟨z,rfl⟩)),hq u hp hg,zero_add] at h₀; exact (dust_atom T H hx hp hg hv (fun v hv he=>ih v.win (he.trans_eq hQ) v hv rfl (he.trans hg))).symm.trans h₀
end Prospect
end Grounds
end
end YM.Contacts.Tempo
