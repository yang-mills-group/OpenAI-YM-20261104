import YM.Contacts.Tempo.Hunt
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
local notation "ℒ" => (2*ζ:ℝ≥0)
abbrev Rolling (e:Parcel G)(s:Parcel.Step)(M h D k:ℕ)(ζ:ℝ≥0)(x:Dye G)(F:Sketch G)(i r:ℕ):Prop:= Course (fun n=> Issued (bath ζ k _) D x (play h M e s F n) i r)
local notation "Λ" => Rolling e s M h D k ζ x
-- rank & primary stage iteration, including no-candidate-when-offset zeros. same occupancy.
lemma roll_earlier (H: Λ F i r)(he: Past i r n l): Λ F n l:= Road.fall H (fun _ j _ _ h=>h.1.earlier he ) -- Issued abbrev
lemma roll_same (H:Λ F i 0)(r:ℕ): Λ F i r:= by
    rcases Nat.eq_zero_or_pos r with hr|hr; · rw [hr]; exact H
    exact roll_earlier H (Or.inr ⟨rfl,hr⟩)
lemma roll_next (H:Λ F i (r+1)): Advance e s M h D k ζ x F i r:= by refine Road.fall H (fun _ _ _ hb H a l he=>?_); by_cases hp:a=i∧l=r+1; obtain ⟨ha,hl⟩:=hp; rw [ha,hl]; exact H.2; exact H.1 a l (by unfold Past at *; omega)
include T
lemma roll_up (H: Λ F i 0)(hx:Living x M D F (2*ζ)): Advance e s M h D k ζ x F (i+1) (M+(i+1)):= by
    refine Road.fall H (?_); intro _ n b hb H a j he; by_cases hp:a=i+1; · subst a; exact clean_stop _ (T.own hx n) (by unfold Past at he; omega) b hb
    by_cases ht:a=i∧j=0; obtain ⟨rfl,rfl⟩:=ht; exact H.2; exact H.1 _ _ (by unfold Past at *; omega)
variable (hc:Prospect A D x (2*ζ) V)
include hc
lemma roll_one (hi:i≤K)(H:Advance e s M h D k ζ x F i r)(hr:r≤ M+i)(hx:Living x M D F (2*ζ)): ∃ P:Sketch G,Held A V K P ∧ Λ (F+P) i r := by obtain ⟨P,hP,Y⟩:= Prospect.through T hc hi hx H h le_rfl; exact ⟨P,hP,Prospect.results T hi Y hr⟩
lemma roll_all (hi:i≤K)(H:Advance e s M h D k ζ x F i r)(hr:r≤M+i)(hx:Living x M D F (2*ζ)):∃ P:Sketch G,Held A V K P∧ Λ (F+P) i 0:= by
    induction r generalizing F with| zero=> exact roll_one T hc hi H hr hx|succ r ih=>
    obtain ⟨P,hP,Y⟩:= roll_one T hc hi H hr hx; obtain ⟨V,hV,Z⟩:= ih (roll_next Y) (by omega) (hx.add (hc.financed hP)); exact ⟨P+V,hP.plus hV,add_assoc F P V ▸ Z⟩
lemma roll_grade (hx:Living x M D F (2*ζ))(hi:i≤K):∃ P: Sketch G,Held A V K P ∧ Λ (F+P) i 0:= by
    induction i with| succ k ih=> obtain ⟨P,hP,Y⟩:= ih (by omega); have hh:= hx.add (hc.financed hP); obtain ⟨U,hU,Z⟩:= roll_all T hc hi (T.roll_up Y hh) le_rfl hh; exact ⟨P+U,hP.plus hU, add_assoc F P U ▸ Z⟩|zero=>
    apply roll_all T hc hi (r:=M) _ (Nat.le_add_right ..) hx; refine Road.by_zero (P:=fun (_:Unit) p=> Harrier.Before η D x (R F p) 0 M) (fun _ _ _ _ h H=>Harrier.Before.mon H h) ?_; intro _ i j l hj; have he:j=0:= by unfold Past at hj; omega
    subst j; exact clean_stop _ (T.own hx i) (by unfold Past at hj; omega) 0 le_rfl
-- principal statement at fixed rung.Hardware.Lift.Param.Frame_N` as above. Full on oath for any label field at that horizon, provided occupancy (not theorem reducing test order!).
structure Critical (e:Parcel G)(s:Parcel.Step)(M h D k:ℕ)(ζ:ℝ≥0)(x:Dye G)(P:Sketch G)(K:ℕ): Prop where
   life : Living x M D P (2*ζ)
   rolling i r (he:i≤ K) : Rolling e s M h D k ζ x P i r
variable (hx:Living x M D F (2*ζ))
include hx
theorem critical : ∃ g: Grant A,Critical e s M h D k ζ x (F+Edited A V K g) K:= by
   obtain ⟨P,hP,Y⟩:= T.roll_grade hc hx (le_refl K); have H:=hx.add (hc.financed hP); obtain ⟨g,rfl⟩:= hP; refine ⟨g,H,fun i r he=>?_⟩; by_cases ht:i=K; · subst i; exact roll_same Y r
   exact roll_earlier Y (Or.inl (by omega))
end Grounds
end
end YM.Contacts.Tempo
