import YM.Contacts.Tempo.Pace
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
variable (hc:Prospect A D x (2*ζ) V)(hi:i≤K)
local notation "♮" => power s A
local notation "Ω" => placed e s A
local notation "Υ+" => grindStep e s A
local notation "♭" => Graded e s A D k ζ x
-- shock gravity vs growth.Distinct weights: tune one top stratum. SΔ.
include T hc hi
namespace Prospect
lemma rowStep (h':♭ P i r l)(he:l<h) : ∃ f:Sketch G,Held A V K f ∧ ♭ (P+f) i r (l+1):= by
   let X(v:Badge A.prism): Unit→ℕ→ℝ:=fun _=>grindStep e s A P i v; let Y(w:Badge A.prism):= gain (power s A w) (X w); let β(w:Badge A.prism):=Y w () 0-w.key P M i
   let F:= Grounds.beat A V i r l β; have hF: Living x M D F (2*ζ):= hc.beats_health β; have hy :Harrier.Before η D x F i r 0:= hc.volume_mute β; let W:= P+F; let heP:=h'.living; let hp:= h'.past'; have H (v:Badge A.prism) (hu:v.slot=r)(hv:v.win<l) : v.key F M i=0:= (Prospect.aural T hc β v hv.le hu).trans (if_neg (ne_of_lt hv));
   refine ⟨F, beat_paid β hi he, heP.add hF, advanceRide T hp hF heP hy hi, fun v hx hu=>?_⟩; by_cases hk:v.win<l
   · have h : placed e s A P i v = placed e s A W i v:= funext fun n=>T.silences hF hy hi H heP n v hx hk; change Soles (placed e s A W i v); rw [←h]; exact h'.ready v hx hk
   have hv : v.win=l:= by omega
   let Q:= Y v; obtain ⟨hV,hQ⟩:= Rates.prices (f:=X v) (Graded.pylon T v h' hx hv.le hi) (stress_cut s v (hv.trans_lt he)); let f:= Ω W i v; have hp : f= Q ():= by
       funext j; induction j with|zero=>change v.key (P+F) M i=_; rw [v.key_add heP T.ready hF,show v.key F M i=β v from (Prospect.aural T hc β v hv.le hx).trans (if_pos hv)]; unfold β Q; ring|succ j ih=>
       rw [show f (j+1)=♮ v*f j+ Υ+ (P+F) i v j from T.tollRuns x (P+F) v () j,ih,T.shout_equal hF hy hi H heP hx hv.le,show Q () (j+1)=♮ v*Q () j+Υ+ P i v j from hQ () j] -- may def opaque
   change Soles f; rw [hp]; exact hV
omit T hc
-- sum iterations across all weights.S_` . We don't assert equality of different choices of continuation widths on retuned sources here.
include T hc
lemma through (h':Living x M D F (2*ζ))(he:Advance e s M h D k ζ x F i r)(l:ℕ)(hl:l≤h):∃ P:Sketch G,Held A V K P∧ ♭ (F+P) i r l:= by
   induction l with|zero=>exact ⟨0,Held.free,(add_zero F).symm ▸ ⟨h',he,fun _ _ hh=>by omega⟩⟩|succ l ih=> obtain ⟨P,hP,GX⟩:= ih (by omega); obtain ⟨Q,hQ,Y⟩:= rowStep T hc hi GX (by omega); exact ⟨P+Q,hP.plus hQ,add_assoc F P Q ▸ Y⟩
omit hc in
lemma current (h':♭ P i r h): ∀ v:Badge A.prism, v.slot=r→Soles (Ω P i v):= by
   intro v hv; by_cases hx:v.win<h; · exact h'.ready v hv hx
   have hw:v.win=h:= le_antisymm v.win_le (le_of_not_gt hx); let f:= Ω P i v; exact Rates.neutral (Graded.pylon T v h' hv v.win_le hi) (a:=‖f 0‖) (fun _=> le_rfl) (norm_nonneg _) (bright v s hw ▸ T.tollRuns x _ v)
-- consume one bath slot using prior and *all* calibrated q, with mark top polynomial bounds
section obtains
omit hc
lemma results (h':♭ P i r h) (hr:r≤ M+i) : Course (fun n=>Issued η D x (R P n) i r):= by
   let P':= fun (_:Unit) n (b:ℝ)=> ∀ v:Badge A.prism,v.slot=r→‖placed e s A P i v n‖≤ b; let Q:= Transfer.points A r; let Z:=fun n=> R P n; let U:=fun n=> Harrier.Before η D x (Z n) i r; let Y:=fun n=> Enroll η D x (Z n) i r; have hZ(n):= T.own h'.living n; have hU:Rising (fun (_:Unit) n=> U n):= fun _ _ _ _ h he=> Harrier.Before.mon he h; have hY:Rising (fun (_:Unit) n=> Y n):= fun _ _ _ _ h he=> w_raise he h;
   refine Road.joint h'.past' (P:=fun (_:Unit) n=> U n) (Q:=fun (_:Unit) n=> Y n) (?_) hU hY; have hs:Road fixed P':= by apply (Road.many (Y:=fun v (_:Unit) j (b:ℝ)=> ‖Ω P i v j‖≤b) Q (fun v hv=>current T hi h' v (mem_filter.mp hv).2) (fun _ _ _ _ _ _ h he=> he.trans h)).fall; intro _ _ _ _ hh v hv; exact hh v (mem_filter.mpr ⟨mem_univ _,hv⟩)
   let R':= Road.joint h'.past' (P:=fun (_:Unit) n=> U n) hs hU (fun _ _ _ _ h he p hx=> (he p hx).trans h); obtain ⟨d,b,hb,B⟩:=R'; obtain ⟨a,ha,A'⟩:= Transfer.foothold T.lic T.steps x A hi T.center T.amount T.count T.market T.cap hr
   obtain ⟨z,hz,hWZ⟩:= h'.living.budget i r; let t:= fit_spare (2*ζ) ζ k T.lic.emit_lt; have hv:0 ≤ t.choose:= zero_le_one.trans t.choose_spec.1;
   apply contract (P:=fun (_:Unit) n=>Y n) (c:=1/4) (by norm_num) (by norm_num) (d:=d) (b:=a*b) (mul_nonneg ha hb) (a:=t.choose*z) (mul_nonneg hv hz ) hY (fun _=> w_raise (spa_weight T.lic.light hWZ) (le_mul_of_one_le_right (mul_nonneg hv hz) (toll_good ..))) (?_); intro z j u hu H; let p:=b*toll 0 j d; have hp:0≤ p:=mul_nonneg hb (toll_glow ..).le; exact w_raise (A' _ (T.in_path j) _ ((T.own h'.living _).lower T.lic.down) p hp ((B () j).1.lower) (B () j).2 u hu H) (le_of_eq (by unfold fixed p; ring))
end obtains
end Prospect
end Grounds
end
end YM.Contacts.Tempo
