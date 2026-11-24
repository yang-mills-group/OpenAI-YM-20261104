import YM.Contacts.Harrier.Much
import YM.Contacts.Harrier.Clover
import YM.Contacts.Prairie.Basin
namespace YM.Contacts.Harrier
open Function Set Filter Lattice RG Wilson Precision Stationary Exterior Matrix Laurent
open Pulse Pulse.Spine Origin Shuttle Finset Bloch MergeProof Push.AbsoluteSums Extra.Iteration Work.F08 Next.Free Extension.UV.Linear
open Milling Milling.Steam Milling.Forge Pulse.Form Kale Garf PertExtension.Series Radial Larch Ion Convoy Lumen Resetter Shuttle.Tide
open Procession Procession.Welcome Procession.Catch Procession.Sun Procession.Lotus Procession.Hinges Procession.Xenon
open Shuttle.Pigment Prairie
open scoped Classical Topology BigOperators NNReal Matrix ContDiff Matrix.Norms.Frobenius
noncomputable section
variable {G:Gauge}{b c d g:ℝ}{X Y A B ι κ α β: Type}{m:Side}{n k h i r l j M D:ℕ}{ζ σ:ℝ≥0}
namespace Transfer
open Parcel Prairie Planned.PrimaryIntegral295
variable {e:Parcel G} {p:Word}{s:Parcel.Step}{S:Boom} (T:e.License S ζ)(hp:OK S p)(hs:s∈S)
-- uniform Lip transmission for $s; both pointwise arbitrary signatures and across different coarsening counts. not estimates uniform L.
variable {D':ℕ}(hh:enough (e.floorGoal 3 D') S)
include hs T
local notation "η" => 2*ζ
lemma mintCandy : Climb S (terrain η (Option (e.White s))) (fun p=> plane (candy (e.raw p s))):= by
   obtain ⟨v,hv,h⟩:=T.base _ hs; obtain ⟨b,hb,h'⟩:= T.pairs _ hs; let X:= Option (e.White s); let a:ℝ:= Fintype.card X; have ha:0≤a:=Nat.cast_nonneg _; refine ⟨⟨_,mul_nonneg ha hv,fun i _=>?_⟩,_,mul_nonneg ha hb,fun p q u hp hq hu=>?_⟩
   · let hL:= line_shape (S:=e.flag s) (brace _ (h i).direct hv) hv; let he:= flight_stem (candy_leaf (σ:=η) hL hv) hv; exact ⟨he.left,he.rows,he.columns⟩
   let U p:=candy (e.raw p s); let Z p:=e.Cov p s; let W:=minusRows (U (u++p)) (U (u++q)); let V:=minusRows (Z (u++p)) (Z (u++q)); let H:=b*mileage u; have hw: W=candy (axisLine G (e.flag s) (prom V)) := by rw [show prom V= _ from Eq.symm (prom_diff (P:=e.flag s) ..)]; ext i j v; cases i<;>cases j <;> first| (simp [U,W,Parcel.raw,axisLine,minusRows,candy]); done | skip; rename_i i j; rcases i with i|i <;> rcases j with j|j <;> first| rfl |simp [U,W,Parcel.raw,axisLine,minusRows,candy]
   -- fix after
   have hy:0≤ H:=mul_nonneg hb (mileage_pos _).le; let hk:= flight_stem (candy_leaf (σ:=η) (line_shape (S:=e.flag s) (brace V (h' _ _ u hu).direct hy) hy) hy) hy; change Pulse.Track _ (plane W) _; rw [hw,mul_assoc]; exact ⟨hk.left,hk.rows,hk.columns⟩
lemma mintBeam : Threads S (tunnel (α:=Option (e.White s)) (β:=Option (Dye G)) η) (fun p=>plane (piece (e.beam p s))):= by
   obtain ⟨v,hv,h⟩:=T.base _ hs; obtain ⟨b,hb,h'⟩:=T.pairs _ hs; let a:ℝ:= Fintype.card (Option (Dye G)); let f:ℝ:= Fintype.card (Option (e.White s)); have ha:0≤a:= Nat.cast_nonneg _; have hf:0≤f:= Nat.cast_nonneg _; let w:=1+v; have hw:= add_nonneg zero_le_one hv
   refine ⟨⟨_,mul_nonneg (add_nonneg hf ha) hw, fun p h'=> Barrage.Reserve.weir_up (flight_stem (piece_leaf (σ:=η) (sky_shape (U:=e.A p s) (h p).feed hv) (le_add_of_nonneg_right hv)) hw) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ha) hw) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hf) hw) ⟩,_,mul_nonneg (add_nonneg hf ha) hb,fun p q u hi hj hk=>?_⟩
   let y:=b*mileage u; have hy:0 ≤ y:=mul_nonneg hb (mileage_pos _).le; let Y:=minusRows (e.beam (u++p) s) (e.beam (u++q) s); have he : Y.strip (2*ζ:ℝ≥0) y:= by
      rintro (x|x) j; · simp [Width,Y,Parcel.beam,axisSky,minusRows]; exact budget_loosen budget_zero hy
      exact (h' p q u hk).flow x j
   let X:=minusRows (piece (e.beam (u++p) s)) (piece (e.beam (u++q) s)); have hX : X=candy Y:= by ext i j k; cases i <;>cases j<;> first| rfl| simp [X,candy,piece,minusRows]
   change Weirs _ (plane X) _ _; rw [mul_assoc,hX]; exact Barrage.Reserve.weir_up (flight_stem (candy_leaf (σ:=η) he hy) hy) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ha) hy) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hf) hy)
include hh
lemma sunny (i k:ℕ)(hi: i ≤ D') : Fleet S (terrain η _) (fun p=> cloak (e.early p s) i k):= by
   have h:Fleet S (terrain η _) (fun p=> e.early p s i k):= by
      by_cases ht:i=0; · simp [Parcel.early, clan, ht, compote]; apply Fleet.fzero
      let f:=Fleet.weaken (k:=terrain ζ _) (Parcel.works T (by omega: 3 ≤ 3) hh i hi k).ofPort bath_terrace; exact Holds.eq (Fleet.sub Parcel.seeded (Threads.lift (R:=fun p=>e.port p i k) (l:=terrain ζ _) License.planted (Parcel.stock_bool s _ _) f)) fun p _=> (e.givens p s ht k).symm
   unfold Xenon.cloak; rw [← Xenon.ribbons]; apply Threads.lift (τ:=tunnel η) (Threads.alone (flight_stem tinrice zero_le_one)) fareFoot h
-- Spot = augmented polynomial boost. Prices at pulse request B+i (B=dart ...).
variable {v:Site s.L}{x:Dye G}{U:Type} {q:ℕ}{F: U→ Field (Fin k) (Node (Dye G))}
abbrev extendF (e:Parcel G) (s:Parcel.Step)(z: Cover)(f:Field (Fin k) (Node (Dye G))) : Field (Fin k) (Node (e.White s)):= packing (lane (Dye G) s.L) (packing (backpack z) f)
abbrev beckon (e:Parcel G) (p:Word) (s:Parcel.Step) (z:Cover) (B i:ℕ) (X:Field (Fin k) (Node (Dye G))) := ray (e.raw p s) (e.beam p s) (e.early p s) B i (extendF e s z X)
open Mileage
lemma moment_charge (h:∀ u, Rest (terrain ζ _) (0,x) (F u) 1) (i r:ℕ)(he:i≤D')(z:Cover)(u:ℕ): Stable U _ S (terrain η _) (fun p v=> ringS u (extendF e s z (F v)) (e.early p s) i r):= by
   unfold ringS; simp_rw [Pi.add_apply]; refine Stable.add (Stable.for_all (sunny T hs hh i r he)) ?_; by_cases hv:i=u; swap; · simp_rw [Pi.single_eq_of_ne hv]; exact Stable.zero
   simp_rw [← hv,Pi.single_eq_same ]; by_cases hy:r=k+1; swap; · simp_rw [Pi.single_eq_of_ne hy]; exact Stable.zero
   subst r; simp_rw [Pi.single_eq_same]; refine Stable.gift (b:=Theater.stuff (2*ζ) ζ z*1) _ (fun v=> ?_) ?_; · 
      let H:= Theater.path_cost (T:=crafts e [] s T OK.nil) (h v) (step_reserved s ζ) (.inl x) z; exact (Xenon.scar_paid (Sum.inl x) H).even
   have hl:0≤ Theater.stuff η ζ z:= by unfold Theater.stuff parcelY; (positivity);
   positivity -- semicolon
lemma momentR (hF:∀ u, Rest (terrain ζ _) (0,x) (F u) 1)(z:Cover)(i r:ℕ)(hi:q+i ≤ D'): Holds S (fun (f:U→Field (Fin r) (Node (Dye G))) b=>∀ u, Rest (terrain η _) (0,x) (f u) b) (fun p v=> beckon e p s z q i (F v) r) := by
   let H:= mintCandy T hs; let L:= mintBeam T hs; let Y:= terrain η (Option (e.White s)); let f p v:= ringS q (extendF e s z (F v)) (e.early p s); let X:= Option (Dye G); let K p v:= Xenon.hearth (e.early p s) (plane (e.raw p s)) (Matrix.of (plane (e.beam p s))) (extendF e s z (F v)) q (q+i) (r+1);
   have hp: Stable U _ S (terrain η X) K:= by
       unfold K Xenon.hearth planeC; simp_rw [←footplane,← shadeplane]; exact Stable.hoist L fareFoot (Stable.mass (T:=f) (fun i hi' j=> moment_charge T hs hh hF i j (hi'.trans hi) z q) H)
   obtain ⟨⟨s',hs',hS⟩,c,hc,hC⟩:=hp; let a:ℝ:=(r+1:ℕ); refine ⟨⟨_,mul_nonneg (a:=a) (by unfold a; positivity) hs',fun p hp u=> homing_credit (hS p hp u)⟩,_,mul_nonneg (a:=a) (by unfold a; positivity) hc,fun p q' u hp hq hu v=>?_⟩
   change Rest _ _ (scoop (K (u++p) v)-scoop (K (u++q') v)) _; rw [show _- scoop _= _ from (show scoop (K (u++p) v)-scoop _=scoop (K (u++p) v-K (u++q') v) from funext fun _=> by simp [scoop,smul_sub]),mul_assoc]; exact homing_credit (hC p q' u hp hq hu v)
end Transfer
end
end YM.Contacts.Harrier
