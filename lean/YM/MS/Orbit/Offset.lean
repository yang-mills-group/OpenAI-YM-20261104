import YM.MS.Orbit.Cookie
/-!
# Links PayA and PayB_
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit.LogReal
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Flux Cog Wire Rake Book Convolve
open scoped Topology ContDiff Interval
variable {G:Gauge}{A I W:Type}{L:I→Side}{F H:Glade G I}{P:Planet G I} {i:I}{b: Bool}{v w:Faces I}
local notation "Ω"=> enterV L b
local notation "Γ"=> σbranch (G:=G) (n:=dimT L i)
local notation "δ"=> dimT L i
lemma pay_cycleA (b:Bool)(L:I→Side)(i:I)(h:Toned F)(hp:Glow P): Static (zoneP L b P i) (PayA L b i v F) = PayA L b i v ( zip0 (enterV L b) P v F ):= by
    -- shadow L hygienic. avoid
    funext t; obtain he:= hp.proper i t; obtain ht:=riverOK (n:=dimT L i) he.pin he.gov; unfold Static zoneP primary Paper; rw [charge]; let Z:= iota G (dimT L i); rw [ Z.read_pc b ht, charge ]; cases b;
    · apply congr_arg (Z.readerV false); obtain hx:= chase_pc (v i) false (h.sound i t) (P:=P i t) (n:=dimT L i); rw [flat_zip0 ( enterV L false ) rfl]; refine hx.trans ?_; congr 2; rw [show Dph false (v i) (v i)=0 from (by simp [Dph,taste])];
    apply congr_arg (Z.readerV true); rw [ imageV,if_pos rfl,Cascade,frame_add,LinearMap.add_apply ]; obtain hx:= chase_pc (v i) false (h.sound i t) (P:=P i t) (n:=dimT L i); obtain hz:= chase_pc (v i) true (h.sound i t) (P:=P i t) (n:=dimT L i); rw [Dph,taste] at hx; rw [if_neg (by decide :¬false=true), add_neg_cancel] at hx; rw [show zip0 (enterV L true) P v F i t=(click (enterV L true) false 0 P F + click (enterV L true) true (Vary v) P F) i t from rfl,Pi.add_apply,Pi.add_apply,map_add]; exact congr_arg₂ _ hx hz -- note `0` function defeq
lemma Φ_BA (h:Toned F)(he:Toned H)(hp:Glow P)(hF: StandGuard L F i)(b:Bool): TypeTouch σbranch (zoneP L b P i) ( PayB L b i F ) ( PayA L b i v H ) = PayA L b i v (expJ P F H):= by
    funext t; let X:=P i t; let S:= iota G δ; obtain hr := hp.proper i t; obtain ht:= riverOK (n:=δ) hr.pin hr.gov; unfold TypeTouch zoneP primary Paper σbranch; rw [ charge H,pay_at ]; rw [ S.read_tree b ht, charge ]; rw [ S.read_plain b (G:=anchor G δ _ _ ) ( F:=Bulk G δ ( F i t)) ( hF t |>.1 ) ht ( evenK hr.close ) ( stampL hr.pin hr.t ), BM hr ( h.sound i t ) ( he.sound i t ) ]; rfl -- placeholders dev
lemma Φ_BB (h:Toned F)(he:Toned H)(hp:Glow P)(hF: StandGuard L F i)(b:Bool): TypeTouch σbranch (zoneP L b P i) ( PayB L b i F ) ( PayB L b i H )= PayB L b i (expJ P F H):= by
    funext t; let S:= iota G δ; obtain hr:=hp.proper i t; obtain ht:= riverOK (n:=δ) hr.pin hr.gov; unfold TypeTouch zoneP primary Paper σbranch; rw [pay_at,pay_at]; rw [S.read_tree b ht,pay_at, S.read_plain b ( F:=Bulk G δ (F i t)) ( G:=pay b • Bulk G δ ( H i t ) ) ( hF t|>.1 ) ht ( evenK hr.close) ( stampL hr.pin hr.t ), show conn _ (mat δ ( P i t )) (Bulk G δ ( F i t )) (pay b • (Bulk G δ (H i t))) = pay b • Cog.conn (field parity) (mat δ ( P i t )) (Bulk G δ (F i t)) (Bulk G δ ( H i t)) from link_smul (frame _) _,BB hr ( h.sound i t) ( he.sound i t ) ]; rfl -- arg names
lemma Φ_AA (h:Toned H)(hp:Glow P): TypeTouch Γ (zoneP L b P i) (PayA L b i v F) (PayA L b i w H)= PayA L b i w (zip2 Ω P v w F H):= by
    funext t; let S:=iota G δ; obtain he:= hp.proper i t; obtain hx:=riverOK (n:=δ) he.pin he.gov; unfold TypeTouch zoneP primary Paper σbranch; rw [charge F,charge H ]; rw [ S.read_tree b hx, charge ]; cases b; · apply congr_arg (S.readerV false); simp only [zip2, adjust,enterV, Bool.false_eq_true,↓reduceIte,add_zero]; exact A_T false he ( h.sound i t )
    apply congr_arg (S.readerV true); obtain hm:= A_T (n:=δ) true ( F:=F i t ) ( H:=H i t ) (A:= v i) ( B:=w i) he ( h.sound i t ); unfold Cog.conn imageV; rw [ if_pos rfl,Cascade,frame_add,link_plus ]; unfold zip2; rw [Pi.add_apply, Pi.add_apply,map_add]; exact congr_arg₂ _ ( A_T ( F:=F i t ) ( H:=H i t ) ( n:=δ ) ( A:=v i ) ( B:=w i ) false he ( h.sound i t ) ) hm
-- need parity reader
lemma Rim {F:Raw A ℂ}{p:Sector A}(U: Cog p)(x y:ℂ)(h:Pure p false F): Pure p false ( U.wheel x y F ) := by
   intro l hl; have ht: sign p true F=F:= by rw [Pure.signs h]; simp
   obtain hv:= congr_fun (roll_sign U x y (F:=F) true) l; rw [ht,Koszul.at_sign,cross,if_pos (show _=true from (by simpa using hl))] at hv; linear_combination (norm:=ring_nf) hv / 2 -- sign parse
lemma swap_net (hp: Glow P)(X: OM (FixedMode G δ))(hq:StandGuard L F i): TypeTouch Γ ( zoneP L b P i ) X ( PayB L b i F ) = TypeTouch Γ ( zoneP L b P i ) ( PayB L b i F ) X:= by
    funext t; let S:=iota G δ; obtain hx:= hq t |>.2; have hz : Pure Γ false ( PayB L b i F t ):= by rw [pay_at]; let U:= YLift L i F t; cases b; exact ( Pure.smul (pay false) hx ); exact Rim S _ _ (Pure.smul ( pay true ) hx )
    exact link_commute_even (frame _) (X t) hz ( fr_pure (readsK (hp.proper i t |>.close) b ) false hz ) -- orientation
end YM.MS.Orbit.LogReal
