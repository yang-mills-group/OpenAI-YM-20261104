import YM.FVA2.O.Seam.End
/-!
# Pull back the `RecipeT` solution

`yieldQ`: can select the OPE preparations for *fixed unit profiles* and then
pull back along the parameters of various larger families attaching the exterior.
Keep the positions/η as specified in this pullback; the family's large distance parameter θ
needn't match the old one. See `O/Enh/Sale`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Seam
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue Rough O.Cool O.Clift Rake.Geo O.Price O.Fuse
open scoped Topology ContDiff Interval
variable { G: Gauge } { I J W : Type } {B: Deck G}{K:Booked B}{M:MS_Data G K}{P:Geo I}{ Q:Geo J }{ Y X:T ( Glade G J )}{ξ:I→J}{p:T ( J→ℝ )}{η:J→ℝ}{ n k d:ℕ}
-- proof direction smaller index refers to J
abbrev pullT (ξ:I→J)(r: Details B J k): Details B I k := fun i n=> r i n ∘ ξ
local notation "x0"=> compose0 ξ
lemma pull_L : x0 ( entrance p X )= entrance ( fun n=> p n ∘ ξ ) ( x0 X ):= by
    funext k i; unfold compose0 entrance; rw [ Finset.sum_apply, Finset.sum_apply ]; exact Finset.sum_congr rfl fun j hj=> by rw [ hx_holder (show j≤k from by simp only [ Finset.mem_range ] at hj; omega), hx_holder (show j≤k from by simp only [ Finset.mem_range ] at hj; omega) ]; rfl
lemma charm_l {r:Details B J k}: x0 ( Physical η M r )= Physical (η∘ ξ) M ( pullT ξ r ):= by
    unfold Physical; funext n i; unfold compose0; rw [ Finset.sum_apply,Finset.sum_apply,Finset.sum_apply,Finset.sum_apply ]; exact Finset.sum_congr rfl (fun j _=> congr_fun ( congr_fun ( pull_L (ξ:=ξ) (X:=roadZ η M j) (p:=r j) ) n ) i)
variable (h:P.η=Q.η∘ ξ)
def dropQ (ξ:I→J)(u:(Station P).Inst): (Station Q).Inst := (Station Q).choose ( ξ ( index u ) ) ( t u ) u.ge
include h
lemma basicQ (i:I): ( Station P ).dawn.basic i= (Station Q).dawn.basic ( ξ i ) := congr_arg (fun t=> (1+|t|)*(1+(0:ℝ))) ( congr_fun h i )
local notation "Ð"=> dropQ ( Q:=Q ) ( P:= P ) ξ
lemma BasicQ (i:( Station P ).Inst) : (Station P).primary.basic i= (Station Q).primary.basic ( Ð i ):= congr_arg (fun v=> (1+|v|)*(1+t i)) ( congr_fun h (index i) )
omit h in
lemma LengthQ ( i:(Station P).Inst ): (Station P).primary.length i= (Station Q).primary.length ( Ð i ):= rfl
lemma valid_l {r:Details B J k}(hp: Valid (Station Q) r): Valid (Station P) (pullT ξ r):= by
    intro i k; obtain ⟨C,hC,d,hK⟩:= hp i k; refine ⟨C,hC,d,fun i' =>?_⟩; rw [basicQ h i']; exact hK ( ξ i' )
lemma taxiQ : Bus (Station P).primary (Station Q).primary Ð:= ⟨ ⟨1, zero_lt_one,1,fun i=>by simp only [Function.comp_apply,  one_mul,pow_one,Pi.one_apply,mul_one]; exact ( BasicQ h i ).ge ⟩,1,zero_lt_one, fun i=> by rw [one_mul,LengthQ i] ⟩
lemma dipQ {F: Glade G J}{x:(Station P).Inst→ℝ}{y:( Station Q ).Inst→ℝ}(hp:Latch.Lease false false (Station Q).primary (sendT ( face (Station Q) ) F) y )(hx:y∘(Ð)=x)(he:nn x): Latch.Lease false false (Station P).primary (sweep (Station P) (F∘ ξ) ) x:= by
    intro E _ _ w hh hT; refine ticket (P:= (Ð)) (f:= Chart (sendT (face (Station Q)) F) w ) ( taxiQ h ) ( hp E w hh hT ) ( paidMono (fun i => ?_ ) ) ( fun i=> pos_nn x he _ i ); unfold Function.comp; rw [ LengthQ (Q:=Q) (ξ:=ξ), ← hx ]; exact le_rfl
variable [LinearOrder W] {y:Position W J}{ R:W→ Label B}{s:Finset W}
lemma charm_Q : x0 ( thicket Q M y R s )= thicket P M ( fun i=> y i ∘ ξ ) R s:= by
    unfold thicket; rw [screen_P, show snap_c ξ (patchD Q M y R)= patchD P M (fun i=> y i ∘ ξ) R from ?_ ]; funext s n i; unfold snap_c Dial.copy patchD; rw [h]; rfl
lemma yieldQ {r:Details B J k}( hp: RecipeT Q M (thicket Q M y R s) k d r ): RecipeT P M (thicket P M (fun i=> y i ∘ ξ) R s) k d ( pullT ξ r ):= by
    obtain ⟨hh,X,hX,hR,hP⟩:= hp; refine ⟨ valid_l h hh,x0 X, h.symm ▸ dresser hX ξ,fun _=> dipQ h (hR _) rfl (fun _=> length_p ..),?_ ⟩
    rw [ ← charm_Q h,h, ← charm_l,nick ]; exact fun i hi=>dipQ h ( hP i hi ) rfl decay_p
end YM.FVA2.O.Seam
