import YM.MS.Port.Captain
/-!
# MS physical clock. Scaling covariant including endpoints. Set P= native length frame, Q=physical degree frame. Native subtraction parameter y=physical η−σ, σ=log(1/a).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Port
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo Vane
open Osc Fiddle Snap Book.Convolve Alps Arts City Dock Emit Mach Land Pearl Train Menus Hem Mell
open scoped Topology ContDiff Interval
variable {G:Gauge}{W I:Type}{F:Flats G}{X: Mob G}{P Q: Geo I}{ζ t y:ℝ}
    {B: Local.Physical.Deck G}{O:Booked B}(M:MS_Data G O) {n:ℕ}{σ:I→ℝ}
lemma Can (hp: Host F n) (g:ℝ): hereZ n F t y= plow (-(n:ℂ)) g (hereZ n F (t-g) (y+g)):= by
    obtain ⟨p,ht⟩:= tallP (Moony.toast hp.bill); rw [ vertical ht hp.tall, vertical ht hp.tall,Alps.snow, show g+(t-g)=t from (by abel), show y+g+(t-g)= y+t from (by abel) ]
lemma Bx4 (hp:Host F n): four n F (y,t) = shift n ζ ( four n F (y+ζ,t-ζ) ):= by
    funext v; change hereZ n F t y 0 v=_; rw [ Can (F:=F) hp ζ ]; unfold plow shift; rw [ show -(n:ℂ)+(Alps.mass (m:=0) v:ℂ)=( ( pitch v-n:ℤ ):ℂ ) from (?_) ]; swap; · push_cast; ring_nf; rfl 
    rw [ τ_amt ]; rfl
variable (h: ∀ i,Q.η i=P.η i+σ i)
include h
lemma fees : glide ( approach Q M) σ 4=approach P M:= by funext n i t; obtain he:= Host.host (gang ( M.bulkOK n )); change shift _ _ (four _ _ (Q.η i,_))=four _ _ (P.η i,t); rw [h]; exact Eq.symm ( Bx4 he )
lemma hoof (p: Label B): rowM P M p=glide (rowM Q M p) σ p.h:= by funext n i t; obtain he:= Host.host (gang ( M.markOK p.h p.item n )); change four _ _ ( P.η i,t )= shift _ _ ( four _ _ ( Q.η i,_ ) ); rw [ h ]; exact Bx4 he
variable [LinearOrder W]{R:W→ Label B}{Y:Position W I} -- Junk fail
variable {U V:Rake.Dance G I W}
lemma shifter (he:DOrd O Q M R Y U): DOrd O P M R (moved σ Y) (loom σ ( Label.h∘R ) U):= by
    let g(i:W):= glide (( rowM Q M ∘ R ) i) σ ( R i|>.h ); obtain he:= steer σ ( Label.h ∘ R ) Y he; rw [fees M h] at he; have hX: rowM P M ∘ R=g:= funext fun i=> hoof M h ( R i ); unfold DOrd; rw [hX]; exact he
omit h M in -- M not included? error
lemma BladeShift (G:Gauge){c:Glade G I}(u:ℤ)(i:I)(he:Allow c i): blade ( twist u σ c ) i= τ (-u) (σ i) * blade c i:= by
    let g(t:ℝ):= t-σ i; have h0:Tendsto g atTop atTop:= Filter.tendsto_atTop_add_const_right atTop (-σ i) tendsto_id -- name
    obtain hp:= ( he.comp h0|>.const_mul ( τ (-u) (σ i) ) ); rw [show (fun t=> τ _ _ * ((fun t=> c i t [])∘g) t)=(fun t:ℝ=> twist u σ c i t []) from ?_] at hp; swap; · ext; simp [ twist, shift, pitch, fieldDim, sr, g ]; -- inspect
    exact tendsto_nhds_unique ( tendsto_nhds_limUnder ⟨_,hp⟩ ) hp
variable (A:Arch ( Gulf Q) (Θ0 G I) (Θ0 G I) (approach Q M) (rowM Q M ∘ R) (Label.h∘ R)) -- used? Far ℓ.Better avoid.e derive arch quality M no need Taylor.Could use using actual lit fees and From.M.
lemma MoonB (hp:DOrd O Q M R Y U)(hx:DOrd O P M R (moved σ Y ) V)( S:Finset W)(n:ℕ)(he:∀ i,Allow (U S n) i): blade ( V S n ) = (fun i=> τ (-(charge ( Label.h ∘ R ) S:ℤ)) (σ i)* blade ( U S n ) i):= by rw [perfect hx ( shifter M h hp )]; exact funext fun i=> BladeShift G _ i (he i) -- parser ..
end YM.MS.Port
