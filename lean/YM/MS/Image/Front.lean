import YM.MS.Vibe.Post
/-!
# Projecting at four dimensions (full regulator, evanescent kept through here).

VertexValue: no smearing, B on Course. Stamp $n$ always. Normalize to high-LPT.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Outlook
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve Garment.Wave Garment.Wick
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{X Y F: T (Flats G)}{J N L:Flats G}{f g p q:T (Coat G)}{b c:Bool}{t r:ℤ}{a h n m k ℓ:ℕ}{i:ℂ}{s y:ℝ}
def hereZ (n:ℕ)(F:Flats G)(s y:ℝ) := ruby (Parade F n y s) 0
abbrev NumX (s y:ℝ)(h:ℕ)(F:T ( Flats G)): T (Mob G) := fun n=> hereZ h (F n) s y
lemma live0 (hE:Stay n J): Lift (Parade J n y s) (hereZ n J s y) := Rub (hE y s) 0
lemma vertical (h:Rent J n)(he:Stay m J): hereZ m J s y=plow (-(m:ℂ)) s (Press J n n (y+s)):= by
   apply Pick.unique ( land (live0 he) n) ( press_pick h _ _ _ )
lemma rise (h: Stay n J)(hp:Stay n N)(he: Merg J)(hv: Vibe n J N) (s y:ℝ): speed (fun t=>hereZ n J t y) (hereZ n N s y) s:= by
   obtain ⟨q,H⟩:= tallP he; simp_rw [vertical H h,vertical (work H hv) hp]; exact cohabit H hv q s y
lemma just_bright (hp:Stay n J)(hf:Moony b J): Form0 b (hereZ n J s y) := by
   let Q:= live0 hp (s:=s) (y:=y); refine ⟨Lift.price Q,Lift.acre Q (P:=Sturdy b) ( Wind.time (b:=b)) ?_⟩; exact Eventually.mono (Moony.march hf n) (fun i hi=> (hi y s).token)
-- project rank test and degree (Pol identity next)
lemma valueC (hp: Stay n J)(hv:Merg J)(Q:LeanC G)(h:Need Q)(hm:∀ i:ℕ, To ( J i) Q) : hereZ n J s y∈Q:= by
   obtain ⟨p,ht⟩:= tallP hv; rw [vertical ht hp]; exact h.seo ( viewP J _ _ Q h ht hm _) _ _
lemma sees_some ( hp: Stay n J)(hv:Merg J)(Q:LeanR G)(h:Will Q)(hm:∀ i:ℕ,realAlong ( J i) Q): hereZ n J s y ∈ Q:= by obtain ⟨p,ht⟩:= tallP hv; rw [vertical ht hp]; exact h.soft (viewR J _ _ Q h ht hm _) (by simp) _
lemma pose_white (hp: Host J h)(hv:CleanP b J): Equal b (hereZ h J s y) 0:= by intro m l hl; exact tendsto_nhds_unique ( Lift.wind (live0 hp.tall) m l) (tendsto_const_nhds.congr' (Eventually.mono hv (fun i hi=> Eq.symm (Emit.orbit hi h m l hl))))
-- projected Grid algebra on arrays constructed
lemma view_head (hx:Host J h){K:Rip G}{c:ℂ}(hK:Knot false K)(hc:c-4=(h:ℂ)-m): Lift ( Parade ( CycleN K J) m y s) (unitC 0 y (pulse c s K) (hereZ h J s y)):= lift_up _ _ ( live0 hx.tall ) hx.bill hK hc
lemma tree₄ {a:ℂ} (hX:∀ i,Host (X i) n)(hY:∀ i,Host (Y i) m){K:Rip G} (ht:Knot false K)(hv:reverseF K)(he:a-n-m=-(k:ℂ)) : Lift ( Parade (pairW (TreeN K) X Y h) k y s ) ( pairW (squad (pulse a s K)) (NumX s y n X) (NumX s y m Y) h) := by
   rw [paired,paired,page_sum]; refine (show Pick 0 _ _ from Pick.fin _ (fun i _=>?_)); exact ( show Lift _ _ from lift_root he ht hv _ _ (live0 ( hX _|>.tall)) (live0 ( hY _|>.tall ))) -- lean pick reorder danger
lemma Q₄ (hp:Host J h) : Lift ( Parade ( Emit.park G J ) (h+1) y s ) (( Grid 0 y s G).J (hereZ h J s y)):= by
   simp only [Emit.park,LinearMap.add_apply,page_add]; change Lift _ (portZ _ _ + unitC 0 y ( B0 G s) _);have hv:= view_head (s:=s) (y:=y) (m:=h+1) hp ((B_caps G 0).clearer) (show (3:ℂ) - 4=(h:ℂ)-(h+1:ℕ) from by push_cast; ring ); rw [pB G s] at hv; exact Lift.add (Lift_Q y s (live0 hp.tall)) hv
lemma pulsePose (x:ℂ) (hp:∀ i,Host (X i) 4)(hv:∀ i,Host (F i) h): NumX s y (h+1) (fun i=> Pose i x X F) n = ((Grid 0 y s G).J (NumX s y h F n)+x • pairW (Grid 0 y s G).C ( NumX s y 4 X) ( NumX s y h F) n):= by
   refine Lift.unique (live0 ( Host.Pose_p hp hv n x).tall) ?_; simp only [Pose,page_add,page_smul]; refine Lift.add (Q₄ (hv n)) ?_; convert Lift.static ( tree₄ hp hv ( K:=B0 G 0) (( B_caps ..).clearer) ( reverse_b G 0) (a:=3) (k:=h+1) (h:=n) (y:=y) (s:=s) ( by push_cast; ring) ) x using 1; rfl; rw [pB]; rfl
end YM.MS.Outlook
