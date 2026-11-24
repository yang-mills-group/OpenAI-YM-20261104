import YM.MS.Image.Seat
/-!
# Convert ζ=0 formulas to exact Domain.recu and Ward

Numbers agree with fixing $ν$. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Outlook
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve Garment.Wave Garment.Wick High Detect Domain Tone.Frame
open scoped Topology ContDiff Interval
variable {I:Type} {G:Gauge}{X Y F:T (Flats G)}{J N:Flats G}{f g p q:T (Coat G)}{b c:Bool}{t r:ℤ}{a h n m k ℓ:ℕ}{i:ℂ}{s y:ℝ} {U:Rip G}
lemma A_min (hp:Host J h) : Lift ( Parade ( step0 G J ) h y s) ( unitC 0 y (A0 G s) ( hereZ h J s y )):= by have he:=view_head (y:=y) (s:=s) (m:=h) hp (c_bo 0) (c:=4) (by ring); rw [pA] at he; exact he
lemma YM_min (hX:∀ i, Host (X i) 4)(hY:∀ i, Host (F i) h): Lift ( Parade ( pairW (drive0 G) X F n ) h y s) ( pairW ( squad (A0 G s)) ( NumX s y 4 X ) ( NumX s y h F ) n):= by
    obtain he:= tree₄ hX hY (K:=A0 G 0) (c_bo 0) (reverse_a G 0) (show (4:ℂ)-(4:ℕ)-h=-(h:ℂ) by push_cast; ring) (s:=s) (y:=y) ( h:=n); rw [pA] at he; exact he -- whitespace named.
lemma Bday (hx:leader G F f p)(he:1≤n): four 4 (program G n F+step0 G (F n))= recu (spaceD G) 1 ((2:ℂ)⁻¹) (Archive 4 F) (Archive 4 F) n := by
    have hK :=(hx 0).2 rfl; have hs(i:ℕ):=Host.host (gang (hx i)); let V:= program G n F+step0 G (F n); funext i; obtain ⟨y,t⟩:= i; rw [ dayB (U:=A0 G t) (spaceD G) ( hs n) hK rfl rfl ( c_bo .. ) (by omega)]; change hereZ 4 V t y 0=_; refine congr_fun (Lift.unique (F:= hereZ 4 V t y) (f:= Parade V 4 y t) ( live0 (grow_host hx n).tall) ?_) 0; unfold V; rw [add_comm (unitC 0 y (A0 G t) _),page_add,pc_max hK,page_smul]; exact Lift.add ( Lift.static ( YM_min hs hs ) _ ) ( A_min (hs n)) -- `.add_comm unitC .. syntax.
lemma Mday (hx:leader G X f p)(hp:comet h r X g F q) : four h (platform X n F+step0 G (F n)) = recu (spaceD G) 0 1 ( Archive 4 X ) ( Archive h F ) n:= by
    have hK :=(hx 0).2 rfl; let V:= platform X n F+step0 G (F n); funext i; obtain ⟨y,s⟩:= i; rw [dayM (U:=A0 G s) (spaceD G) (Host.host (gang (hp n))) hK rfl rfl (c_bo ..)]; change hereZ h V s y 0=_; refine congr_fun (Lift.unique (F:=hereZ h V s y) (f:= Parade V h y s) (live0 (mark_h hx hp n).tall) ?_) 0; unfold V; rw [one_smul,add_comm (unitC 0 y (A0 G s) _),page_add,pm_max hK]; exact Lift.add (YM_min (fun i=>Host.host ( gang (hx i))) (fun i=>Host.host ( gang (hp i)))) (A_min ( Host.host (gang (hp n))))
-- Master Ward.S formula: equality at net enough

def Kept (n:ℕ)(t:ℂ)(B F:T (Mob G)) (s:ℝ)(y:ℝ):= ( Grid 0 y s G).J ( F n )+ t • pairW ( Grid 0 y s G).C B F n
lemma B_ward (hx:leader G X f p) (w:Legs (Lane4 G )) (he: Course true w) (hp: CleanP true ( PB X n))(hn:1≤n) : (send (C:=G.ColorIndex) (id:Detect.FourP→Detect.FourP)).raise ( Archive 4 X n (y,s)) w=High.Ward id (spaceD G) n 1 ((2:ℂ)⁻¹) ( Archive 4 X ) ( Archive 4 X ) (y,s) w := by
    let B:= NumX s y 4 X; have ht(i:ℕ):=Host.host ( gang (hx i)); obtain hz : Equal true (Kept n ((2:ℂ)⁻¹) B B s y) 0:= by unfold Kept; unfold B; rw [← pulsePose _ ht ht]; exact pose_white (Host.Pose_p ht ht ..) hp
    unfold High.Ward; rw [ dayB (U:= B0 G s) ( High.degreeMaster id (spaceD G)) (ht n) ((hx 0).2 rfl) rfl rfl (heed ( B_caps ..)) (by omega)]; let L:= (pairW (squad (B0 G s)) B B n); apply eq_neg_of_add_eq_zero_left; obtain hh:= hz 0 w he; change (Q G 0).raise (B n 0) w + (( unitC 0 y ( B0 G s)) (B n) 0 w + (2:ℂ)⁻¹ * L 0 w)=0; rw [← add_assoc]; exact hh -- eq left orientation & arity parse
lemma M_ward (hx:leader G X f p)(hp:comet h r X g F q) (hv:CleanP false ( PM X F n)) (w:Legs (Lane4 G)): ( send (C:=G.ColorIndex) (id:FourP→FourP)).raise ( Archive h F n (y,s) ) w= Ward id (spaceD G) n 0 1 ( Archive 4 X ) ( Archive h F ) (y,s) w:= by
    have hf(i:ℕ):=Host.host ( gang (hx i)); have hX(i:ℕ):=Host.host (gang (hp i)); let H:= NumX s y 4 X; let L:= NumX s y h F; obtain hz : Equal false (Kept n 1 H L s y) 0:= by unfold Kept; unfold H L; rw [← pulsePose _ hf hX]; exact pose_white (Host.Pose_p hf hX ..) hv
    unfold High.Ward; rw [ dayM (U:= B0 G s) ( High.degreeMaster id (spaceD G)) ( hX n) ((hx 0).2 rfl) rfl rfl (heed (B_caps ..))]; apply eq_neg_of_add_eq_zero_left; change ( Q G 0).raise (L n 0) w + (unitC 0 y ( B0 G s) (L n) 0 w + (1:ℂ)* pairW (squad ( B0 G s)) H L n 0 w )=0; rw [← add_assoc]; exact hz 0 w (fun u=> Bool.noConfusion u)
end YM.MS.Outlook
