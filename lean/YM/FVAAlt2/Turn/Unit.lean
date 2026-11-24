import YM.FVAAlt2.Turn.Linear
/-! Vacuum calibration of DREG optics at horizon zero. No contact/MS global mass/gauge
 assumptions. Includes all evanescent channels (here none remain). -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.FVA.Town
open Set Filter Function Finset MeasureTheory Metric Arc Real
open Plane Koszul Heat Flux Landau Arts Pilot Spin Arc Wire Rock Path Oceans Plum Alps Garment Color Book _root_.YM.MS.Shine Hem Mell Logarithm Pearl Train Dock Emit
open Signal Book Convolve High Detect Domain Tone Tone.Frame Momentum Outlook Motif Literal Halo Mach Mach.Pole
open _root_.YM.MS.Wind _root_.YM.MS.City Native Native.Wilsonian
open Motions Leading Knobs Menus Program Local.Physical Land
open scoped Topology BigOperators ContDiff Interval
set_option linter.unusedSectionVars false
variable (G:Gauge) {m n k:ℕ} {r h x:ℝ}{c:ℂ} {B:Deck G}
abbrev baseM (G:Gauge): Mob G:= fun _=> coin 1
abbrev cabin (G:Gauge): Box (Mob G):= Finsupp.single 0 (baseM G)
abbrev eSp (G:Gauge): Coat G:= fun _=> baseM G
abbrev emit_L (G:Gauge): T (Coat G):= gloss ( Literal.linear (Mob G) (cabin G))
local notation "Φ"=> baseM G
-- span degeneration. exploit elementary `Literal`, unit not inferred from unphysical sent equality.
variable {G} {T₁:ℂ→ Mob G}
lemma gallery₀ (h:T₁∈Gallery G 0 n): ∃ r:ℝ,T₁=(fun _=> (r:ℂ) • baseM G):= by
 refine Submodule.span_induction (p:=fun T _=>∃ r:ℝ,T=(fun _=> (r:ℂ) • baseM G)) ?_ ⟨0,by ext; simp⟩ ?_ ?_ h
 · rintro v ⟨f,x,rfl,rfl⟩; have h : Subsingleton (Lifting.Grid G 0):=inferInstance; refine ⟨ ∑ j:Lifting.Grid G 0,Lifting.group G j x,?_⟩; funext i; rw [saint,Complex.ofReal_sum,Finset.sum_smul]; rfl
 · rintro u v _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; refine ⟨ a+b,?_⟩; funext; push_cast; rw [add_smul]; rfl
 rintro v u _ ⟨a,rfl⟩; refine ⟨v*a,?_⟩; funext; push_cast; rw [mul_smul];rfl
variable {Tx:Box (Mob G)} {F:Law G}
lemma valH (he:∀ z:ℂ,value (Mob G) z Tx=c • Φ): Tx= Finsupp.single 0 (c • Φ):=by
 have hv(ℓ:Mob G→ₗ[ℂ]ℂ) (k:ℕ): ℓ ((Tx-Finsupp.single 0 (c • Φ):Box (Mob G)) k)=0:= by refine valuedZ (Tx-Finsupp.single 0 (c • Φ)) ℓ ?_ k; intro z; rw [map_sub,he,value_sl,pow_zero,one_smul,sub_self,map_zero]
 ext1 y; funext m i; apply sub_eq_zero.mp; exact hv (( LinearMap.proj i: Rack G m →ₗ[ℂ] ℂ ).comp (LinearMap.proj m)) y
lemma zero_map (h:Ele 0 0 F Tx):∃ r:ℝ,F=(r:ℂ) • Φ 0 ∧ Tx=(r:ℂ) • cabin G:= by obtain ⟨r,hr⟩:=gallery₀ h.1; have hv := valH (G:=G) (c:=(r:ℂ)) (fun z=>congr_fun hr z); rw [ ← Finsupp.smul_single ] at hv; refine ⟨r,h.2.symm.trans ?_,hv⟩; rw [ hv ]; simp

variable (G)
lemma sizeMS : Sturdy false (Φ):= { turn:=fun i v _=> Halo.vaultLeaf .., grows:= fun h w=>by cases w<;> rfl }
lemma hue_0: ShadeG (Φ):= by intro m g; rw [ ← Garment.brush ]; exact Halo.vaultLeaf ..
lemma upright_0 : Badge false (eSp G) 0 0:= Pace.prepay (r:=0) (fun _=> Pace.unit) (sizeMS G) (hue_0 G)
lemma billed : Cap0 false 0 0 (eSp G):= bias (fun _=> Pace.unit.up ) ( Outlook.give (upright_0 G) |>.2.2 )
abbrev singleM (G:Gauge): Flats G:= Finsupp.single 0 ( eSp G )
def winter (G:Gauge): T (Flats G) := fun n=> if n=0 then singleM G else 0
lemma lived : Joint 0 0 (singleM G) (eSp G) 0:= joint_static (upright_0 G).born (Live.stays ( give ( upright_0 G )|>.1 ))
lemma pax_v : Pact (step0 G (singleM G)) 0:= by refine pact0 ⟨_,(show (0:ℤ)-2 < 0 by decide), clockCap (mine (F:=singleM G) ( Cap0.heap.single ( billed G ) 0 ) ( lived G ).toll).eye ⟩ -- args
lemma ground_v : Bob false 0 0 0 0 ( singleM G ) (eSp G) 0:= ⟨(lived G).via (pact_sym (by rw [zero_add]; exact pax_v G)),Cap0.heap.single (billed G) 0,Cap0.zero⟩
lemma coinless (X:Law G) : tree Landau.parity (Cpu G x) X (coin 1)=0:= by
 ext w; unfold tree; rw [scatter_congr _ w _ 0 (fun x y h=>?_ )]; exact map_zero (allocate _ w); unfold attaches; simp [coin] -- Cinch, need P parity
lemma pure0 (U:Ridge G n)(V: Rack G n): tree Landau.parity U V (Φ n)=0:= by
 ext w; unfold tree; rw [scatter_congr _ w _ 0 (fun x y h=>?_ )]; exact map_zero (allocate _ w); unfold attaches baseM; simp [coin]
lemma pure_one (F:Flats G): drive0 G F (singleM G)=0:= by
 change explode _ _ _=_; rw [explosionP,Finsupp.sum,LinearMap.sum_apply]; apply Finset.sum_eq_zero; intro i _; rw [singleM,blast_sl]; rw [ show tapeB _ ( F i ) ( eSp G )=0 from ?_,Finsupp.single_zero ]; exact funext fun z=> funext fun n=> pure0 G (Garment.Wick.A0 G 0 n) _
lemma Pure_bill (F:T ( Flats G )): comet 0 0 F (emit_L G) (winter G) 0:= by
 intro n; have ht : platform F n (winter G)=0:= by unfold platform; refine sum_eq_zero fun i _=>?_ ; unfold winter; split <;> first| exact map_zero _| exact pure_one G _
 unfold PathD; rw [ht]; rcases n with _|n; rw [winter, if_pos rfl, show emit_L G 0=eSp G from funext fun k=> Finsupp.single_eq_same]; exact ⟨⟨_, ground_v G⟩,False.elim⟩ -- defeq unfold emit_L 0 needs Finsupp.single val?
 rw [show winter G (n+1) =0 from if_neg (by omega), show emit_L G (n+1)=0 from ?_]; · exact zero_sing _
 exact funext fun i=> Finsupp.single_eq_of_ne (show n+1 ≠ 0 by omega) -- f implicit?
lemma winter_show (Y: Booked B)(R: MS_Data G Y)(i : Plaid B 0) : ∃ c:ℝ, (Land.read i).read = (c:ℂ) • coin (1:ℂ) ∧ Archive 0 ( R.marks 0 i )=(c:ℂ) • Archive 0 (winter G):= by
 have hp:(Land.read i).grade=0:= le_antisymm (Glyph.memory _) (Nat.zero_le _) -- syntax Fin fact val
 obtain he := Y.law 0 i; rw [hp] at he; obtain ⟨c,hc,H⟩:=zero_map he; obtain hx := singc (Pure_bill _ R.bulk) (i:=(c:ℂ)) (by simp); obtain hv:=R.markOK 0 i; rw [H] at hv; rw [ show ((c:ℂ) • emit_L G) = gloss (Literal.linear (Mob G) ( (c:ℂ) • cabin G )) from ?_ ] at hx; swap; · rw [map_smul];rfl
 refine ⟨c,hc,?_⟩; rw [ ← archive_c (winter G) (fun j=> (gang (Pure_bill _ R.bulk j)).dost ) ]; apply archive_eq ( unique_M hv hx (fun _ _=> EventuallyEq.rfl)|>.2 ) (fun j=> (gang (hv j)).dost) (fun j=>(gang (hx j)).dost)
lemma archive_unit (n:ℕ)(a:Clock ℝ): Archive 0 (winter G) n a=if n=0 then coin (1:ℂ) else 0:= by
 rcases a with ⟨y,x⟩; unfold Archive four; dsimp only; unfold winter; split_ifs with h; · exact congr_fun (Lift.unique (H:=Φ) (live0 (s:=x) (y:=y) (lived G).toll) (by rw [singleM,pureP _ (upright_0 G).born ]; exact Lift.stays ( give ( upright_0 G )|>.1 ))) 0
 rw [ no0 ]; rfl

end YM.MS.FVA.Town

