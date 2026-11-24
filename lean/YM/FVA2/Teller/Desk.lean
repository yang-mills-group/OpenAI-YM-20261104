import YM.FVA2.Teller.Loom
/-!
 # Solving in the stricter rank-aware class, against the actual MS flow

 Follows structure of `physicalAtF` (Full/Costs). Parameterized by a choice of highest-rank
 adjustments on n>0 (`b=false` allow, `true` forbid). TECHNICAL lemma `space`
 for `true` carries an additional Taylor **tree** obligation; not using a
 resulting `b=true` implementation without proving that obligation. Prove `false`
 case without that extra obligation at the end (`relaxed`, with the indicated
 bulk `Fixed`). We will actually use the `true` option (see `Inked/Combined`).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.Teller.Desk
open Function Filter Set Finset MeasureTheory Real Metric Lattice
open MS MS.Plane MS.Momentum MS.Arts MS.Koszul MS.Landau MS.Landau.Detect
open MS.Wind MS.Wind.Modeled MS.Wind.Leading MS.Heat MS.Heat.Signal MS.Logarithm MS.High MS.High.Knobs MS.Tone MS.Tone.Frame MS.Color
open MS.Book MS.Book.Convolve MS.Book.Program MS.Dock MS.Train MS.Pearl MS.Emit MS.Garment MS.Garment.Wick MS.Plane.Wire
open MS.Arc MS.Rock MS.Rock.Path MS.Rock.Oceans MS.Motif MS.Hem MS.Hem.Mell MS.Local.Physical MS.Outlook MS.Halo MS.Alps MS.City MS.Mach
open _root_.YM.MS.Shine MS.Plane.Domain
open MS.Land MS.Cylinder MS.Cylinder.Lab MS.Native MS.Native.Wilsonian MS.Menus MS.Lifting Capacity
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}{n d k r:ℕ} {q:Team} {B:Deck G} {J:Glyph B d} {S F:Recount G}{V:FullBook B} {b:Bool}
structure House (J:Glyph B d)(b:Bool)(n:ℕ)(A:Tact B d): Prop where
    leading : n=0→ FitOrder J A
    upper : Located J.grade A n
    strict : b=true → 0<n → Located J.grade A ((n:ℤ)-1)
def Houses (A:Acts B d)(J:Glyph B d)(b:Bool):= ∀ i,House J b i (A i)
abbrev Tape (J:Glyph B d)(b:Bool)(n:ℕ):= {A:Tact B d // House J b n A}
def reactor (J:Glyph B d)(b:Bool)(n:ℕ): Tape J b n:= by
    by_cases h:n=0; · subst n; refine ⟨(Wind.Leading.script J 0).val,fun v=> (Wind.Leading.script J 0).property v,⟨?_,fun _ _ _=>rfl⟩, fun h H=> by omega⟩; intro i hi; apply if_neg (fun h=>?_); subst i; omega
    exact ⟨ (0:Tact B d), fun H=>(h H).elim, ⟨fun _ _=>rfl,fun _ _ _=>rfl⟩,fun _ _=>⟨fun _ _=>rfl,fun _ _ _=>rfl⟩⟩
def aBook (J:Glyph B d)(b:Bool)(A:Code (Tape J b)): Acts B d:= fun i=> (A i).val
def arrang (q:Team)(b:Bool)(J: Glyph B d)(V:FullBook B): Knobs (Tape J b) G where
    wake A:= (SeekF V q d).wake (aBook J b A)
    stay _ _ _ H:= (SeekF V q d).stay _ _ _ (fun i hi=> congr_arg Subtype.val (H i hi))
lemma holdsT (P:Code (Tape J b)): Tag J.grade (aBook J b P):= fun i=> ( P i ).property.upper
lemma new_house {A: Acts B d}{Q: Menus.Price B d}{X: Power G}{v u:ℤ}(H:Located J.grade (A n) u) (hq: Glyph.Homes Q v r)(he:X.allowance=r) (h:(r:ℤ)≤J.grade+u): Located J.grade (Menus.patch A Q X n n) u := by
    rw [Menus.patch, if_pos rfl]; constructor
    · intro i h'; exact Eq.trans (congr_arg₂ ( · - · ) ( H.holds i h' ) (show Q i=0 from by by_contra hz; obtain h0:= hq.grade i hz; omega)) (sub_self _)
    intro x; exact Limit.sub (H.moves x) (Limit.up ( X.ranks x ) (by rw [he]; exact h))
lemma punched {A: Acts B d}{Q: Menus.Price B d}{X: Power G} {v:ℤ}(hA:Houses A J b)(hq: Glyph.Homes Q v r)(he:X.allowance=r)(H:r≤J.grade+n)(H0:0=n → r < J.grade)(hv:b=true → r < J.grade+n): Houses (Menus.patch A Q X n) J b:= by
    intro k; by_cases h:k=n; swap; · rw [Menus.patch, if_neg h]; exact hA k
    subst k
    refine ⟨fun h=>?_,new_house (hA n).upper hq he (by omega), fun i hi=> new_house ((hA n).strict i hi) hq he (by specialize hv i; omega)⟩; subst n; exact fix_order ( ( hA 0 ).leading rfl ) hq he.le (Or.inl (H0 rfl))
-- Slice automatic by rank. n arbitrary. r exactly max through-specific validated later.
lemma sliceHigh {u:ℤ} (A:Code (Tape J b))(H:J.grade+n<r)(hx:u≤d)(hh:Disc false 0 F S 1 d)(hp:∀ t y:ℝ,Limit (S n (t,y)) (J.grade+(n:ℤ))) (x:ℝ) : slice ((arrang q b J V).wake A n-S n) false r u x=0:= by
    let L:= SeekF V q d; let P:=aBook J b A; apply excuse (F:= L.wake P) (v:=d)
    · intro s w hw i h; rw [ torch_piece _ hw ( L.wake P n s ), torch_piece _ hw ( S n s ), maskOff (u:= J.grade+(n:ℤ)) ( by omega ) ( hp s.1 s.2 ), maskOff (u:= J.grade+(n:ℤ)) (by omega)  (show Limit ( L.wake P n s ) (J.grade+(n:ℤ)) from Capacity.RootL V (holdsT A) n s.1 (Real.exp s.2)) ] -- rewrite order ambiguous
    · exact fun x w=> ((aquaF V q P).owes n |>.stay x.1).joint.routine _ _
    · exact fun x w=> (hh.master.road ℝ (ray w) n (Nat.zero_le _) (fun e=> Bool.noConfusion e) (fun e=> Bool.noConfusion e)).1 x
    exact hx
-- technical. Don't instantiate strict case without underwriting. n>0; case n=0 provided separately.
def TreeJet (V:FullBook B)(q:Team)(S:Recount G)(J:Glyph B d) := ∀ (u: ℤ),u≤d→∀ i>0, ∀ A:Acts B d,Houses A J true→ ∀ x:ℝ,slice ( col ( horizonF V q A ) i-S i ) false (J.grade+i) u x=0
lemma space (b:Bool) (h:G.Simple)(hq:Fixed (col (skyline G q)) F true 4 1) (hh: Disc false 0 F S 1 d)(hx: PhysicalHF J S)(hp:∀ i,∀ y t :ℝ, Limit (S i (y,t)) (J.grade+(i:ℤ)))(hk:b=true→ TreeJet V q S J): ∃ A: Acts B d, Houses A J b ∧ Fixed (col (horizonF V q A)) S false d 0:= by
    let K:=arrang q b J V; let W:= SeekF V q d; let U:=Tape J b; let V₀:= col (skyline G q); let T:= mark_seekF V (p:=q) (d:=d) h
    have HT (i:Code U): Spheres wave (spaceL G) V₀ (K.wake i) 1 0 false:= T.law _;
    suffices he: ∃ i:Code U, Fixed (K.wake i) S false d 0 by obtain ⟨i,hi⟩:=he; exact ⟨aBook _ _ i,fun n=>(i n).property,hi ⟩
    refine assigned (B:=fun _=> V₀) HT hh.master hh.good (fun i=>T.occurs (aBook J b i)) hh.open' ?_ (by omega) ?_ (reactor J b)
    · intro X n hn hp i hi r; exact hq (n-i) (by obtain he:=path_in hi; omega) _ (fun _ => Nat.succ_pos r)
    intro n hn r hr u hu hv X EE HE
    let M:= K.wake X n-S n; let L:= slice M false r u; have hz:= advanced (HT X) hh.master hn hr EE
    let A:= aBook J b X; have hA:Houses A J b:= fun i=> (X i).property
    by_cases hk': n=0 ∧ J.grade≤r; · obtain ⟨rfl,H⟩:=hk'; refine ⟨X, Move.refl L ?_ ⟩; intro i w _ hx'; exact congr_fun (guardedF V q (P:=A) ((hA 0).leading rfl) hx H hv hh i) w
    rcases lt_or_ge (J.grade+n) r with hi|hi; · refine ⟨ X, Move.refl L (fun i w hx hx'=>?_) ⟩; exact congr_fun ( sliceHigh ( V:=V) ( q:=q ) X hi hv hh ( hp n ) i ) w
    by_cases hV:b=true → r < J.grade+n; swap; · push Not at hV; obtain ⟨rfl,hV⟩:=hV; replace hV:r=J.grade+n:= Nat.le_antisymm hi hV; subst r; refine ⟨ X, Move.refl L (fun i w hx hx'=>?_) ⟩; exact congr_fun ( hk rfl u hv n (by omega) A hA i ) w
    have ht : Ready L:= slice_ready hz hv (Ready.sub ((HT X).poly n) (hh.master.poly n));
    have hu' (i:ℝ) : L i∈ Lease G u r 0:= lease_one.mpr ⟨slice_solid hz hv fun t=> ((HT X).trueC n t).sub (hh.master.trueC n t),slice_form hz hv,rank_slice⟩
    have hL (i:ℝ) : natQ (L i)=0:= funext (fun l=> closes (HT X) hh.master hh.good hn hr EE hv HE i l (fun v=>Bool.noConfusion v))
    obtain ⟨a,g,h0,h1,hJ,hI,he⟩:= mark_inter ht hu' hL B; obtain ⟨Q,T,hQ,hT,hW⟩:= Menus.room_hereF (n:=n) V q A hu hv h0 h1 hJ hI
    let P := Menus.patch A Q T n; have H':=punched hA hQ hT hi (by omega) hV
    let Y:Code U:= fun i=> ⟨P i,H' i⟩;
    have hm : ∀ i<n,(X i)=(Y i):= fun i h=> Subtype.ext (hW.past i h)
    refine ⟨Y, Move.replace (rewind (K:=K) rfl rfl hm (fun i=> (((aquaF V q A).owes n).stay i).joint) (fun i=> (((aquaF V q P).owes n).stay i).joint) (mark_payF V hW)) (fun i w hw hI=> congr_fun (congr_fun he i) w)⟩
lemma fromMS {Q:Booked B}(V:FullBook B)(X:MS_Data G Q)(b:Bool)(h:G.Simple)(hx:Fixed (col (skyline G q)) (Archive 4 X.bulk) true 4 1)(hk:b=true→ ∀ d:ℕ,∀ i:Plaid B d,TreeJet V q (Archive d ( X.marks d i )) (Land.read i) ) : ∃ (A: Land.Prescription B),A.team=q ∧ TaylorOKF X V A∧∀ d,∀ i,Houses (A.fees d i) (Land.read i) b := by
    have he (d:ℕ)(i: Plaid B d) := space b h hx ( Outlook.fieldD X.bulkOK (X.markOK d i) wisdom (( Q.law d i).moodQ)) (initialHF (Q.law d i) (sizeG i) (X.markOK d i)) (RootD X.bulkOK (Q.law d i) (X.markOK d i)) ( V:=V ) (fun t=>hk t d i); choose A HA H using he; exact ⟨⟨ q,A, fun d i=> ( HA d i 0 ).leading rfl ⟩, rfl, ⟨ hx,H⟩, HA⟩
theorem relaxed {Q:Booked B}(V:FullBook B)(X:MS_Data G Q)(h:G.Simple)(hx:Fixed (col (skyline G q)) (Archive 4 X.bulk) true 4 1) : ∃ (A: Land.Prescription B),A.team=q ∧ TaylorOKF X V A∧∀ d,∀ i,Houses (A.fees d i) (Land.read i) false:= fromMS V X false h hx (fun h=> Bool.noConfusion h)
end YM.FVA2.Teller.Desk
