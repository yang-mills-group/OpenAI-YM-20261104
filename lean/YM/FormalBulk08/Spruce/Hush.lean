import YM.FormalBulk08.Spruce.Close
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Spruce
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K: KernelChoices}{X:Type}{E m n l e r j t d D R:ℕ}{F:Frame G d}{T:SectionData F}{W:Lab G K X}{H:Hol G}
variable {ρ:ChartRatio G}{o:Loc G 1}{Y:X→Anthem D G}
variable (l T ρ)(q:Quota F H W o D E R)(u:Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(C P:Pin W.scrolls)(hp:∀ i,C.N i ≤ P.N i) (Y)
-- top vector, cost publication elsewhere

def afloat (x:X): Matrix (Letter F) Unit Pence:= pantry F (fun _:Unit=>Y x) + debt l T ρ q a C P Y (peak C x)
def calmTop (x:Deck C): Anthem D G:= wave (T:=T) l ρ q a C P x Y-larch (tribal T q a (ρ:=ρ) P.N x) (debt l T ρ q a C P Y x) ()
lemma stitches (x:X): calmTop l T ρ Y q a C P (peak C x) = Y x-larch (bornY ρ W a F T q.horizon x (P.N x) (C.N x)) (afloat l T ρ Y q a C P x) ():= by rw [calmTop,afloat, wave_last,larch_add, Pi.add_apply]; unfold canopy; rw [sub_sub]; rfl
lemma echo_empty (x:Deck C)(h:x.b=W.neck x.a): calmTop l T ρ Y q a C P x=wave (T:=T) l ρ q a C P x Y:= by rw [calmTop, debt, bills_empty _ _ _ q _ C P Y _ _ h.le, larch]; simp only [Matrix.zero_apply,void_launch, Finset.sum_const_zero,sub_zero]
lemma refund (S W:Pence): PowerSeries.subst (runic W) (S.subst (wake W))= S:= by rw [subst_comp_subst_apply (tribe (wake_phi W)) (tribe (runic_phi W)),back_merge]; simp
variable {T l Y ρ}
variable (hy:∀ i,Clef o (Y i) l)(he:∀ i,Qual (Y i) o E (W.eagle (peak C i)))
include hp u hy he h hs ht hb
lemma neat (x:Turn C): Clef o (turf (T:=T) l ρ q a C P x Y) l:= by
    obtain ⟨hT,-⟩:= confidential q u h a hs ht hb C P hp hy he x.ups; exact migrate_w (V:=W.liftU x) (P:=graded W.liftF (W.trail P.N) x) a (W.liftH x) (scooped C x) d hT ((budge C P P hp (fun _=>le_rfl) u h a hs).aV x) ((W.V x.a).clock.adm _) h le_rfl
lemma seam (x: Turn C): signa (slots F) (feed (T:=T) l ρ q a C P x Y) l := fun i _ e hz=>voice_yields F (neat q u h a hs ht hb C P hp hy he x).fare i e hz
lemma winged (x:Deck C) : signa (slots F) (debt l T ρ q a C P Y x) l := by
    let g:=debt l T ρ q a C P Y; let V:= Pose.slots F
    have hh(i:X)(m:ℕ)(h:W.neck i ≤ m)(e:m ≤ C.N i): let z:Deck C:= ⟨⟨i,m,h⟩,e⟩; signa V (g z) l:= by
        induction h with
        | refl=> intro z; unfold g debt; rw [bills_empty _ _ _ q _ C P Y z.a z.b (show _ from le_refl _)]; exact signa_zero V l
        | @step j h' ht'=> intro z; let k : Turn C:= ⟨⟨i,j,h'⟩,e⟩; have hk:=seam q u h a hs ht hb C P hp hy he k; change signa V (debt _ _ _ _ _ _ _ _ k.ups) l; rw [fee]; exact signa_val _ (wake_phi _) (signa_mul (signa_sum hk (ht' (by omega))) ((mat_begins a h q hs ht hb i j _ h' (e.trans (hp i))).1.back))
    exact hh x.a x.b x.zone x.cap
lemma waltz (x:Turn C): ledge D ρ W x.a (P.N x.a) x.b d l a (calmTop l T ρ Y q a C P x.ups)= calmTop l T ρ Y q a C P x.bed:= by
    let P' := W.wood x.a x.b;let S(k:ℕ):=bornY ρ W a F T q.horizon x.a (P.N x.a) k; let Q:= graded W.liftF (W.trail P.N) x; let V:=instory ρ a W P.N x.ups; let R i:= migrates (D:=D) a Q P' K V ρ (W.liftH x) (scooped C x) d i
    let t:= debt l T ρ q a C P Y; let Δ:= echoR T ρ q a C P x; let Z:=wave (T:=T) l ρ q a C P x.ups Y; let B:=feed (T:=T) l ρ q a C P x Y; let M:= Roof.reborn a Q P' K V ρ (W.liftH x); have hT:=mat_begins a h q hs ht hb x.a x.b _ x.zone (x.head.trans_le (hp _)) (T:=T)
    have hz:= hT.1; have hD: larch (S x.b) Δ=R d∘ S (x.b+1):=hT.2
    have hg:Court o F (S (x.b+1)):= birth a h q hs ht hb x.a (x.b+1) _ x.ups.zone (x.ups.cap.trans (hp _)); obtain Ht:= winged q u h a hs ht hb C P hp hy he x.ups
    let U:= larch (S (x.b+1)) (t x.ups); have hp'(i): Clef o (U i) l:= larch_cleared (slots F) (fun _=>l) Ht hg.officers i
    have hx:Court o F (S x.b):= birth a h q hs ht hb x.a x.b _ x.bed.zone (x.bed.cap.trans (hp _))
    have hP : Story V (pink K.penalty Q.wing):=(budge C P P hp (fun _=>le_rfl) u h a hs).aV x; have ha:= (W.V x.a).clock.adm x.b
    have hm (T: Anthem D G) (y:ℕ)(hT: Wade o T y)(he:y≤ max d l) : R (max d l) T= R y T:= migrate_m _ _ _ _ _ _ _ _ hT hP.toVivid h _ he _
    have hV: R l ∘ U=larch (R d∘ S (x.b+1)) ((t x.ups).map M) := by
        have hp:R l ∘ U= R (max d l)∘ U:= funext fun i=> (hm _ _ (hp' i).fare (le_max_right ..)).symm
        rw [hp]; let Y:= S (x.b+1); have hf(i): Wade o (Y i) d:= (hg.officers i).fare.through (slotsFits ..)
        have hh:R (max d l) ∘ U=larch (R (max d l) ∘ Y) ((t x.ups).map M):=hammers ρ a _ _ _ _ _ o d _ _ _ (fun i=> (hf i).through (le_max_left ..)) hP ha h
        exact Eq.trans hh (congr_arg (fun z=> larch z ((t x.ups).map M)) (funext fun i=> hm _ _ (hf i) (le_max_left ..)))
    have heD:(t x.ups).map M= Δ⁻¹*(B+t x.bed):= by
       let b:= wrist ρ a W P x.a x.b; let D:= Δ⁻¹*(B+t x.bed)
       rw [show t x.ups=D.map (PowerSeries.subst (wake b)) from fee l T ρ q a C P Y x]; ext1 i j; let U:= epoch a Q P' K V ρ (W.liftH x)
       change M ((D i j).subst (wake b))= _; unfold M; rw [rele,mul_comm,forward_green]; have hh : U=b:= wrist_step .. |>.symm
       rw [show epoch a Q P' K V ρ (W.liftH x)= _ from hh]; exact refund (D i j) b
    unfold calmTop; rw [waved];
    change R l (Z-U ())= (R l Z-larch (S x.b) B ())-larch (S x.b) (t x.bed) ()
    obtain hZ:Clef o Z l:= (confidential q u h a hs ht hb C P hp hy he x.ups).1
    have he:R l (Z-U ())= R l Z-R l (U ()):= eq_sub_of_add_eq (by rw [show R l _ + _ = _ from (show R l (Z-U ())+ R l (U ())= R l ((Z-U ())+ U ()) from (migrate_add (P:=Q) (V:=P') a _ _ d (hZ.sub (hp' ())).fare (hp' ()).fare hP ha h le_rfl).symm),sub_add_cancel])
    rw [he,show R l (U ())=_ from (show _=larch (R d ∘ S _) _ () from congr_fun hV ()),←hD,larch_circuit,heD,←Matrix.mul_assoc,Matrix.mul_nonsing_inv _ hz.det,Matrix.one_mul,larch_add, Pi.add_apply,sub_sub]
end YM.FormalBulk08.Spruce
