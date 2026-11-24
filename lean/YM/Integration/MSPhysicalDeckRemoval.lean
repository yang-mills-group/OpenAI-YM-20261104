import YM.Integration.MSPhysicalDeckChange
import YM.FVA2.MixedRemoval
import YM.FVA2.MixedStory

/-! The genuine periodic physical perturbative source for independently booked
MS insertions, including sparse BRST cancellation on the cover and a power rate. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.MSPhysicalDeckRemoval

open Function Set Filter Finset Metric MeasureTheory Real
open MS MS.Mach MS.Outlook MS.Dock MS.Theater MS.Land MS.Local.Physical
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian Paint High Wind Rake Rake.Geo Vista Vane City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom Fleet Swirl Swirl.Near SpaceOut Menus Echo Tide
open Momentum Osc Fiddle Osc.Snap Belt Flux Wire High.Knobs MSPhysicalDeckChange
open scoped Topology ContDiff Interval Classical

variable {G : Gauge} {I W : Type} [LinearOrder W] {B₀ B₁ : Deck G}

abbrev rent (V : BookM B₁) (p : Team) (E : Fees B₀ B₁) (u : W → Rake.Label B₀) : W → Actor G :=
  fun w => Menus.rentM V p (E (u w).h (u w).item)

abbrev dressed (V : BookM B₁) (p : Team) (E : Fees B₀ B₁) (u : W → Rake.Label B₀) : W → Actor G :=
  fun w => Menus.scoreM V p (E (u w).h (u w).item)

omit [LinearOrder W] in
theorem ready (V : BookM B₁) (p : Team) (E : Fees B₀ B₁) (u : W → Rake.Label B₀) (hG : G.Simple) :
    ReadyP p (rent V p E u) ∧ ReadyP p (dressed V p E u) ∧
    Changes (rent V p E u) (rent V (Stripped p) E u) p ∧
    ∀ w, Menu p (dressed V p E u w) (rent V p E u w) := by
  exact ⟨⟨fun _ => billRentM .., fun _ x => rentedM V p x _ hG⟩,
    ⟨fun _ => decorM .., fun _ x => Menus.lawM V p x _ hG⟩,
    fun _ _ => rankVM .., fun w => MSPhysicalDeckChange.generator V p _⟩

section geometric
variable {A : Faces I} {L : I → Side} {R : Geo I} {Q : Seeds G I W} {X : Rake.Dance G I W}
local notation "Ψ" => outside L
local notation "ιW" => Orbit.uniform G I
local notation "m0" => (fun (_ : I) => planeF)
local notation "ρk" => (constantP G I (LowP G))
local notation "Y" => (constantP G I (PlanetL G))

theorem boarding (V : BookM B₁) (T : Prescription B₁) (E : Fees B₀ B₁) (u : W → Rake.Label B₀)
    (c : Berth (I := I) (W := W))
    (h₁ : ∀ w n i, Q {w} n i = frameL (c w i) (run (dressed V T.team E u w (R.η i) n)))
    (h₂ : ∀ s : Finset W, 2 ≤ s.card → Q s = 0)
    (hx : Crew Ψ ιW (Scope G (Wind.skyline G T.team) R.η) 0 A Q X) (he : ∀ s n, Knits (X s n)) :
    Fields (info c) m0 ρk Y (initials R T) (MSPhysicalDeckChange.site V T E R ∘ u) (voyage c X) := by
   refine ⟨?_,fun p=> ?_,fun s hs k=>?_ ⟩; · unfold voyage; rw [ hx.1 ]; funext i t p; dsimp only [ Fleet.vessel, Fleet.unload, Pi.zero_apply ]; rw [ map_zero,map_zero ]; -- sometimes no subM
   · let P:=u p; let Hw:= horizonM V T.team ( E P.h P.item ); let F:Rake.Site G I:=fun n i t=>lodging ( c p i ) ( Scope G Hw R.η n i t ); have hΨ : X {p}=F:= by
         refine special p (fun n=>?_) hx; rw [show Q {p} n = _ from funext ( h₁ p n ) ]; exact castP R.η (c p) ( aquaM V T.team ( E P.h P.item )) n L A
     unfold voyage; rw [hΨ]; funext n i t; unfold vessel; rw [Fleet.anchorC, dif_pos ( Finset.singleton_nonempty _ ), Finset.min'_singleton ]; exact unpack_home (c p i)
   obtain H:=hx.2 s ( Finset.card_pos.mp (by omega) ) k
   let f:=X s k; let E:= Vista.fort Ψ A ιW (Scope G (Wind.skyline G T.team) R.η) 0 X s k; have heL(i): f i 0=0:= by rw [show f i 0=Q s k i from H.1 i, h₂ s hs ]; rfl -- beta
   have hE:Toned E:=( knit_plus ( LiftE.knit ( gen_zip0 Ψ ( healthy G I ) A ) ( he s k )) ( campusK ( healthy G I ) (fun k=> feesBuy ( skyPC G T.team|>.owes k) R.η) (fun _ _=> knit0 ..) (fun i _=>he i) k (fun i _=> he s i ) ) ).1
   obtain hz := curve ( F:=f ) ( H:=E ) H.2 (anchorC c s) hE heL
   have hu : ( sailP m0 Y (voyage c X s k)+Rake.multi m0 (info c) ρk Y (initials R T) (voyage c X s) (voyage c X) k s )= (fun i t=> ( exp t:ℂ ) • vessel E ( anchorC c s ) i t):= by funext i t; apply f_inj ( anchorC c s i ); rw [ map_smul, show frameL _ (vessel E _ i t)=E i (exp t) from accountable .., show E i _=_ from π_src (R:=R) (X:=X) c T A s L (fun i n=> he i n |>.1) t k i,smul_inv_smul₀ ( by exact_mod_cast ( exp_pos t ).ne' )]
   unfold Trip; rw [hu]; exact hz
end geometric

section comparison
variable (φ : BookM B₁) (A : Prescription B₁) (E : Fees B₀ B₁) (u : W → Rake.Label B₀)
variable {M : Booked B₀} (S : MS_Data G M) (c : Berth (W := W) (I := I))
variable {V : Visa I} {P : Geo I} {L : I → Side} {x : Faces I} {l : Filter I} {μ : ℝ}
local notation "Yr" => rent φ A.team E u
local notation "Ur" => rent φ (Stripped A.team) E u
local notation "Qa" => goalsK c P.η Yr
local notation "Qr" => goalsK c P.η (dressed φ A.team E u)
local notation "g" => (Label.h ∘ u)
local notation "Cgx" => lifted P c

theorem assembly (hc : G.Simple) (hp : Clearance L x) (he : Vista.width L x) (hm : WidthW V P.η c)
    (ht : Mesh P (info c)) (hv : Sparse l c) (b : Bool)
    (hb : Fixed (col (skyline G A.team)) (Archive 4 S.bulk) true 4 1) (hImplements : Implements φ A.team S E) :
    ∃ (Z : Terrify W I) (X : Rake.Dance G I W), CCOrb G P.η A.team x L Qa b Z ∧
      (∀ i s, PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w => c w i) (x i) Ur (bury i s Z)) ∧
      DOrd M P S u (info c) X ∧ Judge P c V Z (toZ X) L l g ∧
      ∀ s : Finset W, s.Nonempty → ∀ n, Verdict P (Vane.charge g s) 0 (X s n) := by
   obtain ⟨hK,hP,H,hmenu⟩:= ready φ A.team E u hc; have heo : FlowSet V Qa:= moneyM c hm (fun i=>⟨ false,0,hK.badge i ⟩); let t:=A.team; obtain ⟨F,f,hF,hf,hT,h0,hpay⟩:= Ωgo ( P:=x ) hb heo hm.proper b hp he; obtain ⟨Z,X0,hZ,hZ',hX,h',hx⟩:= Ωgo (P:=x) hb ( show FlowSet V Qr from moneyM c hm (fun i=>⟨ false,0,hP.badge i ⟩) ) hm.proper b hp he;
   obtain ⟨U',D,hU,hD,hr⟩:= MSPhysicalDeckChange.covers φ A E u S hc ht hb hImplements; refine ⟨ f,D,hf,fun i s=> κglyph c i hK.badge hf ( fun _=>billRentM .. ) H,hD, ?_, fun s hs n=> hr s hs n |>.2.1 ⟩;
   have hUe : U'=voyage c Z:= Rake.perfect hU ( boarding φ A E u c (fun w n i => goals_m c P.η w n i) (fun s hs => goals_t c P.η (by omega)) hZ (Fleet.fee hZ (moneyM c hm (fun i=> ⟨false,0,hP.badge i⟩))) ); have hΩ(s:Finset W)(hp:s.Nonempty)(n:ℕ): toZ Z s n=toZ U' s n:= by
       funext i; let v(t:ℝ):= (Z s n) i (exp t) []; have he : (fun t:ℝ=> U' s n i t [])=v:= funext fun t=> by rw [ hUe, τv ]
       obtain HT:= ( hX s n i ).comp tendsto_exp_atTop; obtain HH:=hr s hp n|>.1.1 i; change Tendsto (fun t:ℝ=> U' s n i t [] ) _ _ at HH; rw [ he ] at HH; exact tendsto_nhds_unique HT HH
   refine ⟨ ⟨h0,zeroZ hD.1⟩,⟨ toZ Z,toZ F, zeroZ hZ.1,zeroZ hF.1, fun s hs n=>?_,hpay, fun n s=>?_ ⟩ ⟩; · rw [ hΩ s hs n ]; obtain ⟨ h,hv,hu⟩:= hr s hs n; exact ⟨marketV h hv hu,h.2.2⟩
   let a(i:I)(s:Finset W)(n:ℕ):= toZ Z s n i; let v i s n:= toZ F s n i; exact Filter.EventuallyEq.symm ( peaks (l:=l) (X:=a) (Y:=v) ( marked W ) Toy ( pointed _ (zeroZ hZ.1)) (fun i=> fun s _ n _=> Submodule.mem_top) ( pointed _ (zeroZ hF.1)) (fun i s _ n _=>Submodule.mem_top) (fun s n=> Echo.quote hv hP hK hb hc hmenu hZ hF n s) s n ) -- Params order

/-- The finite periodic Ward-corrected physical source and the independently
fixed MS ordinary report share a native positive power of cutoff separation. -/
theorem normalized (h : G.Simple) (he : Clearance L x) (hv : Vista.width L x)
    (hw : WidthW V P.η c) (hm : Mesh P (info c)) (hP : NearPlan l P V L μ) (b : Bool)
    (hb : Fixed (col (skyline G A.team)) (Archive 4 S.bulk) true 4 1) (hT : Implements φ A.team S E) :
    ∃ (Z : Terrify W I) (X : Rake.Dance G I W), (Z ∅ = 0 ∧ Fleet.toZ X ∅ = 0 ∧
      ∀ i s, PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w => c w i) (x i) Ur (bury i s Z)) ∧
      DOrd M (frameF I μ) S u Cgx X ∧ (∀ s n, PeakT l P mildG (fare g P Z s n - toZ X s n) ∧
        PeakT l P 0 (Fleet.toZ X s n)) ∧
      ∀ s : Finset W, s.Nonempty → ∀ n, Verdict (frameF I μ) (Vane.charge g s) 0 (X s n) := by
   have hs:= payTune c hm hP.vanish; obtain ⟨Ω,X,hQ,hX,hD,hK,hY⟩:= assembly φ A E u S c h he hv hw hm hs b hb hT; obtain ⟨Z,Y,H,hJ,hV⟩:= MSPhysicalDeckChange.covers φ A E u S h (posed c hm) hb hT; refine ⟨ Ω,Y,⟨ hK.blanks.1,zeroZ hJ.1,hX ⟩,hJ, fun s n=>?_, fun s hs n=> hV s hs n |>.2.1 ⟩; obtain hh : fare g P ( toZ X )=toZ Y:= clockShape P Cgx u hP.dimm hJ ( by rw [ ← re_n ]; exact hD ) (fun s hs n=> hV s hs n|>.2.1.1 )
   refine ⟨ hh ▸ dealP c hK hP,?_ ⟩; by_cases hs:s.Nonempty; exact Verdict.economic _ _ (hV s hs n|>.2.1.2.2); rw [Finset.not_nonempty_iff_eq_empty.mp hs, zeroZ hJ.1]; exact PeakT.zero -- orientation ▸ may motive
end comparison

section ordinary
open MS.Dial MS.Tide.PeakT FVA2 FVA2.Track

variable (Φ : FVA2.Warehouse G) (A : Prescription B₁) (E : Fees B₀ B₁)
    {M : Booked B₀} (S : MS_Data G M) (u : W → Rake.Label B₀) (R : Trial I W)
    (μ : ℝ) (l : Filter I)

def finite : Fleet.Terrify W I := fun s k i =>
  FVA2.Score.netE (Track.ticketRead Φ (dimT R.side i) (Rake.Label.h ∘ u) A.team
    (μ - R.profile.θ i) (fun j => E (u j).h (u j).item)
    (R.head i) (fun j => R.off j i) s) k

def Rows : Prop := ∀ (s : Finset W) (n : ℕ),
  PeakT.twin l R.profile mildG (fare (Rake.Label.h ∘ u) R.profile (finite Φ A E u R μ) s n)
    (fun i => Dial.tour S u μ (testP R i) s n)

theorem actual (hG : G.Simple) (hr : Uses R l μ)
    (hb : Fixed (col (skyline G A.team)) (Archive 4 S.bulk) true 4 1)
    (hT : Implements (Φ.native B₁) A.team S E) : Rows Φ A E S u R μ l := by
  obtain ⟨V, hV, hP⟩ := qualifies R.off hr.total hr.reality hr.upright hr.super
  obtain ⟨Z, Y, ⟨_, _, hN⟩, hY, ht, _⟩ := normalized (Φ.native B₁) A E u S R.off
    hG hr.clear hr.wind hV hr.knit hP true hb hT
  have hraw (i : I) (s : Finset W) : FVA2.Score.netE (Track.ticketRead Φ (dimT R.side i)
      (Rake.Label.h ∘ u) A.team (μ - R.profile.θ i) (fun j => E (u j).h (u j).item)
      (R.head i) (fun j => R.off j i) s) = bury i s Z := by
    apply (Track.finite_bridge Φ (FVA2.Matched.dimT_even R.side i) _
      (fun j => E (u j).h (u j).item) A.team _ _ _ s _).mp
    exact hr.reality i ▸ hN i s
  have hfin : finite Φ A E u R μ = ordZ Z :=
    funext fun s => funext fun k => funext fun i => congr_fun (hraw i s) k
  intro s n
  have hgeo := posed (μ := μ) R.off hr.knit
  rw [hfin, ← show ordZ (Fleet.toZ Y) s n = (fun i => Dial.tour S u μ (testP R i) s n) from
    funext fun i => shape_f S u μ hgeo hY i s n]
  rw [← funext (fun i => PeakT.ν_norm (Rake.Label.h ∘ u) (s := s) (P := R.profile) (n := n) i Z)]
  exact PeakT.projection ht s n

end ordinary

/-- The alternate dimensional marks are fixed on the original prescription
before any population, spatial configuration, profile, or perturbative order. -/
theorem purchased (Φ : FVA2.Warehouse G) {M : Booked B₀} (S : MS_Data G M)
    {O : Booked B₁} (D : MS_Data G O) (A : Prescription B₁) (hG : G.Simple)
    (hA : TaylorOKM D (Φ.native B₁) A) :
    ∃ E : Fees B₀ B₁, Implements (Φ.native B₁) A.team S E ∧
      ∀ {I J : Type} [LinearOrder J] (u : J → Rake.Label B₀) (T : Dial.Trial I J)
        (μ : ℝ) (l : Filter I), Dial.Uses T l μ → Rows Φ A E S u T μ l := by
  obtain ⟨E, hb, hE⟩ := MSPhysicalDeckChange.selected (Φ.native B₁) S D A hG hA
  exact ⟨E, hE, fun u T μ l ht => actual Φ A E S u T μ l hG ht hb hE⟩

end YM.Integration.MSPhysicalDeckRemoval
