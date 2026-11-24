import YM.FVAAlt2.Plus.Remove
import YM.MS.Dial.Signals

/-! RichBook generalization. Adapted from `MS/Dial/Watch`, `MS/Dial/Signals`. -/

set_option autoImplicit false
noncomputable section

-- Dial/Watch
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real High
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Fleet -- order
open Lattice
open scoped Topology ContDiff
open Vane PeakT Program Menus Swirl Swirl.Near
open Native Wilsonian
variable {W I:Type} {μ:ℝ}{n:ℕ}[LinearOrder W] {l:Filter I}
variable {G:Gauge}{B: Deck G}{M:Booked B}(S:MS_Data G M)(φ: RichBook B)(p:W→Label B)
   (T:Trial I W){A:Prescription B}
local notation "sV"=> p
local notation "gj"=> (Label.h ∘ p)
variable {V:Terrify W I}
def CutoffPl (v:ℝ)(b:Bool)(A:Prescription B)(V:Terrify W I) : Prop:= ∀ i s, PhysicalSum G A.team ( v-T.profile.θ i) ( dimT T.side i ) b s (fun w=> T.off w i) ( T.head i ) ( ApplyMPl φ (Stripped A.team) A p ) (bury i s V)
structure coherentPl (M:Booked B)(S:MS_Data G M)(φ: RichBook B)(p: W→Label B)(T:Trial I W)(v:ℝ)(b:Bool)(A:Prescription B)(l:Filter I)(V:Terrify W I): Prop where
    init: V ∅=0
    cost: CutoffPl φ p T v b A V
    ready (s:Finset W)(n:ℕ): twin l T.profile mildG ( fare ( Label.h ∘ p ) T.profile V s n ) ( fun i=> book S p v ( testP T i ) s n )
    bouquet (s:Finset W)(n:ℕ): twin l T.profile mildG ( fare ( Label.h ∘ p ) T.profile ( ordZ V ) s n ) ( fun i=> tour S p v ( testP T i ) s n )
lemma check_tPl (h:TaylorOKPl S φ A)(U:Uses T l μ)(hp:G.Simple)(b:Bool): ∃ V:Terrify W I,coherentPl M S φ p T μ b A l V:= by
    obtain ⟨ Z,Y,hY⟩:= Tide.calledPl p T.off U.total U.reality U.upright U.super hp U.clear U.wind U.knit h b; have hv:=posed (μ:=μ) T.off U.knit; have hh(s:Finset W)(n:ℕ): Fleet.toZ Y s n=(fun i=> book S p μ ( testP T i ) s n):= funext fun i=> Point_t S p μ hv hY.scheme i s n;
    refine ⟨Z,hY.empty,fun i s=>?_,fun i u=> hh i u ▸ ( hY.compares i u ).1,fun i t=>?_ ⟩; exact U.reality i ▸ hY.native i s; rw [ ← show ordZ ( Fleet.toZ Y ) i t=(fun s=> tour S p μ ( testP T s ) i t) from funext fun s=> shape_f S p μ hv hY.scheme s i t ]; exact ( hY.compares i t|>.2 ) -- parser
variable {b:Bool}
variable [Fintype W] {x:W→QP}
lemma profile_tPl (h:coherentPl M S φ p T μ b A l V)(ht:Uses T l μ)(he:Injective x)(hc:Tendsto (testP T) l (𝓝 x)) (s:Finset W)(n:ℕ): Tendsto ( fare gj T.profile V s n ) l (𝓝 ( book S p μ x s n )) ∧ Tendsto ( fare gj T.profile (ordZ V) s n ) l (𝓝 ( tour S p μ x s n )):= ⟨agrees T (h.ready s n) ht.upright (( contin S p x he s n μ|>.2 ).tendsto.comp hc), agrees T ( h.bouquet s n ) ht.upright (( contin S p x he s n μ|>.1).tendsto.comp hc)⟩
end YM.MS.Dial

-- Dial/Signals
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real High
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Fleet
open Vane PeakT Program Menus Swirl Swirl.Near Native Wilsonian
open Puff Engine SplitP Actors Puff.Mom
open scoped Topology ContDiff
variable {W I:Type}{G:Gauge}{B:Deck G}[LinearOrder W] {F:Finset W}
   (φ: RichBook B)(L: W→Label B)(P:Trial I W){O:Booked B}{μ:ℝ} {b:Bool} {A:Prescription B} {V H:Terrify W I}
lemma measurePl (F:Finset W) (hp: CutoffPl φ L P μ b A V)(hx: CutoffPl φ L P μ b A H) (i:I): bury i F V=bury i F H:= classicalμ ( τ_nil .. ) (hp i F ) ( hx i F ) -- args
lemma separatePl (hp:CutoffPl φ L P μ b A V)(hx: CutoffPl φ L P μ b A H)(hv:V ∅=0)(he:H ∅=0): V=H:= by
   let t (v:Terrify W I)(i:I): Finset W→ T ℂ := fun s k=> v s k i; funext s n i; have hp1(y:Terrify W I)(hy:y ∅=0): Happy (marked W) (t y i):= Tide.pointed _ hy i;
   have hx1(y:Terrify W I)(x:y ∅=0): Puff.Log.Meter Trunk ( marked W ) (fun s=> bury i s y )= t y i:= Puff.Log.recheck _ _ _ (show t y i∈ allIndex _ _ from fun i _=> fun n _=> Submodule.mem_top ) ( hp1 y x );
   have hV := hx1 V hv; rw [funext (fun F=> measurePl φ L P F hp hx i), hx1 H he] at hV; exact ( congr_fun ( congr_fun hV s ) n ).symm
omit [LinearOrder W]
theorem LPT_to_MSPl {S:Gauge}{D:Deck S}{A:Booked D}(L:RichBook D)(F: MS_Data S A)(h:S.Simple) : ∃ Ξ: Prescription D, TaylorOKPl F L Ξ ∧ ∀ (W I:Type) (_:LinearOrder W)(P:Trial I W) (l:Filter I) (μ:ℝ)(u:W→Label D)(b:Bool), Uses P l μ → ∃! V:Terrify W I,coherentPl A F L u P μ b Ξ l V:= by
   obtain ⟨Ξ,H⟩:= High_stopsPl h F L; refine ⟨Ξ,H,fun W I _ P l μ u b hp=>?_⟩; obtain ⟨V,hV⟩:= check_tPl F L u P H hp h b; exact ⟨V,hV, fun y hy=> separatePl _ _ _ hy.cost hV.cost hy.init hV.init⟩
end YM.MS.Dial
