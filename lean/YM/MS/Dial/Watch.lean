import YM.MS.Dial.Reg
/-! Geometry realizations of profile path for every physical separated tuple. Arbitrary degree tests.Knobs locality. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real High
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Fleet -- order
open Lattice
open scoped Topology ContDiff
open Vane PeakT Program Menus Swirl Swirl.Near
open Native Wilsonian
variable {W I:Type} {μ:ℝ}{n:ℕ}[LinearOrder W] {l:Filter I}
variable {G:Gauge}{B: Deck G}{M:Booked B}(S:MS_Data G M)(φ: LitBook B)(p:W→Label B)
   (T:Trial I W){A:Prescription B}
local notation "sV"=> p
local notation "gj"=> (Label.h ∘ p)
abbrev safeQ (G:Gauge){n:ℕ}(t: Fin n→ Labels.Pol G) : Prop:= True -- remove
-- result. time witnesses still coherent. Mom & regularity tied to symbols.
variable {V:Terrify W I}
def Cutoff (v:ℝ)(b:Bool)(A:Prescription B)(V:Terrify W I) : Prop:= ∀ i s, PhysicalSum G A.team ( v-T.profile.θ i) ( dimT T.side i ) b s (fun w=> T.off w i) ( T.head i ) ( ApplyM φ (Stripped A.team) A p ) (bury i s V)
structure coherent (M:Booked B)(S:MS_Data G M)(φ: LitBook B)(p: W→Label B)(T:Trial I W)(v:ℝ)(b:Bool)(A:Prescription B)(l:Filter I)(V:Terrify W I): Prop where
    init: V ∅=0
    cost: Cutoff φ p T v b A V
    ready (s:Finset W)(n:ℕ): twin l T.profile mildG ( fare ( Label.h ∘ p ) T.profile V s n ) ( fun i=> book S p v ( testP T i ) s n )
    bouquet (s:Finset W)(n:ℕ): twin l T.profile mildG ( fare ( Label.h ∘ p ) T.profile ( ordZ V ) s n ) ( fun i=> tour S p v ( testP T i ) s n )
lemma check_t (h:TaylorOK S φ A)(U:Uses T l μ)(hp:G.Simple)(b:Bool): ∃ V:Terrify W I,coherent M S φ p T μ b A l V:= by
    obtain ⟨ Z,Y,hY⟩:= Tide.called p T.off U.total U.reality U.upright U.super hp U.clear U.wind U.knit h b; have hv:=posed (μ:=μ) T.off U.knit; have hh(s:Finset W)(n:ℕ): Fleet.toZ Y s n=(fun i=> book S p μ ( testP T i ) s n):= funext fun i=> Point_t S p μ hv hY.scheme i s n;
    refine ⟨Z,hY.empty,fun i s=>?_,fun i u=> hh i u ▸ ( hY.compares i u ).1,fun i t=>?_ ⟩; exact U.reality i ▸ hY.native i s; rw [ ← show ordZ ( Fleet.toZ Y ) i t=(fun s=> tour S p μ ( testP T s ) i t) from funext fun s=> shape_f S p μ hv hY.scheme s i t ]; exact ( hY.compares i t|>.2 ) -- parser
variable {b:Bool}
lemma agrees {f g:I→ℂ}{u:ℂ}(he:twin l T.profile mildG f g)(hv:Tendsto T.profile.θ l atTop)(h:Tendsto g l (𝓝 u)): Tendsto f l (𝓝 u) := by obtain he:= (PeakT.topos mild_p hv he.2).add h; simpa only [zero_add,Pi.sub_apply,sub_add_cancel] using he -- function variant
variable [Fintype W] {x:W→QP}
lemma profile_t (h:coherent M S φ p T μ b A l V)(ht:Uses T l μ)(he:Injective x)(hc:Tendsto (testP T) l (𝓝 x)) (s:Finset W)(n:ℕ): Tendsto ( fare gj T.profile V s n ) l (𝓝 ( book S p μ x s n )) ∧ Tendsto ( fare gj T.profile (ordZ V) s n ) l (𝓝 ( tour S p μ x s n )):= ⟨agrees T (h.ready s n) ht.upright (( contin S p x he s n μ|>.2 ).tendsto.comp hc), agrees T ( h.bouquet s n ) ht.upright (( contin S p x he s n μ|>.1).tendsto.comp hc)⟩
omit [Fintype W][LinearOrder W]
lemma highest_zero (μ:ℝ)(x:Points n)(X:Fin n→Label B)(h:x∈ conf n): tour S X μ (fun i=> Theater.out (x i)) Finset.univ 0= Maxwell.Wick.moment G x (fun k=> Maxwell.reduceEq ( Milk.Lightning (X k))) := by
    let F (z:Fin n)(_i:Unit):= Theater.out (x z); have ht: Injective ( fun i=> F i () ):= Theater.out.injective.comp ( show Injective x.ofLp from h ); have he: Mesh ( frameF Unit μ ) F:= by
       intro i j hp; let b:= ‖F i ()- F j ()‖; have hz:0< b:= norm_pos_iff.mpr (by apply sub_ne_zero.mpr; exact ht.ne hp); refine ⟨ ⟨_,hz,fun k=>?_⟩,⟨ _,hz,fun k=>?_⟩⟩ <;> (cases k; simp only [ Geo.roots,frameF,Pi.zero_apply,exp_zero,Pi.sub_apply,mul_one ]; rfl )
    obtain ⟨Z,hZ⟩:= Vane.formal ( Rake.builder S he X ); obtain h:= Milk.Hymn he hZ () ( fun F h=> ( Dial.reports _ he hZ h _ ).1 () ); rw [shape_f S X μ he hZ _ _ _] at h; exact h -- defeq?
end YM.MS.Dial
