import YM.FVA2.RiseMark
/-!
# Higher momentum jets in separated continuum labels.Assemble.Vertex
 -/
set_option autoImplicit false
set_option maxRecDepth 4096
noncomputable section
namespace YM.FVA2.Poesy
open YM.MS Function Set Filter Topology MeasureTheory Real
open MS.Plane MS.Koszul MS.Landau Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake MS.Orbit MS.Breeze MS.Book MS.Book.Convolve Flux
open MS.Osc MS.Osc.Snap MS.City MS.Rake.Geo MS.Land MS.Local.Physical MS.Port MS.Tide MS.Vista MS.Vane MS.Dial MS.Wind MS.High Wire
open scoped BigOperators ContDiff
variable {G: Gauge} {I W: Type} [LinearOrder W] {v:ℝ}
variable {A: Deck G}{B:Booked A}{S:MS_Data G B}
local notation "Υ" => frameF I v
local notation "Δ"=> constantP G I (PlanetD G)
-- use polymorphic cost uniformly along any mesh. Once chosen also emit on larger Type, need that for daughters. harmless large?
abbrev multiple (x:MS.Rake.Site G Unit)(I:Type): Site G I:= fun n _=>x n ()
-- main one row permit derivative. Does not carry comparison
structure Choice (v:ℝ)(M:MS_Data G B) where
    order: ℕ
    row: Site G Unit
    tag (I:Type)(p:ℕ): Tip (frameF I v) false false order ( multiple row I p )
    law (I:Type): Ven (fun _=> planeF) ( constantP G I ( PlanetD G ) ) (constantP G I (PlanetD G) ) ( approach ( frameF I v ) M) ( multiple row I )
    bound (I:Type)(K:Belt I)(h:Gold ( frameF I v ) K)(n:ℕ): Here false false K ( multiple row I n ) ( rateS K order )
variable (A0:Choice v S) (p:Rake.Label A)

def choice (v:ℝ)(M:MS_Data G B)(p:Label A):Choice v M:= ⟨ p.h,rowM (frameF Unit v) M p, fun I n=> tagF ( frameF I v ) M p n, fun I=> VeniceD ( frameF I v ) M p, fun _ K h n => (Architect ( fun _ :Unit=> p ) K ( b:=M ) h ).first () n ⟩
def derive (d:QP): Choice v S := ⟨ A0.order+1,rise d A0.row, fun _ _=> tip_der d ( A0.tag .. ), fun I=> venDer d (A0.law I),fun I _ h n=> rateDer d A0.order ( A0.bound I _ h n ) ⟩
open scoped Classical
variable {x y: Position W I}{U: Rake.Dance G I W}
variable (a: W→Choice v S)
-- same geometry, only varying one `turn` mark
abbrev rootsRow (I:Type)(v:ℝ)(M:MS_Data G B)(a:W→Choice v M): W→Site G I:=fun i=> multiple ( a i ).row I
abbrev Frozen (U: Rake.Dance G I W)(x: Position W I):= Fields x (fun _=>planeF) (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) (approach (frameF I v) S) (rootsRow I v S a) U
lemma of_choice {p: W→Label A}: Frozen ( choice v S ∘ p ) U x ↔ DOrd B Υ S p x U:= by rfl
-- construct arch using any deck label (nonempty unit? alternative from general nameD & tagD) 
omit [LinearOrder W] in
lemma passage (h:Mesh Υ x): Tour Δ Δ Υ x false ( approach Υ S ) ( rootsRow I v S a ) (Choice.order∘a):= ⟨ h,Geo.masterD ..,fun _ _=>tagD _ _ _, fun i n=>( a i ).tag I n,fun i=>( a i ).law I⟩
omit [LinearOrder W] in
lemma moneyCast (K:Belt I)(h:Gold Υ K): Arch K Δ Δ (approach Υ S) (rootsRow I v S a) ( Choice.order∘ a ):= by
    let U: Empty→Rake.Label A:=fun i=> i.elim; obtain X:= Architect U K (b:=S) h; exact ⟨ X.main,X.χ,X.states, fun i n=>( a i ).bound I _ h n ⟩
-- same story replicates on same parameters uniform. thru∞.
lemma footing (h:Mesh Υ x):∃ U:Rake.Dance G I W, Frozen a U x:= Vane.formal ( passage a h )
lemma walletCast (h: Mesh Υ x)(hv: Frozen a U x){w:Finset W}(he:w.Nonempty)(n:ℕ): Verdict Υ (charge ( Choice.order∘ a ) w) 0 ( U w n ):= closure (passage a h) ( moneyCast a _ gulfG ) ( moneyCast a _ westV ) hv he n
lemma from_copy {J:Type}{z:Position W J} {Q:Rake.Dance G J W}(h:Frozen a Q z)(f:I→J): Frozen a ( Dial.copy f Q ) (fun w=> z w ∘ f):= by -- adapt.
    let U:= Dial.copy f Q; let x:Position W I:= fun w=> z w ∘ f; refine ⟨?_,fun i=> ?_,fun s ht n=>?_⟩; · funext k i; change Q ∅ k (f i)=_; rw [h.1]; rfl
    · funext k t; change Q {i} k (f t)=_; rw [h.2.1]
    let K:= constantP G J ( PlanetD G ); let L:= rhs z (fun _=>planeF) K K ( approach (frameF J v) S ) Q s n; have hz : rhs x (fun _=>planeF) Δ Δ ( approach Υ S ) U s n = L ∘ f:= by
        funext i t; unfold rhs Src L; dsimp only [ x,U,rhs,Src,multi,lonely,expJ, copy ]; simp only [ Pi.add_apply,comp_apply, Finset.sum_apply,basis_copy ]; refine congr_arg₂ ( ( ·+· ):Law G→_ ) rfl (congr_arg₂ (·+·) ( Finset.sum_congr rfl (fun i hi=>?_)) ( Finset.sum_congr rfl (fun i hi=> Finset.sum_congr rfl (fun j _=>?_)) )); all_goals rfl
    obtain ⟨⟨k,hK⟩,hS,hL⟩:= h.2.2 s ht n; change collect ( U s n ) ∧ Job.train false ( rhs x _ _ _ _ U s n ) ∧ U s n= river (rhs x _ _ _ _ U s n); rw [hz]; exact ⟨ ⟨ k,fun i t=> hK _ _ ⟩,fun i=>hS ( f i ), congr_arg (· ∘ f) hL ⟩

def fox (x: W→QP): Rake.Dance G Unit W:= if H: ∃ U, Frozen a U ( fun w _=>x w ) then H.choose else 0
lemma choiceFox {x:W→QP}(hp:Injective x): Frozen a (fox a x) (fun w _=> x w):= by
    unfold fox; split_ifs with h; exact h.choose_spec; suffices he: Mesh (frameF Unit v) (fun p (_:Unit)=>x p) from False.elim ( h (footing a he ));
    intro i j hi; have he:0<‖x i-x j‖:= norm_pos_iff.mpr (sub_ne_zero.mpr (hp.ne hi)); refine ⟨⟨_,he,fun i=>?_⟩,⟨_,he,fun i=>?_⟩⟩ <;> simp [Geo.roots]
abbrev priceZ (x:W→QP)(w: Finset W)(n:ℕ):ℂ:= blade (fox a x w n) ()
lemma attach (h:Mesh Υ x)(hv:Frozen a U x)(i:I)(s:Finset W)(k:ℕ): U s k i=fox a ( pointI x i ) s k ():= by
    have hx:= from_copy a hv ( fun _ : Unit=>i ); rw [perfect (choiceFox a (detailI v h i)) hx]; rfl
lemma solveZ (h:Mesh Υ x)(hv: Frozen a U x)(i:I)(s:Finset W)(k:ℕ): blade ( U s k ) i=priceZ a ( pointI x i ) s k:= by unfold priceZ Vane.blade; rw [ attach a h hv i s k ]
-- specify Coordinates.Need bigger Cast definitions? Here lemmas enough. Nonempty Omega.S
end YM.FVA2.Poesy
