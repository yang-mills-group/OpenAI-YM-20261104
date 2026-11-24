import YM.Juniper.Bright.Trim
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Juniper.Bright
open ConnectedActivityE6 Blaze Silica March Captain PhysicalNext PhysicalNext.Repeat Height
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Shoot SliceRows Control Pulse Mask Raw Matter Pond Gas Ursell Trees Reserves Greenbelt Deck Mint Shield Stained
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Extra.Iteration Animals Corona Match Song Meadow
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G: Gauge} {c f L : Side} {P:Teller G}
      {W μ x C s t δ K u:ℝ} {χ:Chi}{Q: ConnectedActivityE6.Target G P} {o:Target.Order G W}
      {j n k m:ℕ} {S : StepData c f} {T:Tube G S} {R: Rep G f}
   {I:Cash W x μ L Q o C T R}{B:BudgetPoint}
open Refrain
/-! Fidelity to *same* assembly; motion receipt even after support cost. -/
variable {a M ℓ i v d w p A b D W' s':ℝ}{k':ℕ}
def leftOver (Z:Finset (Song.Magazine I)) (T:ℝ)(χ:Chi): Collection.Source G c := let R:=blank I
    ⟨choir (arrest (Song.opus I R χ T) (fun i=> i∉Z)) ∘ pennant I, (plusone I R χ T).hardRead⟩
lemma leftover_value (P: Finset (Song.Magazine I)) (i:ℕ): (leftOver P s χ).logRead i=if i∈ lantern I P then 0 else (plusone I (blank I) χ s).logRead i:= by
    set V:=pennant I i; have he:= garden_walk P i; rw [if_congr he rfl rfl]
    unfold leftOver; dsimp only [Function.comp_apply, arrest, choir]; split_ifs <;> first|rfl| exact (by ext U; simp_all) -- edit
lemma leftover_moves (Z:Finset (Song.Magazine I))(H:Collection.Local (posting B I) B (plusone I (blank I) χ s) t δ)
    (U: Signed) (u:Site c): Nonempty (((posting B I).read (leftOver Z s χ)).Moves U u):= by
   obtain ⟨η⟩:= H.transforms U u; let g:= arrest (Song.opus I (blank I) χ s) (fun i=> i∉Z)
   let T:= whirl (ι:=Song.Magazine I) U u; let p:= pennant I; let K:=p.trans (T.trans p.symm)
   have hp i: p (K i)=T (p i):= p.apply_symm_apply _
   have he x:= spirit (scaleT B I) g U u x
   refine ⟨⟨K,η.kp,(fun i=> ?_), (fun i=> ?_),η.forced_support,η.forced_inventory,η.forced_tests,(fun i V=>?_ ),η.valuesK⟩⟩
   · change (revolve _ (p (K i))).site=_; rw [hp]; exact (he _).1
   · change (revolve _ (p (K i))).support=_; rw [hp]; exact (he _).2.1
   change choir g (p (K i)) V=_; rw [hp]; exact congr_fun ((he _).2.2) _
lemma leftover_local (P: Finset (Song.Magazine I))(H:Collection.Local (posting B I) B (plusone I (blank I) χ s) t δ)
   (h:Meadow.Budget B (posting B I).reg (leftOver P s χ).logRead W'):Collection.Local (posting B I) B (leftOver P s χ) W' δ:=by
   obtain ⟨k,ha,hV⟩:= h; exact ⟨fun i=>(hV i).1,⟨H.family.sym,H.family.symtest,H.family.meas,H.family.meas_test,H.family.reads,H.family.reads_test,H.family.permit⟩,leftover_moves P H,⟨k,fun i=>(hV i).2,ha⟩,H.expensive⟩ -- conversion family proof

variable (B) (I) (N:Captain I j M d v ℓ A b p D w k' χ) (r:ℕ→ Shelf I n)
local notation "F"=> Song.opus I (blank I) χ s
local notation "η"=> radiusB x
-- compatibility with P low purchased enough at every fixed period. n is width anchor. r may retain MORE and price with stronger width.
include N
lemma pets {m :ℕ}(hp:B.threshold=Pressure.temp x)(ht:B.order≤j)(hK:B.B=radiusB x)(hP:B.power ≤ m)(h_σ: preExponent B ≤ a)
    (h: Ac.Hit (Captain.reachability (H:=I)) η (fun z=> if high I k z then N.markΦ z m else 0) a s') :
    Meadow.Budget B (locate I) (arrest (Song.sequence I (blank I) χ) (high I k)) s':= by
  have hS i : B.Regular (locate I i).support (Song.sequence I (blank I) χ i) ∧ B.supBounds (Song.locate I i).site (Song.locate I i).support (Song.sequence I (blank I) χ i) (N.markΦ i m):= Bright.every i ▸ pocketScore B I (blank I) χ N hp ht m hP i -- rewrite orientation
  let t i := if Bright.high I k i then N.markΦ i m else 0; have hh i:0≤t i:= by unfold t; split; exact (hS i).2.1; exact le_rfl
  refine ⟨t,fun x=> budget_mono (h x) (fun i=> ?_) (fun i=> ?_),fun i=>?_⟩
  · split; exact mul_nonneg (hh _) (Real.exp_nonneg _); exact le_rfl
  · dsimp only; split
    next he=> rw [if_pos (show x∈ Captain.reachability (H:=I) i from he ▸ (Song.locate I i).anchor)]; rw [hK]
              exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right h_σ (Nat.cast_nonneg _))) (hh i)
    exact (h x).1 i
  unfold t arrest; split; exact hS i; exact stamp0
omit N
lemma paths (σ C Λ:ℝ)(s:ℝ)(k:ℕ)(h:T.down.Bounds T.low σ C Λ)(ht:WilsonStartup.Decent T.low B) (hp: preExponent B / B.B ≤ σ/4)(hK: Real.exp (-(σ/4)*k)*octaveNeed G B T.low σ C Λ R.beta s ≤ s')  : Meadow.Budget B (strings T.down (n:=c) B) (arrest (sounding T.down T.low R.beta s) (fun x=> k≤Meadow.arc T.down x)) s' := by
   obtain ⟨f,hh,hF⟩:= Meadow.lent (c:=c) B T.down T.low _ s h ht hp
   refine Bright.pays_less hK ⟨fun i=> if k ≤ Meadow.arc T.down i then f i else 0,?_ ,fun i=>?_⟩
   · have he:= h.width; refine Meadow.arch_tail _ _ _ ?_ (by positivity) (fun i=>(hF i).2.1)
     exact hh
   dsimp only; unfold arrest; split_ifs; exact hF i; exact stamp0

lemma rich {u: ℝ} (P:ℕ→Finset (Magazine I)) (b:Magazine I→Prop)(ht: ∀ i, F i ≠ 0 → ¬b i→ ∀ᶠ n in atTop,i∈ P n)(hs:Meadow.Budget B (scaleT B I) (arrest F b) δ)
    (h: Meadow.Budget B (scaleT B I) (F) t) (hp:0<u):
    ∀ᶠ n in atTop, Meadow.Budget B (posting B I).reg (leftOver (P n) s χ).logRead (turnFee B*(δ+u)) :=by
   let t(i:ℕ) (j:Magazine I) := ¬ b j∧ j∉ P i
   let K i (j:Magazine I):= j∉ P i
   have hv j (hj:F j≠0): ∀ᶠ i in atTop, ¬ t i j:= by
     by_cases he:b j; filter_upwards with i; exact fun h=> h.1 he
     exact (ht j hj he).mono fun i hi p=> p.2 hi
   filter_upwards [gone (F) t h hv hp] with i hi
   have hK:Meadow.Budget B (scaleT B I) (arrest F (K i)) (δ+u) := by
     refine Bright.splits _ _ _ ?_ (camp _ (K i) hs) hi
     funext j; by_cases hz:b j <;> by_cases hq:j∈ P i <;> simp [t,K,arrest,hq,hz]
   obtain ⟨f,hf,hF⟩:= hK; obtain ⟨hh,ht⟩:= Song.spiral _ _ f (fun i=>(hF i).1) (fun i=> (hF i).2) hf
   exact ⟨(fun j:Seat c × Magazine I=> Song.Rim c*(turnFee B*f j.2)) ∘ Song.pennant I,fun i=> Cost.equiv (pennant I) (ht i),fun i=> hh (pennant I i)⟩
include N
lemma paysT (k:ℕ)(hp:B.threshold=Pressure.temp x)(ht:B.order=j)(hK:B.B=radiusB x)(h_σ: preExponent B ≤ a)
    (σ C' Λ : ℝ)(hT:T.down.Bounds T.low σ C' Λ)(hw:WilsonStartup.Decent T.low B)(hS: preExponent B / B.B ≤ σ/4)
    (hξ: Real.exp (-(σ/4)*B.B)*octaveNeed G B T.low σ C' Λ R.beta s ≤ s')
    (hX: Armada Q L μ a x i D j k')(h: Ac.Hit (Captain.reachability (H:=I)) (radiusB x) (fun z=> if high I k z then N.markΦ z B.power else 0) a δ)
    (hc:∀ i:I.fragrances, F (.inl i)≠0 → ¬high I k i →∀ᶠ m in atTop,i∈ (r m).slate k) (hu:0<u):
    ∀ᶠ m in atTop, Collection.Local (posting B I) B (plusone I (blank I) χ s) t K → Collection.Local (posting B I) B (leftOver (selection (r m) k B.B m) s χ) (turnFee B*((δ+s')+u)) K :=by
   let P m:= selection (r m) k B.B m; let v:=s; let kcopy(i : Magazine I):Prop:=i.elim (high I k) (fun i=>B.B ≤ Meadow.arc T.down i)
   have h' : ∀ i:Magazine I, F i≠0→¬ kcopy i → ∀ᶠ n in atTop,i∈ P n:= by
     rintro (i|i) hi hh; exact (hc i hi hh).mono fun m hm=> inl_mem_disjSum.mpr hm
     obtain ⟨⟨w,j⟩,hv⟩:= (Meadow.rollers c).surjective i
     have ht : melody T.down j ≤ B.B:= by rw [←arc_receipt T.down w j,show legs w j=i from hv]; exact (lt_of_not_ge hh).le
     filter_upwards [burgeoning T.down B.B j ht] with m hm using inr_mem_disjSum.mpr (mem_map.mpr ⟨(w,j), mem_product.mpr ⟨mem_univ _,hm⟩,hv⟩)
   have hz : Meadow.Budget B (scaleT B I) (arrest F kcopy) (δ+s'):=by
     obtain ⟨f,hf,hF⟩:= pets I B N hp ht.le hK (le_refl B.power) h_σ h
     obtain ⟨g,hg,hG⟩:= paths (T:=T) B (R:=R) _ _ _ s B.B hT hw hS hξ -- remove poss arg
     refine ⟨Sum.elim f g,fun i=> Cost.sum (hf i) (hg i),fun i=>?_⟩
     rcases i with i|i <;> first| exact hF i| exact hG i
   obtain ⟨f,hf,hF⟩:= Song.books B I (blank I) χ N hp ht.le hK s h_σ hX (le_refl B.power) hw hT (hS.trans (by have hx:=hT.width; linarith))
   exact (rich I B P kcopy h' hz ⟨f,hf,hF⟩ hu).mono fun i hi h=> leftover_local _ h hi
end YM.Juniper.Bright
