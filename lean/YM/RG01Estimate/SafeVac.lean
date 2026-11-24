import YM.RG01Estimate.Pews
/-!
 # Quantitative local Vacuum recovery (prerevision) on ONE profile stack of a purchased Loom.

 This theorem is up to the construction's *pre* Normalization chart (`Collection.Local`) from
 VERIFIED_RESET_STEP. Relevant/counterterms should reclose by an exact full polynomial + separately
 estimated sector, not infimum. Takes the specified kinetic α; no scalar/E sums discarded.
 Retains Ψ output regular entries and their supports (no free simultaneous basis change);
 permits picked path widths across candidate and actual. Error norm E measured on λ^+ after merger.
 K result includes all attachments here, not claiming unchanged after the kinetic sweep.

 Requires supplied Frame stamps per stage & Herder inputs, not asserted automatically.
 Polynomial K certified before forcing. g-power Radius not depending on shifts at physical β offsets.
 Still unmarked only. Use this BEFORE any higher-arity polynomial selection or root projections.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RG01Estimate.Precise
open PhysicalNext.Repeat
open Filter Function Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior Gauge
open Matrix Finset Push AbsoluteSums Gas Extra.Iteration Extra.Iteration.Calibration Bid Bloch Laurent UVNext UVNext.PricedKernels
open Pressure AnalyticBridge VerifiedReset Collection Quotes PriceCompiler Uniform RG.Shoot
open ConnectedActivityE6 Testing SectorMeasure Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural Macrame
open Sienna Token Lantern Lapis Shellac Fare Planned.JetPort Pane
open Laplace Courtyard Receipt ConnectedActivityE6.Coat Roost Boulevard Award
open Evoc Deck AbsoluteSums.Animals Board Promise Slide Trio Abacus
open Progress.DirectedRecipe Next.Scheduling
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{U:Alloy X D}(R:Factor U)
   {d n i j r ℓ e :ℕ} {Y:Type}
section pose
variable {c f:Side}{S:StepData c f}(p:BudgetPoint)(D:PathData G) (c':Clip)
   (M: Leads G c) (Z:Collection.Listing G c)
-- post-reg append of candidate labels *incl every stencil*
-- no assertion post-local on the guessed formal basis unless seals hold. peel constructive.

def Delivered (β α:ℝ)(U:Config G f→ ℝ)(τ q w:ℝ)(Z:Listing G c)(v:Collection.Source G c) : Prop :=
    let t:ℕ→ Config G c→ℝ := fun i=> Abacus.tariff i (Caddy.righty M.trunk) 0
    let e:= revise v (v.logRead-t)
    let y:= revise v t
    (∀ X':Config G c,S.push β U X'=earlyValue Z D c' p v β τ α X') ∧
      Collection.Local Z p y M.bill w ∧ Collection.Local Z p e q w ∧ Collection.Local Z p v (M.bill+q) w ∧
        ∃ e:ℕ↪ℕ,(∀ i,Z.reg (e i)=M.listing.reg i) ∧ (∀ i,t (e i)=M.trunk i) ∧ ∀ i,i∉Set.range e→t i=0

lemma numbering_kept (p:BudgetPoint) (Z:Listing G c)(l n:ℕ):
     let t:ℕ→ Config G c→ℝ:= fun i=> Abacus.tariff i (Caddy.righty M.trunk) 0
     let M₀ := Marlin.pluck p (Marlin.lodge (Caddy.stores Z M.listing.reg) l n)
     ∃ e:ℕ↪ℕ,(∀ i, M₀.reg (e i)=M.listing.reg i) ∧ (∀ i,t (e i)=M.trunk i) ∧ ∀ i,i∉Set.range e→ t i=0:= by
   intro t X
   let q:= Caddy.e; let y:= Marlin.leanU c; let z (i:ℕ):ℕ:=q.symm (.inr i)
   let Y (j:ℕ):ℕ:=y.symm (.inl j)
   let e:ℕ↪ℕ:= ⟨Y ∘ z,(y.symm.injective.comp Sum.inl_injective).comp (q.symm.injective.comp Sum.inr_injective)⟩
   have h i : y (Y i)=.inl i:= y.apply_symm_apply _
   have hv i : q (z i)=.inr i:= q.apply_symm_apply _
   refine ⟨e,fun i=>?_,fun i=>?_,fun i hi=>?_⟩
   · change Sum.elim (Caddy.stores Z M.listing.reg).reg _ (y (Y (z i)))= M.listing.reg i; rw [h]; change (Sum.elim _ M.listing.reg (q (z i)))= M.listing.reg i; rw [hv]; rfl
   · change Sum.elim (Caddy.righty M.trunk) _ (y (Y (z i)))=_; rw [h]; change Sum.elim (0:ℕ→ Config G c→ℝ) M.trunk (q (z i))= M.trunk i; rw [hv]; rfl
   change Sum.elim _ (Song.choir _) (y i)=(0:Config G c→ℝ)
   cases hx: y i with
   | inl v=>
         change Sum.elim _ M.trunk (q v)=(0:Config G c→ℝ)
         cases hq:q v with
         | inl u=> rfl
         | inr v'=> exact False.elim (hi ⟨v', y.symm_apply_eq.mpr (by rw [hx, show z v'=v from q.symm_apply_eq.mpr hq.symm]) ⟩)
   | inr v=> unfold Song.choir; simp
end pose
section data
variable {N m p : ℕ}
local notation "J" => U.B.a.clock.J (m+1)
local notation "I" => U.B.a.clock.J m
local notation "P" => U.B.a.clock.adm (m+1)
local notation "L" => D.L (U.B.a.clock.J (m+1))
local notation "B" => (U.B.a.budget m)
local notation "B'" => U.B.a.budget (m+1)
local notation "χ" => Chi.canonical
local notation "γ" => U.B.kin.alpha N m
local notation "x" => U.B.a.clock.hatBeta m
local notation "𝕊" => (U.B.a.clock.op m p)
local notation "f'" => U.B.a.S.side (m+1) p
local notation "c" => U.B.a.S.side m p
set_option quotPrecheck false
local notation "H₀" => ((U.B.a.S.oneStep m p).exact_size)
local notation "T" => ships U.B N m p
local notation "A₀" => X.O
local notation "X₁" => (R.target (U.B.a.clock.J (m+1)) (U.B.a.clock.J m))
local notation "B''"=> Meadow.studio ℓ (radiusB x)
local notation "z" => Trio.base ℓ (radiusB x)
local notation "D''" => 2*Trio.base ℓ (radiusB x)
local notation "C₀" => Precise.shape U m ℓ
local notation "η₀" => Trio.coverTicket ℓ
variable {β:ℝ}
local notation "ε" => gStep β
local notation "qt" => gStep β^(r+1)
local notation "Q'" => (Time.forecastK U.B.a m R.scout β)
variable (u₀ : Precise.Horizon X D (U.B.a.clock.J (m+1)) (U.B.a.clock.J m) ℓ r n (U.B.a.clock.adm (m+1)))
   {s a b h :ℝ→ℝ}(F₀: Folio D (U.B.a.clock.adm (m+1)) u₀ e s a b h)
local notation "Ε" => u₀.Y (U.B.a.clock.hatBeta m)
local notation "fQ" => wick G L u₀.y x
local notation "k''" => Precise.sideFee D R.shape I J x
local notation "k₀" => (Precise.sideFee D R.shape I J x + Precise.tiny G L x)
local notation "γ₀" => Precise.wage D P u₀ F₀ x
variable (u' : OpenAt D R.shape (U.B.a.clock.adm (m+1)) u₀ F₀ (R.scout (U.B.a.clock.J (m+1)) (U.B.a.clock.J m)) (U.B.a.clock.hatBeta m))
    (s':ℕ→ Finset Y)(hs:∀ i,∀ᶠ z' in atTop,i∈s' z')
    (A: Insured U N m d (U.B.a.S.oneStep m p).exact_size β Y)
    (M:Leads G (U.B.a.S.side m p)) (V:Herder β ((U.B.a.S.oneStep m p).exact_size) A u₀ M s a b h e)
    (hr: Routed.Allowed R)
include R hr u' hs V
set_option maxHeartbeats 500000 in
lemma delivered (ht: m<N)(hN:β∈ Shoot.band U.B.a (m+1))(hj:2 ≤ r)(hm:1 ≤ n)(h' : r ≤ J)(hv:0≤ s x) (hn: house (X₁).halo (radiusB x) d (Fate.steps r)+optic (X₁).halo (radiusB x) d+5 ≤ B'')(hM : Meadow.studio (X₁).halo (radiusB x)≤B'') (hν:4* B''+16 ≤ (c).val) (hK: 2*z<(c).val) (τ:ℝ) (hτ : Inherit.Debits A.rep A.sacrifice τ) (hq:τ ≤ Fate.debt r G (D.L (U.B.a.clock.J (m+1))) x) :
   ∃ w Z v, Delivered (S:=(𝕊)) (B) (T).down (T).low M β γ A.rep.eval w (Routed.retention R m * τ+qt * γ₀) Q' Z v:= by
   let H:= (𝕊); let K:= T
   have hi : β∈ band U.B.a (m+1):= hN
   have hp : A.rep.beta∈ band U.B.a (m+1):= by rw [A.β']; exact hi
   -- EquivalentParameters for true operation
   have hy : Routed.EquivalentParameters (A:=U) N m p A.rep:= ⟨A.pathU,A.clip,A.point,hp,(by rw [A.point]; exact A.point ▸ A.legal)⟩
   obtain ⟨E,hE⟩:= Routed.supplies R A.rep hy ht -- order
   let X': Match.Alliance E E 1 0:=Match.staple rfl rfl rfl
   let D':= Beam.marquee E (B)
   have hT:= Routed.step R hr ht E hE hp hy.point X' rfl A.sacrifice r hj h' hτ hq
   let R':= Routed.retention R m*τ; let E':= p -- main index
   have hz:=sunrise R β H₀ A u₀ F₀ M u' ht hi s' hs E hE V hr hj h' hm hv hn hM hν
   have hL:= Board.all_pay R ht H₀ E hE X'
   have hB:= Caddy.low_inherits B χ E X' γ A.sacrifice r hL
   have ht':0<β:= (half_pos (by have hf:= U.B.a.fits.delayed (m+1); exact zero_lt_one.trans hf)).trans_le hi.1
   let v:=qt; have hg:= Caddy.invoice B χ E X' γ A.sacrifice r (fun i=> Evoc.board E A.music r (s' i) i)
       (Evoc.exhausts E A.music r A.sacrifice A.coverage s' hs) hB hT.1 (show 0<v from pow_pos (Fare.gS β ht').1 _)
   obtain ⟨i,h',Xq,hq,hΨ⟩:= (hg.and hz).exists
   let X:= Evoc.board E A.music r (s' i) i
   obtain ⟨hB,hU,hL⟩:=h'
   let t:= Caddy.cut χ E X' γ A.sacrifice r X; let F:= Evoc.node E A.music r A.sacrifice χ (B) γ i (s' i) A.cost (show (B).B=radiusB x from rfl) (show house (X₁).halo (radiusB x) d (Fate.steps r)≤ B'' from by omega) hM
   obtain ⟨Z⟩:= Tree.select (𝕊).ratio (𝕊).patch.odd_side
   have hS:=Precise.builds R β H₀ A u₀ F₀ u' ht hi E hE M V s' i t hU ((levy_erh R) ▸ hB) F hL (Evoc.pasture E A.music r A.sacrifice A.coverage χ B γ i (s' i) A.cost ..) hK hν Z Xq hq hΨ
   dsimp only at hS
   obtain ⟨hZ,f,hf,hI,hF,hS⟩:=hS
   refine ⟨_,_,_, hZ,hI,?_,hS, numbering_kept ..⟩
   -- absorb
   rw [hf,add_sub_cancel_left]; exact hF
end data
end YM.RG01Estimate.Precise
