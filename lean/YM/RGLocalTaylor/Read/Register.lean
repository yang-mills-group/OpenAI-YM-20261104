import YM.RGLocalTaylor.Read.Germ
import YM.RGLocalTaylor.Mayer.Calendar

/-!
# Full register and paid oriented reconstruction

Pre-reset render at *any* reanchored catalogue (origin inside) and any
headers used in shaping the later/Beam support representation. No need for a
separate issuance of narrower power credentials. `Vote` includes fixed Scalar/
kinetic partners unchanged and the full error on the same posting as the
actual `plusone`. Its weighted costs are before projection etc; account for
final localization costs at usage. Not-tear across alliances except via their
same-site/period declared transport. Derives estimates from proven analytic
worker Rollbook & Passport. Proofs based in part on RG01.Survive.Render.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor.Read
open Function Filter Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6 Shell SliceRows Control Window Coat Footprint Raw Matter
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Stained Shield
open PhysicalNext PhysicalNext.Repeat Height Greenbelt
open Gas Ursell Trees RG.Supply Org Roost Opera
open AnalyticBridge VerifiedReset Collection Extra.Iteration Match Song Refrain Geo Quotes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G}
variable {s μ C W : ℝ} {n : ℕ} {R R' : RG.Rep G f}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {I : Cash W s μ L Q o C T R'}
open RG01.Survive
variable {v ρ w δ β a : ℝ}{j l M r : ℕ}{g : Expansions H M}{x : H.ThinP→Orders M→ℝ}{z : H.ThinP→ℝ}
    (h:Rollbook χ g v j x z ρ) (X:Match.Alliance I H 1 0) (γ : ℝ)
    (take : H.fragrances→ℕ→Prop) (hT : ∀ i n, take i n → r ≤ n)

-- Term and integrated output; independent of reanchor and budget.
def opusPay (g:Expansions H M) : Magazine I → Config G c → ℝ := Sum.elim
    (fun i=> (-1:ℝ) • field take g (X.furrow i)) (fun _=>0)

def meticulous (g:Expansions H M) : Magazine I → Config G c → ℝ := Sum.elim
    (fun i=> (-1:ℝ) • field (fun i d=>¬take i d) g (X.furrow i)) (fun j=> opus I X χ γ (.inr j))

def voted (g:Expansions H M) : Collection.Source G c where
  logRead := choir (opusPay X take g) ∘ pennant I
  hardRead := (plusone I X χ γ).hardRead

def modeled (g:Expansions H M) : Collection.Source G c where
  logRead := choir (meticulous X (χ:=χ) γ take g) ∘ pennant I
  hardRead := (plusone I X χ γ).hardRead

include h
lemma renders : (plusone I X χ γ).logRead=(modeled X (χ:=χ) γ take g).logRead+(voted X (χ:=χ) γ take g).logRead := by
  have he z: opus I X χ γ z=meticulous X (χ:=χ) γ take g z+ opusPay X take g z:= by
    cases z with
    | inl i=>
      ext V
      change (-1:ℝ)*stream H χ V (X.furrow i)= _; rw [h.recover take]; exact mul_add ..
    | inr k=> exact (add_zero _).symm
  ext i U; let z:= (Song.pennant I i); change Song.Rim _ * opus I X χ γ z.2 (z.1.view U)= _; rw [he]; exact mul_add ..

variable {p:BudgetPoint}
    (hs:p.threshold=Pressure.temp s)(hp:p.B=radiusB s)(hi:p.order≤j)(hn:p.power≤n)
    (q:ℝ)(hq:0≤q)(hS:Sailor G p.threshold q j)(hr:j*q≤v)(hv:0<v)
    (hA: Quotes.preExponent p ≤ a)(hδ:0<δ)(hY:Ready H.smallAt p.B (fun i=>2^j*z i) (a+δ) w δ β)

variable (Z: Magazine I→RegularAddress c) (ha : ∀ i,(Z i).support=(scaleT p I i).support)
include hs hp hi hn hq hS hr hv hA hδ hY ha hT

set_option maxHeartbeats 400000 in
theorem release : Meadow.Budget p Z (opusPay X take g) ((ρ^r)⁻¹*(collars G δ s j n*(w*(1-β)⁻¹))) := by
  obtain ⟨hf,hW⟩:= Rollbook.clearing h take p w δ β a hs hp hi n hn q hq hS hr hv hA hδ hY r hT
  let v i:= (ρ^r)⁻¹*LeafReady.allowance p i j n z
  let k: Magazine I →ℝ:= Sum.elim (fun i=>v (X.furrow i)) (fun _=>0)
  let t:= (ρ^r)⁻¹*(collars G δ s j n*(w*(1-β)⁻¹))
  have ht i:(Z (.inl i)).support=Song.perf H (X.furrow i):= (ha _).trans (Song.reconnects I X i)
  have hZ (m : Magazine I) : let V:=opusPay X take g m; p.Regular (Z m).support V ∧ p.supBounds (Z m).site (Z m).support V (k m):= by
    intro V; rcases m with m|m
    · let x:= X.furrow m
      have hh:= hW x (Z (.inl m)).site (show (Z (.inl m)).site∈Song.perf H (X.furrow m) from (ht m) ▸ ((Z (.inl m)).anchor))
      rw [ht]; exact ⟨CouplingShape.reg_scale _ hh.1,by simpa only [abs_neg,abs_one,one_mul] using! CouplingShape.sup_scale (-1) hh.2⟩
    exact ⟨CouplingShape.reg_const _,by simpa only [abs_zero] using! (CouplingShape.sup_const (G:=G) (p:=p) (X:=(Z (.inr m)).support) (o:=(Z (.inr m)).site) 0)⟩
  refine ⟨k,fun i=> ?_,hZ⟩
  change SumBudget _ t; rw [← add_zero t]; apply Cost.sum
  · refine budget_mono (Cost.equiv (X.furrow) (hf i)) (fun m => ?_) fun m=> ?_
    · dsimp only; split; next => exact mul_nonneg (hZ (.inl _)|>.2.1) (Real.exp_pos _).le
      exact le_rfl
    dsimp only; split
    next h=>
      have hx : i∈perf H (X.furrow m) := by rw [← h,← ht]; exact (Z (.inl m)).anchor
      rw [if_pos (show i∈reachability (X.furrow m) from hx),ht]; exact le_rfl
    exact (Cost.equiv (X.furrow) (hf i)).1 m
  simp [SumBudget,k]

lemma recorded : Meadow.Budget p (Song.revolve Z ∘ pennant I) ((voted X (χ:=χ) γ take g).logRead) (readerCost (G:=G) p j n ρ δ s w β r):= by
  obtain ⟨f,hf,hV⟩:= release h X take hT hs hp hi hn q hq hS hr hv hA hδ hY Z ha
  obtain ⟨hc,hh⟩:= spiral _ _ f (fun i => (hV i).1) (fun i=>(hV i).2) hf
  exact ⟨_,fun i=> Cost.equiv (Song.pennant I) (hh i),fun i=> hc (Song.pennant I i)⟩

section passport
omit ha h hi hn hq hS hr hv hδ hY
variable (hg:Mayer.Passport H a w (turnFee p) δ p.order p.power M)  -- turnFee namespace?
include hg hδ
set_option quotPrecheck false
local notation "Y₀" => Mayer.issue H Chi.canonical M
/-- The expense on the physical width, including observer (`turnFee`). -/
theorem earning : (plusone I X Chi.canonical γ).logRead=(modeled (χ:=Chi.canonical) X γ take Y₀).logRead + (voted X (χ:=Chi.canonical) γ take Y₀).logRead ∧ ∀ (Z : Magazine I→RegularAddress c),
    (∀ i,(Z i).support=(scaleT p I i).support) →
      Meadow.Budget p (Song.revolve Z ∘ pennant I) ((voted X (χ:=Chi.canonical) γ take Y₀).logRead) ((Mayer.arcRadius G L s)^r)⁻¹:= by
  obtain ⟨A,a',C,d,V,t,u,B,q,e,K,θ,uJ,vJ,k,l,N,hG,hP,hF,hW,hL⟩:= hg
  have hN := N.oboe
  let z p:= Mayer.carrier N.conduit l M e uJ θ (Mayer.arcRadius G L s) ((M+4:ℝ)*u) p
  let v:=Mayer.arcRadius G L s
  have he : Rollbook Chi.canonical Y₀ V p.order (fun i t=> Mayer.prices N l M e uJ θ v ((M+4:ℝ)*u) i.val t) (fun k => z k.val) v :=
    ⟨Mayer.fullShape M H _,hW.holds,hW.scale,hW.pos,hW.recognizes,fun i V=> by rw [← Finset.sum_apply, Mayer.fullIdentity] ⟩
  refine ⟨renders he X γ take, fun Z hz=> ?_⟩
  have hS:Sailor G p.threshold q p.order:= by rw [hs]; exact ⟨fun c g hb=> N.weigh.stroke c g (hb.trans N.talent)⟩
  obtain ⟨f,h,hV⟩:= recorded he X γ take hT hs hp le_rfl le_rfl q N.income hS N.near N.position hA hδ (hp.symm ▸ hW.agrees) Z hz
  refine ⟨f,fun i=> budget_loosen (h i) ?_,hV⟩; unfold readerCost; rw [mul_left_comm]; exact mul_le_of_le_one_right (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hW.scale) _)) hL

end passport
end YM.RGLocalTaylor.Read
