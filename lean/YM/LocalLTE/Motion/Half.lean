import YM.LocalLTE.Motion.Lilies
/-! # Sharp itinerary frequency
All labels common, support ball of E_q leaves specified only at epochs whose radius G design. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.East
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March Match
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open Height LocalLTE.Fan Pastel -- namespace edit
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {T₀ : Patch} {ℓ k j n: ℕ} {K : Teller G} {s a W U V g C' y A M K₀ r β δ q b v σ t w Λ γ: ℝ} {m : ℕ}
variable {X : ConnectedActivityE6.Target G K} {o:Target.Order G W}
variable {S:StepData c f} {T:Tube G S} {R R' : RG.Rep G f} (H : Cash W s a L X o U T R) {I: Cash W s a L X o U T R'} {χ : Chi}
local notation "B" => radiusB s
open PhysicalNext.Repeat Roost
open YM.LocalLTE FrameBox Inset PriceCompiler
open LocalLTE.Fan Field Fan.Bakers Vine
variable {κ :ℝ}
-- on actual same epoch. Cane fixed R=base. δ tune.Numeral input scope.`Works` inside any H.
variable (f':ℕ→ℕ) (Q:H.fragrances) (hQ:East.lectures H j n f' Q) {I:Type} {φ : Filter I} (A:I→Rep G f) (G':∀ i,Cash W s a L X o U T (A i))
    (hS:Stamp T) (hw:Peers L s K X W o k j m n κ)
    (hc:∀ i,let H:=A i; H.path=R.path ∧ H.p=R.p∧ H.activities.reg=R.activities.reg ∧ H.activities.forced=R.activities.forced)
    (hE:∀ i:ℕ, f' i≤j→∀ V:Config G f, flags R.p.threshold V=∅ → Tendsto (fun x =>(A x).activities.E i V) φ (𝓝 (R.activities.E i V)) )
    (hA:Tendsto (fun x=> (A x).beta) φ (𝓝 R.beta))
local notation "ζ"=> (Inset.cone (-(1/2)) (betaF G s L))
local notation "Y"=> Fan.postponement L s o
-- convergence requires Packed pin and occupancy all x.Interpolation lemmas separately
variable (hK:∀ i, Coup.License j (A i) κ (betaF G s L) f' (L.val* Pressure.radiusB s))
open Bakers
-- keep D fixed, Stream.Seam. `runeOrbit` deterministic facing.Assets.Transfer.
variable (χ : Chi)
open Price Tensor
local notation "E"=> Directions G c
-- cast across readable stanzas. Derived TERM. Truth no-off.Post.Permit linear. 
variable (m)
def offK (i:ℕ) (n _k:ℕ)(κ:ℝ)(R':Rep G f)(j:H.fragrances) : Config G c→ℝ:=
    let x:= stagnate n X.halo*radiusB s
    let g:= cane (Beam.dashboard H j).site
    if h : 2*(2*x) ≤ c.val then (-1:ℝ) • LocalLTE.FrameBox.realise g x κ (colorP (East.reins m H f' j χ R' i (Fold.trace (Beam.dashboard H j).site x h))) else 0 -- k unused

def way (j n k i:ℕ)(κ:ℝ)(R' : Rep G f) : Magazine H → Config G c→ℝ:=Sum.elim (fun q=> if East.award H f' j n k i q then offK m H f' χ i n k κ R' q else 0) (fun _=>0)
lemma reproduce {K':Cash W s a L X o U T R'} (j n k i:ℕ)(hr:R'.path=R.path)(hp:R'.activities.reg=R.activities.reg)(hk:R'.activities.forced=R.activities.forced) : awardO K' χ f' j n k i m κ= Song.choir (way m H f' χ j n k i κ R') ∘ pennant H:= by
    obtain ⟨u,c,⟨S₀,v,e1,k1⟩,m',b,t⟩:=R; obtain ⟨r,C,⟨S₁,V,e2,k2⟩,M,b₁,T₁⟩:= R';
    cases hr; cases hp; cases hk; unfold awardO
    let I: RG.Rep _ _:= ⟨u,C,⟨S₀,v,e2,k2⟩,M,b₁,T₁⟩
    rw [show East.strand K' χ f' j n k i m κ= East.way m H f' χ j n k i κ I from ?_]; rfl -- edit
    funext z; rcases z with z|z; swap; · rfl
    let A:= Match.staple (H:=H) (J:=K') rfl rfl rfl
    have h: East.award K' f' j n k i z ↔ East.award H f' j n k i z:= by
       unfold East.award; apply and_congr _ Iff.rfl
       rw [East.window,East.window,mem_filter,mem_filter]; apply and_congr Iff.rfl; exact ((East.literal_cal H A rfl k j n rfl rfl rfl f').1 z).symm
    unfold East.strand East.way; dsimp only [Sum.elim]; simp_rw [h]; split; next hi=> unfold East.offK; rfl
    rfl
-- color linear map general
section
variable {d:ℕ}{r:Site c} (A:Grove r)(u:ℕ)(κ:ℝ)(s:Seat c)(d':ℝ)
def linearO : LocalLTE.Cabana.Pkt (Directions G c) d→ₗ[ℝ] (Config G c→ℝ):= {
    toFun p:= fun v=>d'*LocalLTE.FrameBox.realise A u κ (colorP p) (s.view v)
    map_add' f g:= by
       funext v; unfold LocalLTE.FrameBox.realise; rw [Pi.add_apply]; simp_rw [sunwheel]; let w:= A.crook u Chi.canonical κ (s.view v); have ht (P: LocalLTE.Cabana.Pkt (Directions G c) d): MeasureTheory.Integrable (fun t:G.El=> Cabana.actual P (FrameBox.wheel t w)) G.probHaar:= ((LocalLTE.Cabana.moves P ω).continuous.comp (LocalLTE.FrameBox.wheel_moves _)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _); rw [← mul_add, LocalLTE.Cabana.actual_add]; exact congr_arg (d' * ·) (integral_add (ht f) (ht g))
    map_smul' c P:= by
       funext v; unfold LocalLTE.FrameBox.realise; rw [Pi.smul_apply]; simp_rw [sunwheel]; rw [LocalLTE.Cabana.actual_smul]; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; rw [integral_const_mul]; ring }
end
variable {m}
-- fixed-E-slot lap: X support ANY.Reg takes p to itself.trans.Bb.
include G' hK hA hQ hw hE hS hc
variable (hκ:Coup.License j R κ (betaF G s L) f' (L.val*Pressure.radiusB s))
include hκ
omit hQ Q in
lemma waves [φ.IsCountablyGenerated] (w:ℝ)(he:0<w) (o':Site c) (D:Support c) (J P':ℕ) (X':BudgetPoint) (u:ℕ) (hJ:pie P'+1≤ k)
    (hg:X'.Regular D (East.awardO H χ f' j n J P' m κ u) ∧ ∃ v,X'.supBounds o' D (East.awardO H χ f' j n J P' m κ u) v)(hp:∀ᶠ i in φ, X'.Regular D (East.awardO (G' i) χ f' j n J P' m κ u) ∧ ∃ v,X'.supBounds o' D (East.awardO (G' i) χ f' j n J P' m κ u) v) : ∀ᶠ i in φ, X'.supBounds o' D ((East.awardO H χ f' j n J P' m κ u)-(East.awardO (G' i) χ f' j n J P' m κ u)) w:=by
      have hs i:= East.reproduce m H f' χ (κ:=κ) (K':=G' i) j n J P' (hc i).1 (hc i).2.2.1 (hc i).2.2.2
      have ht := East.reproduce m H f' χ (κ:=κ) (K':=H) j n J P' rfl rfl rfl
      let g(q:RG.Rep G f):= choir (East.way m H f' χ j n J P' κ q) (pennant H u)
      simp_rw [hs] at hp ⊢; rw [ht] at hg; simp_rw [ht] -- danger hr var
      let U:= (pennant H u).2; let V:= (pennant H u).1; by_cases hz:∀ Q:Rep G f,g Q=0
      · apply Eventually.of_forall; intro i; change X'.supBounds _ _ (g R-g (A i)) _; rw [hz,hz,sub_self]; exact VerifiedReset.sup_le (VerifiedReset.sup_const (0:ℝ)) (by rw [abs_zero]; exact he.le)
      obtain ⟨R₀,hg₀⟩:= not_forall.mp hz
      have h' : (East.way m H f' χ j n J P' κ R₀) U≠ 0 :=fun h'=>hg₀ (by unfold g Song.choir; change Rim c • (East.way _ _ _ _ _ _ _ _ _ _ U ∘ V.view)=_; rw [h',show (0:Config G c→ℝ) ∘ V.view=0 from rfl,smul_zero])
      rcases hQ:U with Q|Q; swap; · rw [hQ] at h'; exact False.elim (h' rfl)
      rw [hQ] at h'; unfold East.way at h'; dsimp only [Sum.elim] at h'; split at h'; swap; · exact False.elim (h' rfl)
      next hx=>
         unfold East.offK at h'; dsimp only at h'; split at h'; swap; · exact False.elim (h' rfl)
         next ht'=>
            let e:=(Beam.dashboard H Q).site; let t:= stagnate n X.halo*radiusB s; let M:= LocalLTE.FrameBox.Fold.trace e t ht' (G:=G); let v'(R:Rep G f):= East.reins m H f' Q χ R P' M; let Z':= East.linearO (d:=pie P'+1) (G:=G) (cane e) t κ V (-Song.Rim c)
            have hEq (S : Rep G f): g S= Z' (v' S):= by
               funext v; change Rim c * (East.way _ _ _ _ _ _ _ _ _ _ U _)=_
               rw [hQ]; unfold East.way; dsimp only [Sum.elim]; rw [if_pos hx]; unfold East.offK; rw [dif_pos ht']; unfold Z'; rw [mul_comm]; change ((-1:ℝ)*_)*_=-_ *_; ring -- edit
            change X'.Regular _ (g R)∧_ at hg
            change ∀ᶠ i in φ,X'.supBounds _ _ (g R-g (A i)) _; simp_rw [hEq]
            have h':lectures H j n f' Q:=(show Slice H (East.lectures H j n f') _ from (mem_filter.mp hx.1).2)
            have ht:Tendsto (fun i=> v' (A i)) φ (𝓝 (v' R)):= by unfold v'; rw [East.leases]; exact East.shines H f' Q h' _ G' hS hw hc hE hA hK χ hκ P' hJ M
            refine Price.fairC ht (?_) (?_) w he -- edit
            · filter_upwards [hp] with i hx; change X'.Regular D (Z' _) ∧ ∃ v, X'.supBounds o' D (Z' (v' _)) v; rw [← hEq]; exact hx
            change X'.Regular D (Z' _) ∧ ∃ v,X'.supBounds o' D (Z' (v' R)) v; rw [← hEq]; exact hg
end YM.PhysicalNext.Repeat.East
