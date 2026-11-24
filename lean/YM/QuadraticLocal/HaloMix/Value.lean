import YM.QuadraticLocal.Rough.Lanes
import YM.QuadraticLocal.HaloMix.Pound
/-!
# At the pre-porch layout, obtain a stronger bill on MARKED (plus unmarked
 true) K when the inlet can afford another tilt. Not scaling marker radii
 by a coupling power per step, only using a proportional old budget in **Theta**
 including all higher arities; use same published mark weights w here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QuadraticLocal.Lanes
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
open RemainderComparison RemainderComparison.Lyric RemainderComparison.Mosaic RemainderComparison.Muse RemainderComparison.Sleet RemainderComparison.Serif RemainderComparison.Typeface RemainderComparison.Flues
open Marker Mallow Ovens Progress.DirectedRecipe
variable {ι V' : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J I:ℕ}(χ:Chi)
variable (U:Pad H j χ) {τ κ K Y γ V T0:ℝ}
variable (M:ι→Portrait R α) (x' y:α) (l:ι→ℝ)
variable (h:Roles H χ U k s J I a d e K σ Y γ V T0) (hh:Motto (brand M x') l 0 H τ K Y I)
local notation "Vx"=> brand M x'
local notation "Vy" => brand M y
variable {R':Rep G f} (H':Cash W x μ L Q o C T R')(D:Match.Alliance H' H 1 0)
    (P':BudgetPoint)(hp : P'.B=radiusB x) (ht:P'.threshold=Pressure.temp x)
    (E₀:ℕ→RegularAddress c)(V₀:ℕ → Config G c→ℝ)
variable [DecidableEq V']{Jm:Marker.Census V'}
local notation "Φ" => Poly Jm
variable (z:ι→Marker.Poly Jm) {gP:V'→ℝ} {kZ:ℕ}(hZ : Chorus Jm gP Set.univ z kZ)

local notation "XA" => Refrain.read H' D χ E₀ V₀
local notation "HL" => fun y:α => Lane (brand M y) H χ Set.univ l 0 z H' D


variable (hT : Glit.LeasePlot (brand M x') H l Y τ)
local notation "TZ"=> ( Set.univ : Set ι )
variable [Countable ι]
variable {origins : V'→ Site c}
local notation "K!"=> Flues.kettle H χ M x' l Set.univ 0 H' D E₀ V₀
local notation "Ψ"=> stuff (funnel H M x' H' D) (badge H M x' H' D)
local notation "ϕ"=> Flues.candle M x' S
open Push Push.Corrected
variable (hc:∀ i, Width.LocalCharge (G:=G) P' origins (Flues.candle M x' S i) (fun _=> z i))

open Throng
variable {εm:ℝ}(H0:1≤εm) (hb: Glit.LeasePlot (brand M x') H (Lyric.mulScale εm l) Y τ) (hs:Motto (brand M x') (Lyric.mulScale εm l) 0 H τ K Y I)
local notation "Ψm"=> Lyric.mulScale εm l
local notation "F"=> funnel H M x' H' D
local notation "Ξ"=> (K!)
local notation "κw"=> Flues.kettle H χ M x' Ψm Set.univ 0 H' D E₀ V₀
local notation "sh"=> shaft H χ U M x' l H' D P' ht E₀ V₀ z hc
local notation "sh'"=> shaft H χ U M x' Ψm H' D P' ht E₀ V₀ z hc
local notation "fee0"=> (Real.exp ((-Q.mark L μ x)*(1/2:ℝ)) * gStep R.beta ^s)
include hc ht
set_option quotPrecheck false
-- this conversion retains Arrivals.We.Scope.σ
lemma bankers (Y': α) (i:ℕ) (U' : Config G c) : (sh').val i Y' U'= (((εm^Verse.load Set.univ ((Flues.kettle H χ M x' l Set.univ 0 H' D E₀ V₀).score i)):ℝ):ℂ) • (sh).val i Y' U':=by
   -- if actually bank serial #, use excursion exact; otherwise both zero by funnel
   let Lw:= Ψm; by_cases hi:i∈ Set.range (F)
   swap
   · change (κw).song Set.univ z _ _ _ = _ • (Ξ).song Set.univ z _ _ _ ; rw [cleared _ χ M x' _ _ _ 0 _ H' D _ _ _ hi,cleared _ χ M x' _ _ _ 0 _ H' D _ _ _ hi,smul_zero]
   obtain ⟨i,rfl⟩:=hi; let A:=Mosaic.parade (brand M Y') H χ i.1.val i.2; change (κw).song _ _ _ _ _ = (_ : ℂ) • (Ξ).song _ _ _ _ _
   rw [Flues.boils, Flues.boils]; rw [show (Ξ).score (F i)=A.letters from ?_]; unfold Verse.paint; simp_rw [show ∀ (l:ι→ℝ), sits (Set.univ) l 0=l from fun l=> by ext; simp [sits,Verse.marked]]; rw [show Ψm= Verse.marked (Set.univ) εm *l from (by ext; simp [Verse.marked,Lyric.mulScale]), Verse.excursion, Complex.ofReal_mul,mul_smul]
   · unfold kettle; dsimp only; rw [stuffed]; exact Flues.written _ _ _ _ _ i
include H0
lemma metal_port (i:ℕ)(U':Config G c)(t:α)(f:Poly Jm)(hv:Width.Covered ((sh').val i t U') f): Width.Covered (boom εm ((sh).val i t U')) f:= by
   let k:= sh; let z':=(sh').val i t U'; let p:=k.val i t U'
   have h': z'= _:= bankers H χ U M x' l H' D P' ht E₀ V₀ z hc t i U' -- inference εm?
   intro ν; refine ⟨le_trans ?_ (hv ν).1,(hv ν).2⟩; change ‖(boom εm p).part ν‖ ≤ ‖z'.part ν‖; rw [paid,h',Poly.part_smul]; let q := Verse.load Set.univ ((Ξ).score i); let c:=(Verse.controls Set.univ z ((Ξ).score i)); rw [norm_mul,norm_mul]
   by_cases hz:q=0 ∧ ν≠Jm.quiet
   · have he:c=1:= Flues.cold Set.univ z _ hz.1; have hw:p.part ν=0:= by change ((_:ℂ) • c).part ν=_; rw [he,Poly.part_smul,Poly.one_part,if_neg hz.2,mul_zero];
     rw [hw,norm_zero,mul_zero,mul_zero]
   apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); change ‖((Throng.weight εm ν:ℝ):ℂ)‖ ≤ ‖((εm^q:ℝ):ℂ)‖; rw [Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans (Throng.mass H0 _)),Real.norm_of_nonneg (pow_nonneg (zero_le_one.trans H0) _)]
   unfold Throng.weight; split; exact one_le_pow₀ H0; next h=> have hh:=pow_le_pow_right₀ H0 (Nat.pos_of_ne_zero (show q≠0 from (fun he=>hz ⟨he,h⟩))); simpa only [pow_one] using hh
include h hp hb hT hh hZ hs U
local notation "P0"=> layoutGlobal H χ U M x' l h hh H' D P' hp ht E₀ V₀ z hZ hT hc
lemma cash_mark : (Throng.Hard.metal P0 εm).Paid gP P'.B a (fee0):= by
    let S₀:= sh; let q:=Ψ
    have hμ :=shaftValue H χ U M x' l h hh H' D P' hp ht E₀ V₀ z hZ hT hc; obtain ⟨f,hF,hG⟩:= (shaftValue H χ U M x' (Ψm) h hs H' D P' hp ht E₀ V₀ z hZ hb hc).cost -- super Mark prices this step
    have hpℓ i t (U':Config G c) : Width.Covered (boom εm (S₀.val i t U')) (f i):= metal_port H χ U M x' l H' D P' ht E₀ V₀ z hc H0 i U' t _ (hF i t U')
    let f' i:= ∑' j:{j // q j=i}, f j.val; have hs:= h.price.visit.posts; have hw:= hZ.votes; let P (i:ℕ):= ((XA).forced i).support; have hV i : (P i).Nonempty:= have h:= (XA).forced i|>.inventory_ne; h.mono ((XA).forced i|>.inventory_sup)
    have hh:= RG3.Letters.Frame.from_hit P'.B a (fee0) (fun i=> Poly.price gP (f i)) (fun i=> hV (q i)) (fun i=> Poly.nonnegative hw _) hs (show Ac.Hit (P∘q) P'.B _ _ _ from hG)
    have hf i:= Poly.budgeted hw (hh.2.1.comp_injective (show Injective (Subtype.val (p:=fun j=> q j=i)) from Subtype.val_injective)) (fun (j:{j // q j=i})=> le_refl (Poly.price gP (f j.val)))
    refine ⟨f',?_,fun x=>?_⟩
    · intro i t U'; change Width.Covered ((boom εm) (∑' j:{j // q j=i}, S₀.val j.val t U')) _; have he:= hμ.quality S₀ hs hw U' t i; rw [(boom εm).map_tsum he]; exact QuadraticLocal.SameSlot.coveredSum (fun j:{j // q j=i}=> hpℓ j.val t U') (show Summable (fun j:{j // q j=i}=> _) from (boom εm).summable he) (hf i).1
    apply budget_mono (SameSlot.sumHit q P (fun i=>Poly.price gP (f i)) (fun i=>Poly.nonnegative hw _) hG x)
    · intro i; split; exact mul_nonneg (Poly.nonnegative hw _) (Real.exp_pos _).le; exact le_rfl
    intro i; dsimp only [P]; split; exact mul_le_mul_of_nonneg_right (hf i).2 (Real.exp_pos _).le; exact le_rfl
end YM.QuadraticLocal.Lanes
