import YM.Qlocal.Reckoner.Planet
import YM.Qlocal.Flight
/-!
# Invoking the joint s.c primitive into the surgery currency
 Also marking transported Force SPACE gap ∋ δ>0. Preserves the actual log all μ.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.Qlocal.Reckoner.Palace
open Marker Lattice Wilson RG MeasureTheory Extra.Trajectories Push Push.AbsoluteSums
open Overlay RG3.Press RG3.Held RG3.Script.Picnic RG3.Forms Progress.DirectedRecipe
open Function Set Filter Finset Integration Integration.LocalComparison Integration.RiderTastePresentation
open PhysicalNext PhysicalNext.Repeat Mallow Blush
open scoped Topology InnerProductSpace Classical ContDiff Matrix.Norms.Frobenius BigOperators YM.Qlocal.Payload
open Merge Switch UniformPays Publishing Emissions Payload MergeProof Menu Accent Lotus Footprint StageArt
open RGComparison01 RGComparison01.Pledge Pressure
open ConnectedActivityE6 ConnectedActivityE6.Channel AnalyticBridge VerifiedReset Collection Quotes
open SliceRows Coat Baked Palette Resin Checks Song Refrain
open Next.Foundations Pressure.Stores Next.Fluctuations SectorMeasure Oriented Tree
open Planet Parabola Scribe
variable {Ω ι J V : Type} {G:Gauge}{c f L:Side}
    {P: RG.Rep G f}{P': RG.Rep G c}
    {X:Support c}{o:V→Site c}{s:V→Support c}
    {a b τ δ w e r v t Fκ t₀:ℝ}
    {S:StepData c f}{Z₀:Teller G}{Q:ConnectedActivityE6.Target G Z₀}{T: Tube G S}
    {W β μ C₀:ℝ}{O: Target.Order G W} {j k:ℕ}{u:ℕ→ℝ}
    {Δ:ℕ→Prop}
variable (U:Cash W β μ L Q O C₀ T P)
variable {M:ι→Leaf P}{D: Ω→ι→Leaf P}
variable (h:Roster M D) (α:ℝ) (g:ι→ℝ) (χ:Chi) (D₀: Match.Alliance U U 1 0)
local notation "p0" => P'.p
local notation "F★"=> P'.activities
set_option quotPrecheck false
local notation "d★"=> (P'.p).supportExponent
local notation "K★"=> fun x=> shoot (D x) U χ g U D₀
local notation "D★"=> (Beam.marquee U p0).read (plusone U D₀ χ α)
variable [Fintype ι]
    (ht:Primitive.Earnings U χ h α P'.p g D₀ Δ k e t Fκ τ r v)
    (R : KLink P'.p ((Beam.marquee U P'.p).read (plusone U D₀ χ α)) t b P'.p P'.activities w P'.p.supportExponent)
local notation "λ!"=> Primitive.table U χ h g
local notation "Lℓ"=> (fun x i=> Ink.yielded (D x) g U (χ:=χ) (h.castLabel U x i))
local notation "Wℓ"=> (R.carry K★)
variable (ha:KLink.Last R) (hv:P'.eval=S.push P.beta P.eval)(hp: ∀ i,P'.eval i≠0) (hT:P'.p.threshold=Pressure.temp β) {F0:Config G c→ℝ}
    (hS : SwitchStep (J:=Cl M U) D S g F0 ((Beam.marquee U P'.p).read (plusone U D₀ χ α)) P'.p (fun x=> shoot (D x) U χ g U D₀) (fun (x:Ω) (i:Baked.Cl M U)=> Ink.yielded (D x) g U (χ:=χ) (h.castLabel U x i)))
    (hz:b ≤ v)(hW : P'.p.supportExponent+δ ≤ v) (hq: δ ≤ StellarTree.spare P'.p.B) (hk:0 ≤δ)
variable [Fintype V][Nonempty V][DecidableEq V]
local notation "Ψ"=>Whole V
local notation "ζ"=> (1:Parabola.Ray (Whole V)) -- lean uses Pi type
variable (f₀:ι ↪ V)
    (he:∀ i,o i∈ s i)
    (hL:∀ i,s (f₀ i) ⊆ (M i).crest.image S.ratio.parent)
local notation "Γ" => mantra λ! f₀
local notation "K₀"=> Planet.proper_read f₀ Wℓ
local notation "z"=> fun i:ι=> Planet.glyph (f₀ i)
noncomputable def blank (V:Type)[Fintype V][DecidableEq V]: Ray (Whole V):= fun _=>1
lemma blank_pos (V : Type)[DecidableEq V][Fintype V] : Rental (blank V):= ⟨fun _=> zero_lt_one,fun _ _ _ _=>(one_mul _).symm.le,rfl⟩
local notation "z₀"=> blank V
set_option maxHeartbeats 500000 in
include U hS hv hp hT ht ha hz hW hq he hL hk in
lemma crown [Countable (Cl M U)] :
   Scribe.Proper Γ (p0) s ∧ Scribe.Spend Γ (p0) z₀ (P'.p.supportExponent+δ) r ∧
   (Reckoner.Night P' s K₀ z₀ (P'.p.supportExponent+δ) w) ∧
   ∀ x:Ω,S.push P.beta (Photo.given (S:=S) (D x) g (Whole V) (z)) = (((Scribe.printP Γ K₀).taste P' o s).leaf x).density := by
 let Y:=λ!; let V0:= U.supportP ∘ Palette.sign M S; have hP(i):s (f₀ i)⊆ V0 i:= (hL i).trans (Stowe.enrolled M U i)
 let f:=(z); have hg := ht.force.relax (le_refl t) hz; let v' :ℝ := P'.p.supportExponent+δ; have hS₁ :=Flight.narrows (Primitive.rental U χ h α P'.p g D₀ ht) hW
 have hK := (ha.spare Ω ι hg).relax (le_refl w) (add_le_add_right hq _) -- `add_left`
 have hR:= Primitive.reads U χ h α P'.p g D₀ ht; have hO: Scribe.Proper (Γ) P'.p s:= Planet.seen f₀ Y hR hS₁ hP
 have hφ : Syntax (z) s V0:= Planet.regard f₀ hP
 let C:=blank_pos V; have he0 i:(z₀) (book f₀ i) ≤1:=le_refl (1:ℝ); have hΦ := Planet.glyphs_paid f₀ z₀ he0
 have hQ x i (y:Site c) (hp:y∈V0 i): Merge.Motion.Hush i y (fun i=> (P'.activities.forced i).support) ((Wℓ) x):= R.addresses _ _ _ (ht.force_addresses _ _ _ hp)
 have hC:= levels P' hφ he Y hR hS₁ hK hQ (fun i=>(C.pos i).le) hΦ rfl;
 have hu0 : Scribe.Spend Γ (p0) z₀ (P'.p.supportExponent+δ) r:= by simpa only [one_mul] using (Planet.romance f₀ Y hS₁ z₀ C.oneSize he0)
 have heK:= weighs P' hφ he Y hR hS₁ hK hQ; have hy:= page f₀ (K:=Wℓ) Y; rw [← hy,one_mul] at hC; rw [← hy] at heK
 refine ⟨hO,hu0,?_ ,fun x=>?_⟩
 · convert! Scribe.from_bulk heK hC C; ring -- input h₀ caring B=1
 obtain ⟨l,hx,h⟩:= Primitive.payment U χ h α P'.p g D₀ ht hT (P'.p.exponent_pos.le.trans ((le_add_of_nonneg_right hk).trans hW)); let he' := SwitchStep.finish_into hS hg R hv hp; rw [hy]; exact funext fun V=>Service.answers hφ he Y hR hS₁ hK hQ U he' (le_add_of_nonneg_right hk) l hx h x V
end YM.Qlocal.Reckoner.Palace
