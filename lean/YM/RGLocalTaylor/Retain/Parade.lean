import YM.RGLocalTaylor.Retain.Hedge
/-!
# Submit principal linear error and buy on PERCENTAGE of the real orbit price
BEAM Steps, every emission address. This relies on authenticated receipt for
 the **impulse**. Not asserting lease in Lit with other unsupported pricing or
 using another representation. The future use in Worker dresses this with
 the actual Φ Witness.Color.Glass Loss.All. Need post-position margin. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGLocalTaylor

open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary ConnectedActivityE6.Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond Shield Eider Flux Hues Rotation Stained
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F F' : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {η r q a Y W d C' A b s μ C v B : ℝ}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R}


open Blaze.March
namespace Retain
open PhysicalNext PhysicalNext.Repeat Lotus Daisy Greenbelt RG01.Survive
open Mayer goodK Mill
open Match Song Push AnalyticBridge VerifiedReset Collection Extra.Iteration Refrain Geo Quotes
open Captain Ursell Gas Brim
open Fort
open RGLocalTaylor.Read
namespace Gorge
variable {f₁ f₂ : Post.glyph G f} {M : ℕ}(H) (X :Cash W s μ L Q o C T (impulse R f₂ a))
   (p:BudgetPoint)(i:ℕ) {w w' : ℕ→ℝ}
variable {ξ α δ ε K H₀ ρ r' u wF:ℝ}
set_option quotPrecheck false
local notation "X'" => impulse R f₂ a
local notation "t'" => Time.credit G P.below * Pressure.δE s
local notation "o'" => Chi.canonical
local notation "ρ₀" => Mayer.arcRadius G L s
local notation "d'" => (ρ₀^(M+1))⁻¹
local notation "χM" => cover H (physical H M) (χ:=χ)
local notation "ΛM" => cover H (mantle H 0 M) (χ:=χ)
local notation "A!" => Read.field (fun _ i=>i=1) χM
local notation "ζ" => Read.field (nextG H M) χM
local notation "ζ'" => Read.field (nextG H M) ΛM
local notation "τ" => (fun (_ : H.fragrances)(i:ℕ)=>M+1≤ i)
local notation "Mm" => (Mayer.issue H χ M)
local notation "F'" => Read.field τ Mm

-- can use price holder with ANY order book; only need Θ field in impulse.Subscription.
section trial
variable {V : Rep G f} {J : Cash W s μ L Q o C T V}(P' : Match.Alliance J H 1 0) (hp:P'.units=Equiv.refl _)
local notation "W'" => (Beam.marquee J p)
local notation "α'" => Gorge.stamp H P'
local notation "LP" => orient p (Beam.marquee J p).reg

variable (hy : M≥1)

lemma totalEra (T:H.fragrances→ℕ→Prop) (i:H.fragrances) : (fun V=> stream H χ V i) = Read.field (fun x p=>¬ T x p) Mm i+ Read.field T Mm i:= by
   ext V; dsimp only [Pi.add_apply]; unfold Read.field; rw [← mul_add, add_comm (_ :ℝ) (∑ q∈_,(_ :ℝ)), Finset.sum_filter_add_sum_filter_not]; unfold aliquot stream Gas.term -- danger open
   rw [← Fintype.prod_sum (f:=fun x j=>Mayer.issue H χ M (i.2 x) j V)]; have hx(p:H.ThinP):∑ i:Orders M,Mm p i V=leaflet H χ V p:= by rw [← Finset.sum_apply,fullIdentity]
   simp_rw [hx]; ring

include hy hp
-- η arbitrary χ. θ1(X) computed via `Read.field`; λ cost in Credential
variable (γ:ℝ)
lemma iconicPrice (h:Local (Beam.marquee J p) p (Height.serve J P' χ (Beam.lit J)) ε K)(hF:LP (α' (ζ - ζ')) ξ) (hT: LP (α' F') u):
   LP (α' (iconOnly H A!)) (ε+(ξ+u)):=by
   obtain hs:= broadcast H p P' hp h; let T:= onlyLit H χ; let A:= iconOnly H A!; let e:=iconOnly H ζ; let f:=iconOnly H F'
   have hx: T=A+(e+f):=by
      ext z V; by_cases hz:z∈ Set.range (icon H)
      · let U:= (fun i k=> M+1 ≤ k:H.fragrances→ℕ→Prop); let W:= iconOnly H A!
        have h : floors H M=fun i k=>¬ U i k:=rfl
        unfold T onlyLit A e f iconOnly; simp only [hz, ↓reduceIte, Pi.add_apply]
        have hv := totalEra (χ:=χ) H (M:=M) U z; have hm:= issued H (floors H M) (χ:=χ) (M:=M) (by unfold floors; omega) -- universal intro
        rw [← h, ← hm, at_two H (χ:=χ) _ hy] at hv
        exact (congr_fun hv V).trans (add_assoc ..)
      unfold T onlyLit A e f iconOnly; simp only [hz, ↓reduceIte,Pi.zero_apply,Pi.add_apply,add_zero]
   have hV : A= T-(e+f):=eq_sub_of_add_eq hx.symm; change LP (α' A) _;rw [hV,log_sub H P',log_add H P']
   have hz : LP (α' e) ξ:= picked H p P' hF fun i=> by
      by_cases h:i ∈ Set.range (icon H)
      · left; obtain ⟨i,rfl⟩:= h; unfold e iconOnly; rw [if_pos (Set.mem_range_self _), Pi.sub_apply,hushRoll H, sub_zero] -- h lemma args?
      exact Or.inr (if_neg h)
   exact orient.subtract hs (adds p (W').reg hz (picked H p P' hT fun i=> by unfold f iconOnly; split ; exact Or.inl rfl; exact Or.inr rfl))

omit hp hy
-- use May1.H.Contract from same actual Earnings Motion. Issue stride at canonical χ.
lemma costEra (he: preExponent p≤ α)(hh:0<ε)(hp:p.threshold=Pressure.temp s)(ht:p.B=radiusB s)
   (h:Mayer.Passport H α wF (turnFee p) ε p.order p.power M) : orient p (Beam.marquee J p).reg
       (α' (Read.field (fun _ i=> M+1≤ i) (Mayer.issue H Chi.canonical M))) ((Mayer.arcRadius G L s^(M+1))⁻¹):=by
   have hh := Read.earning P' 0 τ (fun _ i h=>h) hp ht he hh h; exact hh.2 (Beam.contents J p) (Beam.patch J p)
end trial

section post
variable {V : Rep G f}{J : Cash W s μ L Q o C T V}(P' : Match.Alliance J H 1 0)(Z:Match.Alliance J X 1 0)
local notation "St" => stamp H P'
local notation "W'" => (Beam.marquee J p)
local notation "LX" => orient p (Beam.marquee J p).reg
local notation "hT" => Read.field (fun _ i=>i=1) (cover X (physical X M) (χ:=χ))
local notation "ψE" => Read.field (fun _ i=>i=1) (cover H (mantle H f₁ M) (χ:=χ))
local notation "eK" => (RPC H f₂ (χ:=χ))

variable (hM:M≥1)(hp:P'.units=Equiv.refl _)(hz:Z.units=Equiv.refl _) (he :R.activities.E=f₁+f₂)
variable {p₁ p₂ :ℕ→ℝ}(h: dual H f₂ a p₁ p₂)
variable (h₁:p.threshold=Pressure.temp s)(h₂:p.order≤j)(h₃:p.B=radiusB s)
variable {N : Captain H j C' d v Y A b r B q n χ}
include hM hp hz he h h₁ h₂ h₃ N
lemma value_L (hV:LX (stamp X Z (iconOnly X hT)) ξ)
   (hv: shelved X p₂) (hE:LX (St (ζ-Read.field (nextG H M) (cover H (Fort.mantle H f₁ M) (χ:=χ)))) wF):
   LX (St (Read.field (floors H M) χM - Read.field (floors H M) (cover H (mantle H f₁ M) (χ:=χ)))) (a*ξ+wF):=by
   let F:=Read.field (nextG H M) (cover H (mantle H f₁ M) (χ:=χ)); let e:=eK
   rw [at_two H _ hM,at_two H _ hM,show A!+ζ-(ψE+F)= (A!-ψE)+(ζ-F) from (by abel),log_add H P']; refine adds p _ ?_ hE
   have he:= Gorge.shape_coin (N:=N) (H:=H) (p:=p) hM he h₁ h₃ h₂ h -- order inspect
   have hx: LX (St e) (a*ξ):= by unfold stamp e; rw [projected H X hM P' Z hp hz h.pos.ne' (M:=M) hv,Gorge.stampS]; exact scales p _ hV h.pos.le
   have hg := Gorge.recording (H:=H) p P' he; rw [mul_zero] at hg
   rw [show A!-ψE=(A!-ψE-e)+e from (sub_add_cancel ..).symm,log_add]; simpa only [zero_add] using adds p _ hg hx
end post
end Gorge
end Retain
end YM.RGLocalTaylor
