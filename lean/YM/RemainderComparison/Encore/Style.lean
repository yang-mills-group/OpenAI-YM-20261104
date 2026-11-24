import YM.RemainderComparison.Encore.Crests
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Encore
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset Solos Lyric Mosaic Serif Marker GridRenewal.Rain
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge} {L f c : Side} {R:Rep G f}{S:StepData c f}
variable {θ ι:Type} [DecidableEq θ]{J:Marker.Census θ}
variable (M:ι→Lotus.Leaf R)(U:Config G f)(B:Set ι)(l:ι→ℝ)(z:ι→Marker.Poly J)
-- λ calibration log input can be used only after exact representation.B.Current. «ℓ» already debited for holder. K copies may carry projections.B.Cloud.Owns.Frame.Consumer contracts. No smallness derived from true exponential path alone at K.
variable {P:Teller G}{Q: ConnectedActivityE6.Target G P}{T:Tube G S}{W x μ a v c' w δ d:ℝ} {p o t : ℕ} {u:ConnectedActivityE6.Target.Order G W}
variable (H:Cash W x μ L Q u v T R)
variable {F:θ→ℝ}(h : Chorus J F B z t)(hp: Muse.Motto M l δ H a c' w p)
set_option quotPrecheck false
local notation "Ψ" => Muse.sits B l δ
local notation "Φ" =>primitive M U B Ψ z
local notation "P₀" => TuneR M B l δ z S
local notation "X"=> gas M U B Ψ z
variable [Fintype θ]
variable (σ:Config G f→ι→ℝ) -- NAT vacuum calibration extras; OWN kernel buds.Sem.Role.Real.No estimate on Φ

def layer (δ:ℝ)(i:ι): Marker.Poly J:= if limb M i=none then if i∈B then primitive M U B (Muse.sits B l δ) z i else Lacuna.tint J (σ U i) else 0
structure Renders (δ:ℝ) : Prop where
   geometry : doors M
   history : ∀ U i,i∉B→ limb M i=none → Muse.sits B l δ i * (M i).ingredient U= Real.exp (σ U i)-1
   earns : ∀ U, Summable (fun i:ι=> if i∉B ∧ limb M i=none then ‖σ U i‖ else 0)
local notation "K"=> layer M U B l z σ δ
include h hp
omit h [Fintype θ] [DecidableEq θ] in
lemma luminous : Summable (wages M Ψ) ∧ ∀ i,0≤ Ψ i:=by
   obtain ⟨P',hE,Y,p',hc⟩:= hp.claim; obtain hg := Serif.league M H l δ hp; let L:= Ψ; have he i:0≤ L i:=by unfold L Muse.sits; simp only [Pi.mul_apply]; unfold Verse.marked; split<;> exact mul_nonneg (by first|exact hp.positive|exact zero_le_one) (hc.currency i)
   refine ⟨hg.mul_left (1+|δ|)|>.of_nonneg_of_le (fun i=> mul_nonneg (he i) (Leaf.profit (M i))) fun i=>?_,he⟩
   unfold Palette.wages Muse.sits; unfold Verse.marked; simp only [Pi.mul_apply]; split; next=>
     rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (by linarith only [le_abs_self δ,abs_nonneg δ]) (mul_nonneg (hc.currency _) (Leaf.profit (M i)))
   next=> rw [one_mul]; exact le_mul_of_one_le_left (mul_nonneg (hc.currency _) (Leaf.profit _)) (le_add_of_nonneg_right (abs_nonneg _))
omit [Fintype θ] in
lemma column : Summable (fun i=>Marker.Poly.price F (Φ i)):=by
    obtain ⟨he,hL⟩:= luminous M B l H hp -- arg order
    refine he.of_nonneg_of_le (fun i=> Marker.Poly.nonnegative h.votes _) (fun i=>?_)
    unfold primitive; rw [Marker.Poly.adapted,Complex.norm_real]; exact (mul_le_of_le_one_right (norm_nonneg _) (Serif.bought h _)).trans (by rw [norm_mul,Real.norm_of_nonneg (hL i)]; exact mul_le_mul_of_nonneg_left ((M i).earn U) (hL i))
variable (hX:Renders M B l σ δ)
include hX
lemma stamp :
     P₀ U = (Complex.ofReal (Real.exp (R.exponent U))) • (cyclone (∑' i,K i)*(∑' b,gas M U B (Muse.sits B l δ) z b)) :=by
    have he:= column M U B l z H h hp; refine Encore.thole M U B Ψ z H.laws.intake.cap h.votes he hX.geometry δ l rfl K ?_ ?_
    · refine (Marker.Poly.budgeted h.votes (he.add (hX.earns U)) ?_).1; intro i; unfold Encore.layer; by_cases hv:i∈B <;> by_cases hp:limb M i=none
      · simp only [hv,hp,↓reduceIte,not_true_eq_false, false_and,add_zero,le_refl]
      · rw [if_neg hp,Marker.Poly.zero_price]; exact add_nonneg (Marker.Poly.nonnegative h.votes _) (if_neg (fun x=>hp x.2)|>.ge)
      · simp only [if_pos hp, if_neg hv,Lacuna.tint,Marker.Poly.adapted,Complex.norm_real, Marker.Poly.one_price]; -- simplify right
        simp only [hv,hp,not_false_eq_true,and_self,↓reduceIte,mul_one]; exact le_add_of_nonneg_left (Marker.Poly.nonnegative h.votes _)
      rw [if_neg hp,Marker.Poly.zero_price]; apply add_nonneg (Marker.Poly.nonnegative h.votes _); split; exact norm_nonneg _; exact le_rfl
    intro i; unfold layer; split_ifs; next hv hw=>
       apply Flues.evaporate; unfold primitive Verse.controls; simp only [Multiset.map_singleton,Multiset.prod_singleton,if_pos hw]; rw [smul_mul_smul_comm,h.square, smul_zero]
    next hv hw=>
       unfold Lacuna.tint primitive Verse.controls; simp only [Multiset.map_singleton,Multiset.prod_singleton,if_neg hw]; rw [hX.history U i hw hv,← GridRenewal.Rain.beacon, GridRenewal.Rain.clear,← Complex.ofReal_exp, GridRenewal.Rain.beacon,Complex.ofReal_sub,sub_smul]; simp
    next=> exact GridRenewal.Rain.flare
omit h hX hp in
lemma blueprint (l:ι→ℝ) (h:doors M)(d:ℝ): Renders M Set.univ l (fun _=>0) d:= ⟨h,fun _ _ h=> False.elim (h trivial),fun U=> by simp⟩ -- warnings
end YM.RemainderComparison.Encore
