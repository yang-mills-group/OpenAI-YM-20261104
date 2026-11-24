import YM.MSbar.Parma.Rations
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Parma
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c n:Side}{S:StepData c n}(F: Forest S.ratio)
local notation "X"=>Primary n G
local notation "Y"=>Primary c G
local notation "K"=>Joint F G
local notation "T"=> S.ratio
local notation "Ψ"=>address F G
local notation "θ"=>Measuring.chart n G
local notation "⌂"=>Positions (Joint F G)
local notation "O"=> Tramp.path S.ratio G
open MvPolynomial
noncomputable def emptied {σ:Type} (k:ℕ)(F:PowerSeries (Pot σ)) := PowerSeries.mk fun j=> if j<k then PowerSeries.coeff j F else 0 -- Fintype Pot?
variable (τ:S.Choices) (P:PathData G)(l:Clip)(R:Matrix (Body 1 n) (Body 1 c) ℝ)(ρ:fieldDir G c 1→AxisChart G F)(J:ChartRatio G)
variable {f:Nesting G n}(p:ℕ)(r m:ℕ)(hv:0<r)(hr:r≤p)(hf:Kind f)(hF:Expanse f 1 p)
local notation "V"=>barbed F τ J
local notation "ε"=>emptied
local notation "μ"=>PowerSeries.coeff
local notation "Ω"=> song F τ P l J
local notation "g"=>barbed F τ J f
local notation "e"=>barbed F τ J (emptied r f)
local notation "C'"=>swatch F τ l P
lemma expanseB (f:Nesting G n)(h:Expanse f 1 p): Expanse (barbed F τ J f) 1 p:=by
    have hx (k:⌂→ℝ)(u:ℕ)(hv:u≤2): Expanse (splitV (singularity k u)) 1 p:=by
        let Q:= singularity k u; refine ⟨fun t ht=>?_⟩; by_cases hp:t=0; subst t; rw [splitK];simp
        rw [splitV,map_sub,PowerSeries.coeff_C_of_ne_zero hp,sub_zero,singularity,PowerSeries.coeff_mk]; exact (potsD ..).trans (by omega)
    refine ⟨fun j hj=>?_⟩; unfold barbed; rw [map_add,map_sub,PowerSeries.coeff_map,sub_eq_add_neg]; refine (totalDegree_add ..).trans (max_le ((totalDegree_add ..).trans (max_le ((hx _ _ (by omega)).profile j hj) ?_)) ((clearD _ _).trans (h.profile j hj))); rw [totalDegree_neg]; exact (hx _ _ le_rfl).profile j hj
include hf hF hv hr
lemma lair {a c₁ c₂ c₃ c₄:ℝ}{s:ℕ}{R} (E:Station F τ ρ P l R s a c₁ c₂ c₃ c₄): Expanse (barbed F τ J (emptied r f)) 1 r:=by
    apply expanseB; refine ⟨fun j hj=>?_⟩; rw [emptied,PowerSeries.coeff_mk]; split; apply hF.profile j (by omega); simp
local notation "D"=>Whisk.ribbon 1 r
variable {W s₁ s₂ s₃ s₄ K' x C b :ℝ}{k q:ℕ}(h:Station F τ ρ P l R q b s₁ s₂ s₃ s₄)(hp:0≤ b)
-- Bounds bill for lower at order ≤r or ≤r-1, barbed core. two costs. output principal relief inaccessible.Trilo.Roe.
variable (hw:1≤ W)(ht: Tin (Measuring.chart n G) b q (r+1) W (PowerSeries.coeff r f) K')
local notation "Tκ"=> Tin Ψ b q
include hw ht h hp
noncomputable def plaque (r m:ℕ)(s b:ℝ):= (∑ i∈Finset.range (Whisk.ribbon 1 r), b^(i+1)) * s^(m+2*Whisk.ribbon 1 r+1)
lemma sheenL : Tin Ψ b q m W (PowerSeries.coeff r (confect C' g)-PowerSeries.coeff r (confect C' e)- Rolling.rail (taps F G) (PowerSeries.coeff r f)) (plaque r m s₃ s₄*(K'/W^2)):=by
    have hp₀:Kind (emptied r f):=by unfold Kind emptied;rw [PowerSeries.coeff_mk,if_pos hv,hf]; -- semicolon
    have h₀:Kind (barbed F τ J f):=well _ _ _ _ hf; have hV:Kind e:=well _ _ _ _ hp₀; have hF':Expanse (barbed F τ J f) 1 r:= ⟨fun i hi=> (expanseB F τ J p f hF).1 i (hi.trans hr)⟩
    have hx(i:ℕ)(hx:i<r) : μ i g=μ i e:=by unfold barbed; rw [_root_.map_add, _root_.map_add, PowerSeries.coeff_map, PowerSeries.coeff_map]; rw [emptied,PowerSeries.coeff_mk,if_pos hx]
    have he : μ r g-μ r e= Rolling.rail (taps F G) (μ r f):=by unfold barbed; rw [_root_.map_add, _root_.map_add, PowerSeries.coeff_map, PowerSeries.coeff_map,emptied,PowerSeries.coeff_mk,if_neg (by omega),map_zero]; abel
    have hL:Tκ (m+2*D) W (μ r g-μ r e) (s₃^(m+2*D+1)*K'):=by
       rw [he]; have hv':0 < W:=zero_lt_one.trans_le hw; apply Tin.scaleT h.stamp hp hv'; apply Tin.aspires hv' ht; exact (hF.profile _ hr).trans (by omega)
    have hc:= Tin.burn C' h₀ hV hx hw hp h.loop hL rfl hF' (lair F τ P l ρ J p r hv hr hf hF h) le_rfl; unfold plaque; rw [←he]; apply Tin.it (zero_lt_one.trans_le hw) hc _ le_rfl; exact le_of_eq (by ring)
variable (he: Guessed F R ρ) (hρ : Critical F l P ρ)
local notation "M"=> Rolling.rail (shuttle (G:=G) F R)
include he hρ
lemma distant : Tin O b q m W (PowerSeries.coeff r (song F τ P l J f ρ)-PowerSeries.coeff r (song F τ P l J (emptied r f) ρ)-M (PowerSeries.coeff r f)) (s₂^(m+1)*(plaque r m s₃ s₄*(K'/W^2))):=by
    let N:=Rolling.rail (poring F ρ); let t:= μ r (song F τ P l J (emptied r f) ρ)
    have ht':M (μ r f)= N (Rolling.rail (taps F G) (μ r f)):=by
        -- via rail pol ring maps or evaluation. Need MvPolynomial.funext. Use eval and real infinite
        let R':=shuttle (G:=G) F R
        have hx(x: Positions (Primary c G)): R' *ᵥ x=taps F G *ᵥ (poring F ρ*ᵥ x):=by rw [taps,poring,LinearMap.toMatrix'_mulVec,LinearMap.toMatrix'_mulVec]; exact (vaultT F R x ρ l P he hρ).symm
        have hv(x:Positions (Primary c G)) : clue (M (μ r f)) x = clue (N (Rolling.rail (taps F G) (μ r f))) x :=by
            rw [show clue (M _) x=(MvPolynomial.eval (_ *ᵥ x) (μ r f)) from congr_fun (clearL R' x) _, show R' *ᵥ x= _ from hx x]; exact (Eq.trans (show _= MvPolynomial.eval _ _ from (congr_fun (clearL (taps F G) (poring F ρ*ᵥ x)) (μ r f)).symm) ((congr_fun (clearL (poring F ρ) x) _).symm))
        exact MvPolynomial.funext hv -- name
    rw [ht']; let Y':= μ r (confect C' e); let Z:= μ r (confect C' g); change Tin O b q m W _ _
    simp only [song, PowerSeries.coeff_map]; change Tin O b q m W (N Z-N Y'-N _) _; rw [← map_sub,← map_sub]; exact Tin.scaleT h.land hp (zero_lt_one.trans_le hw) (sheenL F τ P l R ρ J p r m hv hr hf hF h hp hw ht)
end YM.MSbar.Parma
