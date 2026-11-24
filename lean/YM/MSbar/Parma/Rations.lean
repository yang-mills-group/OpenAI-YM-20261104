import YM.MSbar.Parma.Dune
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Parma
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave UVNext.PricedKernels
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c n:Side}{S:StepData c n}(F: Forest S.ratio)
local notation "X"=>Primary n G
local notation "Y"=>Primary c G
local notation "Φ"=> Key F G
local notation "K"=>Joint F G
local notation "T"=> S.ratio
local notation "Ψ"=>address F G
local notation "θ"=>Measuring.chart n G
local notation "⌂"=>Positions (Joint F G)
local notation "O"=> Tramp.path S.ratio G
variable {μ C' Λ :ℝ}{j s p N:ℕ}{V: KernelChoices}
variable (Z:Uniform.Before G μ C' j V N)(J:ChartRatio G)
variable (τ:S.Choices)(hj:S.patch.J=j)(hv:S.kernel=V)(h:Bid.Larger (G:=G) S) (hJ:LocalRatio J)
variable (l:Clip)(R:PathData G)(hR:R.Bounds l μ C' Λ)
variable (P:Cross S.ratio.count (TypeFace 1) (TypeFace 1)) (ρ:fieldDir G c 1→ AxisChart G F) (hc:Critical F l R ρ)(hf:Guessed F (installed S.ratio P) ρ)
local notation "L"=>swatch F τ l R
local notation "I"=>installed S.ratio P
variable {a C b B δ v:ℝ} (ha:0<a)(ho:P.strip a B)(hb:0≤ B)
-- explicit cov direction.*, permits same for multiple curves
noncomputable def grain (l:Clip)(P: Patch)(Z:Uniform.Before G μ C' j V N) (a:ℝ): ℝ:= min (Z.tables l P).rate (a/P.L.val)/5
structure Station (F:Forest S.ratio) (τ:S.Choices) (ρ:fieldDir G c 1 → AxisChart G F) (R:PathData G)(p:Clip)(V:Matrix (Body 1 n) (Body 1 c) ℝ)(s:ℕ)(a b c₁ c₂ c₃:ℝ): Prop where
   mouth (t:ℝ): t∈Set.Icc (0:ℝ) 1→ Syrup (slide G n) (Tramp.path S.ratio G) a s (Tramp.mouth F V t G) b
   land : Syrup (address F G) (Tramp.path S.ratio G) a s (poring F ρ) c₁
   stamp : Syrup (Measuring.chart n G) (address F G) a s (taps F G) c₂
   loop : LoopNet (address F G) a s (swatch F τ p R) c₃
noncomputable def goalM (G:Gauge)(P:Patch)(C a B δ:ℝ):= shellS (summerSize G) (tintCost G) C (tranche P a B) δ
noncomputable def goalL (G:Gauge)(P:Patch)(C a B δ:ℝ):= shellS (townCost G) (tintCost G) C (1+tranche P a B) δ
noncomputable def goalK (G:Gauge)(C δ:ℝ):= shellS (tintCost G) (townCost G) C 1 δ
noncomputable def goalN (G:Gauge)(v:ℝ)(C δ:ℝ):= shellS (townCost G) (townCost G) C (v/2/2)⁻¹ δ
variable (hD:δ=grain l S.patch Z a) (hE:0≤ C)(hs:∀ t:ℕ,(1+(t:ℝ))^s≤ C*Real.exp (δ*t))
include Z h hv hj hR hc hf ha ho hb hD
include τ
set_option quotPrecheck false
local notation "θ₀"=> (Z.tables l S.patch).gap
lemma nectar : 0 < δ :=by
   have h₁:= (Z.receipt F τ hR h hj hv).1; have hζ:=h₁.pos_m; have hd:0 < (Z.tables l S.patch).rate:= tiltWidth_pos _ (half_pos hζ) h₁.pos_a h₁.pos_C.le; rw [hD]; unfold grain; positivity
include hs hE
lemma spends (hv':0≤v)(hk:v ≤ δ): Station F τ ρ R l (installed S.ratio P) s v (goalM G S.patch C a B δ) (goalL G S.patch C a B δ) (goalK G C δ) (goalN G θ₀ C δ):=by
    have hd:= nectar F Z τ hj hv h l R hR P ρ hc hf ha ho hb hD; let v':= Z.tables l S.patch; let e:= a/S.patch.L.val
    have hx (i:ℝ)(he:min v'.rate e ≤ i) : δ+v+v+δ+δ ≤ i:= by
       have hp:δ*5=min v'.rate e:=by unfold v' e; rw [hD]; unfold grain;ring
       linarith only [hp,hk, he]
    have hμ:= hx _ (min_le_right ..); have hA:= hx _ (min_le_left ..)
    have hp:= funds0 P ha ho hb; have ht:= cardP (S:=S) (G:=G); have hr:= starM G n
    have hz :0< v'.gap:= (Z.receipt F τ hR h hj hv).1.pos_m
    refine ⟨fun t hu=> ?_,?_,?_,?_⟩
    · exact bookF _ _ _ hμ hd hv' hE hd.le hp hs (feet F P ha ho hb t hu) (tok1 G n) ht
    · exact bookF _ _ _ hμ hd hv' hE hd.le (by linarith only [hp] : 0≤1+tranche S.patch a B) hs (stape F P R l ρ hc hf ha ho hb) (Uniform.town F) ht
    · exact bookF _ _ _ hμ hd hv' hE hd.le zero_le_one hs (clap F e) hr (Uniform.town F)
    exact syrupLoop _ _ hv' (bookF _ _ _ hA hd hv' hE hd.le (by exact inv_nonneg.mpr (half_pos (half_pos hz)|>.le)) hs (fun i j=> peacock F Z τ hj hv h l R hR i j) (Uniform.town F) (Uniform.town F))
end YM.MSbar.Parma
