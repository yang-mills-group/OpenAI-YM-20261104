import YM.MSbar.Parma.Pluto
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
local notation "O"=> Tramp.path S.ratio G
variable (τ:S.Choices) (P:PathData G)(l:Clip)(R:Matrix (Body 1 n) (Body 1 c) ℝ)(ρ:fieldDir G c 1→AxisChart G F)(J:ChartRatio G)
variable {f:Nesting G n}(p:ℕ)(r m:ℕ)(hv:0<r)(hr:r≤p)(hf:Kind f)(hF:Expanse f 1 p)
local notation "μ"=>PowerSeries.coeff
local notation "X!"=>barbed F τ J (emptied r f)
variable {q s:ℕ}{a b c₁ c₂ c₃ c₄ A W B:ℝ}(h: Station F τ ρ P l R s b c₁ c₂ c₃ c₄) (ha:0≤ b)(hw:1≤ W)(hA:0≤A)(hB:0≤B)
variable {N:ℕ}
local notation "D"=>Whisk.ribbon 1 r
noncomputable def totalP (m r:ℕ)(C:ℝ)(K':ℝ):= C*K'^(m+2*Whisk.ribbon 1 r+1)
variable (hp:∀ i<r, Tokew (Measuring.chart n G) b s (m+2*Whisk.ribbon 1 r) 0 (PowerSeries.coeff i f) A)
variable (h₁:∀ i≤r, Tokew (address F G) b s (m+2*Whisk.ribbon 1 r) 0 (PowerSeries.coeff i (splitV (singularity (swung F J) 0)-splitV (singularity (pushChart F G τ) 2))) B)
local notation "C₁"=> B+totalP m r A c₃
local notation "i!"=> (Measuring.chart c G)
noncomputable def plaqueR(m r:ℕ)(s A B b L':ℝ):= L'^(m+1)*driver 1 r m s (B+totalP m r A b)
local notation "C₂"=>plaqueR m r c₄ A B c₃ c₂
include h hp h₁ hv hr ha hf hF hA
open MvPolynomial
lemma beacon : Tokew (Tramp.path S.ratio G) b s m 0 (PowerSeries.coeff r (song F τ P l J (emptied r f) ρ)) C₂:=by
    let t:= m+2*Whisk.ribbon 1 r; let R':= emptied r f
    have h0:Kind R':=by unfold R' Kind emptied; rw [PowerSeries.coeff_mk,if_pos hv,hf]
    have hh:∀ i≤r,Tokew Ψ b s t 0 (μ i X!) C₁:=by
        intro i hi; unfold barbed; rw [_root_.map_add,PowerSeries.coeff_map]; apply Tokew.kit (h₁ i hi); unfold emptied;rw [PowerSeries.coeff_mk]; split; next hb=>
            have ht:= Tin.scaleT h.stamp ha (by norm_num : (0:ℝ)<1) (Tin.lit (w:=1) zero_lt_one le_rfl (hp i hb)); apply Tokew.delta (Tin.weightTok zero_lt_one le_rfl ht) le_rfl; simp only [one_pow,one_mul]; unfold totalP; exact le_of_eq (mul_comm ..)
        next hh=> rw [map_zero]; refine ⟨?_,fun i=>?_⟩
                  · have he:=h.stamp.cash; unfold totalP; have hv:0≤c₃:=zero_le_one.trans he; positivity
                  rw [_root_.map_zero]; exact Quote.nill (by have he:= h.stamp.cash; unfold totalP; have hv:0≤c₃:=zero_le_one.trans he; positivity)
    let V:=X!; have hv : Tokew Ψ b s m 0 (μ r (confect (swatch F τ l P) V)) (driver 1 r m c₄ C₁):= Whisk.cargo (well _ _ _ _ h0) (0:Site n) ha h.loop (lair F τ P l ρ J p r hv hr hf hF h) hh le_rfl
    unfold song; rw [PowerSeries.coeff_map]; apply Tokew.delta (Tin.weightTok zero_lt_one le_rfl (Tin.scaleT h.land ha (by norm_num : 0 < (1:ℝ)) (Tin.lit (w:=1) zero_lt_one le_rfl hv))) le_rfl; simp only [one_pow,one_mul]; rfl -- check formula.C issue note `PowerSeries.coeff` maybe ambiguity
variable (he:Guessed F R ρ) (hk:Critical F l P ρ)
variable (ht:Tin (Measuring.chart n G) b s (r+1) W (PowerSeries.coeff r f) a)
variable {v:ℝ}{F':ℝ→Wilson.Config G n→ℝ}(hV:Trend F' f P l p)
variable (h₂:∀ i<r,Tokew (slide G n ∘ Sum.inl) b s (m+1) 0 (PowerSeries.coeff i (tariff n p l P f)) A)
local notation "M"=> Rolling.rail (shuttle F R)
local notation "Ν"=>Rolling.rail (maple R G)
local notation "B₂"=> c₁^(m+1)*((∑ i∈ Finset.range r, 2*2^m*tub G b s (r-i) (m+1))*A)
local notation "C₃"=> c₂^(m+1)*(plaque r m c₃ c₄*(a/W^2))
include hk he hw ht hV h₂
lemma capture : Tin (Tramp.path S.ratio G) b s m W ((PowerSeries.coeff r (colorCut F τ P l J f ρ))- (Rolling.rail (maple R G) (PowerSeries.coeff r f))) (W^(m+1)*C₂ +C₃+W^(m+1)*B₂):=by
    have hw0:= zero_lt_one.trans_le hw
    let k:= μ r (colorCut F τ P l J f ρ); let V:= μ r (song F τ P l J (emptied r f) ρ); let G':= μ r (song F τ P l J f ρ); let t':=M (μ r f); let Z:= ((Ν) (μ r f))
    have he:= Tin.lit hw0 hw (beacon F τ P l R ρ J p r m hv hr hf hF h ha hA hp h₁); have hh:= distant F τ P l R ρ J p r m hv hr hf hF h ha hw ht ‹_› hk
    have ht:= swing F R f P l r p hV hr ha h₂ h.mouth; rw [show μ r (tariff n p l P f)= μ r f from (by unfold tariff; rw [map_sub,PowerSeries.coeff_C_of_ne_zero hv.ne',sub_zero])] at ht
    let K':= Tin.unite hw0 (Tin.unite hw0 he hh) (Tin.lit hw0 hw ht); have hc: ∃ x:ℝ,k= G'+ MvPolynomial.C x := by
        refine ⟨-(MvPolynomial.eval 0 G'),?_⟩; unfold k colorCut Bakery.Rewind; rw [PowerSeries.coeff_mk,Bakery.rewind,sub_eq_add_neg,map_neg]
    obtain ⟨x,hq⟩:= hc; change Tin O _ _ _ _ (k-Z) _
    rw [show k-Z= (V + (G'-V-t') + (t'-Z))+MvPolynomial.C x from ?_]
    exact Tin.it hw0 (Tin.unite hw0 K' (Tin.constant hw0 x le_rfl)) (by rw [add_zero]) le_rfl
    rw [hq]; abel
end YM.MSbar.Parma
