import YM.MSbar.Parma.Above
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Parma
open Function Filter Whisk Lis Measuring Cacao CrossH Push Uniform Lattice RG Pressure Matrix
open Precision Gauge Midpoint Rolling Tramp Exterior Tree Wilson Laurent Bloch Wave UVNext.PricedKernels
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G:Gauge} {c n:Side}{S:StepData c n} (F:Forest S.ratio)(τ:S.Choices)(P:Cross S.ratio.count (TypeFace 1) (TypeFace 1))
local notation "X"=>Primary n G
local notation "Y"=>Primary c G
local notation "ℓ"=>Measuring.chart n G
local notation "T"=>Measuring.chart c G
local notation "L"=>(S.ratio.count.val:ℝ)
local notation "R'"=>installed S.ratio P
open MvPolynomial
variable (f:Nesting G n)(F':ℝ → Config G n→ℝ)(R:PathData G)(l:Clip)(v:G.ColorIndex)(J:ChartRatio G) {ρ:fieldDir G c 1→ AxisChart G F}
variable {a η s₁ s₂ s₃ s₄ b H Z K' D w A:ℝ}{r m p k N:ℕ}
variable (hG:G.Simple)(hf:Trend F' f R l p)(hK: Keeps f p (sun G v)) (hr:r≤p)(hx:0<r)(hb:0≤b)(hη:6≤N)
local notation "T₀"=>teethT f r
local notation "F₁"=>clue (teethT f r)
local notation "C'"=> fixP G r a D η H N k
local notation "s'"=> fixedG G S.patch.L r a D η H N k
variable (hZ:Tin (Measuring.chart n G) b N (r+1) w (teethT f r) Z) (hw:1≤ w) (he:∀ i<r, Tokew (Measuring.chart n G) b N 3 0 (PowerSeries.coeff i (tariff n p l R f)) A)
variable (h:Cane P D η a H k N) (hp:3≤k) (hg:2≤S.ratio.count.val)(hT:a/(S.ratio.count.val:ℝ) ≤ b) (ha:0≤ A)
noncomputable def snag (r:ℕ):=r+1+2*Whisk.ribbon 1 r
variable (ht: Station F τ ρ R l (installed S.ratio P) N (a/(S.ratio.count.val:ℝ)) s₁ s₂ s₃ s₄) (hC:Critical F l R ρ)(hR:Guessed F (installed S.ratio P) ρ)
variable (h₁:∀ i<r,Tokew (Measuring.chart n G) b N (snag r) 0 (PowerSeries.coeff i f) A)
variable (h₂:∀ i<r,Tokew (Measuring.chart n G) b N (snag r) 0 (PowerSeries.coeff i (tariff n p l R f)) A)
variable (h₃:∀ i≤r, Tokew (address F G) (a/(S.ratio.count.val:ℝ)) N (snag r) 0 (PowerSeries.coeff i (splitV (singularity (swung F J) 0)-splitV (singularity (pushChart F G τ) 2))) K')
-- tail cost stage after. Λ/Q.W powers.
noncomputable def sherry (G:Gauge)(r m:ℕ)(s:ℕ)(v a A:ℝ):= v^(m+1)*((∑ i∈ Finset.range r, 2*2^m*tub G a s (r-i) (m+1))*A)
noncomputable def coeffSnow (r m:ℕ)(s₂ s₃ s₄:ℝ):= s₂^(m+1)*Parma.plaque r m s₃ s₄
noncomputable def chem (G:Gauge)(a C η D:ℝ)(r k N:ℕ)(g:Side)(s₁ s₂ s₃ s₄ W Z A K':ℝ):=
    (Parma.fixP G r a D η C N k/g.val*Z+Parma.fixedG G g r a D η C N k*(W^4*A)) -- replace before
    + (W^(r+1+1)*Parma.plaqueR (r+1) r s₄ A K' s₃ s₂ + s₂^(r+1+1)*(Parma.plaque r (r+1) s₃ s₄*(Z/W^2))+ W^(r+1+1)*sherry G r (r+1) N s₁ (a/g.val) A)
include hG hf hK hr hx hb hη hZ hw h hp hg hT ha ht hC hR h₁ h₂ h₃
lemma ascentPub : Tin (Measuring.chart c G) a N (r+1) w (PowerSeries.coeff r (colorCut F τ R l J f ρ)) (chem G a H η D r k N S.patch.L s₁ s₂ s₃ s₄ w Z A K'):=by
    let X₀:= Rolling.rail (maple R' G) T₀; let q:=r+1; let Y₁:= PowerSeries.coeff r (colorCut F τ R l J f ρ); have he₂:b ≤ b:=le_rfl
    have hx':3≤ snag r:=by unfold snag Whisk.ribbon; omega
    have hV:= hard S.ratio P f F' R l v hG hf hK hr hx hb hη hZ hw (fun i hi=> Tokew.delta (h₂ i hi) hx' le_rfl) h hp hg hT ha
    have hP :0≤a/L:=div_nonneg h.a0 (by positivity)
    have hQ:=capture F τ R l R' ρ J p r (r+1) hx hr hf.bond hf.plane ht hP hw ha (fun i hi=> (Tokew.soft (h₁ i hi) hT hP)) h₃ hR hC (sunrise (c:=n) ℓ hT _ hZ) hf (fun i hi=>?_)
    · change Tin T _ _ _ _ Y₁ _; have hv: Y₁=X₀+(Y₁-X₀):=by abel
      rw [hv]; apply Tin.unite (zero_lt_one.trans_le hw) hV (descendent S.ratio _ hQ h.a0)
    exact ((Tokew.soft (h₂ i hi) hT hP)).delta (by unfold snag Whisk.ribbon; omega) le_rfl
end YM.MSbar.Parma
