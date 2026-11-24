import YM.MSbar.Bristol.Price
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.Bristol
open Function Filter Precision Whisk Lis Cacao Push Uniform Lattice RG Tonic Aqua
open Gauge Midpoint Rolling Exterior Wilson Wave Lis Cypress
open Matrix MvPolynomial Finset Bakery Tree MeasureTheory Duel Metric Pressure Work.G05 CrossH
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff InnerProductSpace
open Bakery.Portal Further.GaussianScalar Jade Kelvin Bout Parma Tramp Heath Stock Heath.Cottage Film Lodge Measuring RawP
variable {G:Gauge}{c:Side}{σ:Type}[Fintype σ][DecidableEq σ]
variable {G:Gauge}{c:Side}{p q m:ℕ} (R:Rep G c)(Z:Nesting G c)(b:PowerSeries ℝ)
local notation "X₀"=>Positions (Primary c G)
local notation "X"=> Pot (Primary c G)
local notation "Ω"=>ink c R.clip R.path
local notation "V"=> PowerSeries ℝ
local notation "φ"=>film R Z
local notation "S"=> bley b Z Ω
variable (u r s:ℝ)
local notation "μ"=>PowerSeries.coeff
local notation "ℓ"=> Measuring.chart c G
variable (i:G.ColorIndex){A w v t x a y Y E D:ℝ}{k d:ℕ}
open JetTab
local notation "x!"=> sun G i
variable {a1 a2 d0 t1 t2 θ:ℝ}
local notation "λ'"=> surf b s u p
local notation "T"=> film R (bley b Z (ink c R.clip R.path)) s p
local notation "f!"=> film R Z r p
local notation "P"=> pegs Z b s u p
local notation "g'"=> f! ∘ (Yturn u)
variable (hv:0<u) (hu:u*r=s) (hs:0 < w)(hw:0 < v) (hR:Premier (Rolling.main c R.clip R.path)) (h:Kind Z)(hx:Expanse Z 1 p)(hf:∀ x∈Metric.closedBall 0 v, ContDiffAt ℝ k (film R Z r p) x)
variable (hK: RangeB (Measuring.chart c G) q a v (film R Z r p) m y)
variable (hΩ:1 ≤ |caliper c (sun G i) (ink c R.clip R.path)|)(he:|stackH c (sun G i) (rim (film R (bley b Z (ink c R.clip R.path)) s p))| ≤ A)(ha:0≤a)(hq:2 ≤ q) (hL:u*w ≤ v)
variable (hk₀:p+2≤ m)(hk:m+1≤ k)
local notation "Y'"=>RangeB (Measuring.chart c G) q a
include hK hs hv hf hw hL hk
lemma outset :RangeB (Measuring.chart c G) q a w (film R Z r p ∘ Yturn u) m y ∧∀ i∈Metric.closedBall 0 w, ContDiffAt ℝ k (film R Z r p ∘ Yturn u) i := by
     refine ⟨stroll hK (by omega) hw hf hs hv hL,fun x hx=>?_⟩; apply (hf _ ?_).comp _ (Yturn u|>.contDiff.contDiffAt)
     change u • x∈Metric.closedBall 0 v; rw [mem_closedBall_zero_iff,norm_smul,Real.norm_of_nonneg hv.le]; exact (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hx) hv.le).trans hL
include hx h hu hR he hΩ ha hq hk₀
-- pay nonlinear equity
local notation "δ"=> |surf b s u p|
variable (hT:Tin (Measuring.chart c G) a q m w (pegs Z b s u p) (t1+θ* |surf b s u p|))(hP: θ/w^2 ≤ 1/2)
include hT hP
lemma vault : |surf b s u p|≤ 2*(A+y/w^2+t1/w^2):=by
     have hh:= outset R Z u r hv hs hw hf hK hL hk; let κ := g'; have he : ContDiffAt ℝ 2 κ 0:= (hh.2 0 (Metric.mem_closedBall_self hs.le)).of_le (by exact_mod_cast (show 2 ≤ k from by omega)) -- name shadow
     have ht:JetTab (Measuring.chart c G) a q w {0} κ 1 y:=by simpa using hh.1.1 1 (by omega); -- sem
     have hg:= rentH R Z b u r s i hv hu hs hR h hx he ht hΩ ‹|_|≤A› ha hq hT (by omega)
     have hh:=mul_le_mul_of_nonneg_right hP (abs_nonneg (surf b s u p))
     rw [add_div,show θ* |λ'|/w^2=θ/w^2* |λ'| by ring] at hg; linarith only [hg,hh]
omit hf hK hs hv hw hL hk hu hR he hΩ ha hq h hT hP
include hx hk₀
lemma peDegree : (pegs Z b s u p).totalDegree≤ m+1:=by
     unfold pegs; refine totalDegree_finsetSum_le (fun i hi=>?_ ); unfold lampZ; refine totalDegree_finsetSum_le (fun j hh=> (totalDegree_smul_le ..).trans ((homogeneousComponent_isHomogeneous ..).totalDegree_le.trans ?_)); apply Nat.le_trans (Nat.lt_succ_iff.mp (mem_range.mp hh)); have ht:=mem_range.mp hi; omega
include hf hK hs hv hw hL hk hu hR he hΩ ha hq h hT hP
local notation "T'"=> 2*(A+y/w^2+t1/w^2)
variable (hr:Tin (Measuring.chart c G) a q m w (ink c R.clip R.path) (w^2*Y))(hg:0≤θ) (hV:0 < d0)(hd:d0≤u)
local notation "Y0"=> (m+1:ℕ)
local notation "b0"=>w^2*Y
noncomputable def budgetK (m:ℕ)(w b Y A Bk θ:ℝ):= b+(m+1:ℕ)*(Bk+θ*(2*(A+b/w^2+Bk/w^2)))+2*(A+b/w^2+Bk/w^2)*((m+1:ℕ)*(w^2*Y))
include hr hg
lemma finale : RangeB (Measuring.chart c G) q a w (film R (bley b Z (ink c R.clip R.path)) s p) m (budgetK m w y Y A t1 θ) :=by
     let U':= T'; let G':=g'; obtain ⟨hh,hf₀⟩:= outset R Z u r hv hs hw hf hK hL hk
     have hp: δ ≤ U':= vault R Z b u r s i hv hu hs hw hR h hx hf hK hΩ he ha hq hL hk₀ hk hT hP
     have ht:= colorR P (peDegree Z b u s hx hk₀) hT hs ha; have hB:= colorR Ω (le_trans (potsD ..) (by omega)) hr hs ha
     let W:=f! ∘ Yturn u; rw [slips R Z b u r s (div_eq_iff hv.ne'|>.mpr (by rw [←hu,mul_comm])) hv hu h hx hR]
     let Hb(x:X₀):=clue P x; have he(x:X₀): ContDiffAt ℝ k (clue P) x:=(helm ..).contDiffAt
     refine Bristol.runC (Bristol.confl (f:=W + clue P) (g:=λ' • clue Ω) (Bristol.confl hh ht (show m < k from (by omega)) hs hf₀ (fun x _=> (helm ..).contDiffAt)) (srep λ' hB (show m < k from by omega) (fun x hx=> (helm ..).contDiffAt) hs) (by omega:m < k) hs (fun x hx=> show ContDiffAt ℝ k (W+ clue P) x from (hf₀ x hx).add (he x)) (fun x hx=> show ContDiffAt ℝ k (λ' • clue Ω) x from ((helm Ω (↑k)).contDiffAt).const_smul λ')) ?_
     refine add_le_add (add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add_right (mul_le_mul_of_nonneg_left hp hg) _) (Nat.cast_nonneg _)) _) (mul_le_mul_of_nonneg_right hp (mul_nonneg (Nat.cast_nonneg _) hr.dec)) -- height m
-- tune currency.S general projection
noncomputable def taxes (C H t s E:ℝ)(p:ℕ):= priceZ C p*(s*t⁻¹*(2*s^(p+1)*C^2)+(C+1)*s^(p+1))*H
noncomputable def floorS (H t s E:ℝ)(p:ℕ)(C:ℝ):= priceZ C p*(s*t⁻¹)*H
omit hT hP hg
variable {K U:ℝ}
variable (hB:μ 0 b=1)(h0:Belt p b≤ K)(h1:Belt p b⁻¹ ≤ K)(hD: |u|≤ K)(hE:u⁻¹≤ K)(hh:1≤ K)(hs0:0≤ s)(hs1:s≤1)
variable (hC: 0 ≤ taste p b s) (hG:∀ i≤p,Tin (Measuring.chart c G) a q m w (PowerSeries.coeff i Z) U)
local notation "K'"=> taxes K U d0 s 0 p
local notation "γ"=> floorS U d0 s 0 p K
include hB h0 h1 hD hE hh hs0 hs1 hC hG hV hd
noncomputable def pVault (w c y A K:ℝ):=2*(A+y/w^2+K/w^2)
lemma appeal (hP:floorS U d0 s 0 p K / w^2 ≤1/2): let P':=pVault w U y A (taxes K U d0 s 0 p); RangeB (Measuring.chart c G) q a w (film R (bley b Z (ink c R.clip R.path)) s p) m (budgetK m w y Y A (taxes K U d0 s 0 p) (floorS U d0 s 0 p K)) ∧ |u-taste p b s| ≤ d0⁻¹*(P'+2*s^(p+1)*K^2):=by
     let L:=taxes K U d0 s 0 p; let κ:= γ; have hZ: Tin ℓ a q m w P (L+κ*δ):=by
            have hp:= tones Z b u s hv h0 h1 hD hE hh hs0 hs1 hB h hG hs d0 hd hV hC -- tone variable order
            apply Tin.it hs hp (le_of_eq ?_) le_rfl; unfold L taxes κ floorS; ring
     have hκ : 0 ≤κ:=by unfold κ floorS priceZ; have hu: 0 ≤ U:= (hG _ le_rfl).dec; apply mul_nonneg _ hu; apply mul_nonneg _ (by positivity); refine sum_nonneg fun i _=> sum_nonneg fun j _=>?_ ; unfold tonK; have hx:0≤ K:=zero_le_one.trans hh; positivity
     refine ⟨Bristol.finale R Z b u r s i hv hu hs hw hR h hx hf hK hΩ he ha hq hL hk₀ hk hZ hP hr hκ,?_⟩; have he:=vault R Z b u r s i hv hu hs hw hR h hx hf hK hΩ he ha hq hL hk₀ hk hZ hP; exact (pledge b u s hv h0 h1 hD hE hh hs0 hs1 hB hd hV hC).trans (mul_le_mul_of_nonneg_left (add_le_add_left he _) (inv_pos.mpr hV).le)
end YM.MSbar.Bristol
