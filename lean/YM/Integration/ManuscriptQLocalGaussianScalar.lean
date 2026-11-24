import YM.Integration.ManuscriptQLocalIdealSquare
import YM.Integration.ConditionalAffineRootContraction
import YM.Integration.ConditionalAffineForcing

/-! The two separately prescribed Gaussian scalar terms on the original
common field, translation root, and one physical forest change. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalGaussianScalar
open Marker Bloch Function Filter Matrix Lattice Wilson RG RG.Shoot Tree Precision Exterior
open Pressure Supply Pressure.Testing Pressure.Tube Pressure.Stores Push.SectorMeasure Push.SectorMeasure.Oriented
open Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Gaussian Next.Fluctuations.Sector
open AnalyticBridge.GaussianFieldAlignment FreeResolvent FreeResolvent.Affine FreeResolvent.TestD FreeResolvent.Mark
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Greenbelt PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open PhysicalAffineScalarRootContraction
open FullQLocal.RenderedStep
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section FullLog
variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) (k : S.Choices)
local notation "E" => Vec G c 1

def spectralFee (G : Gauge) (P : Patch) (K : KernelChoices) (p : Clip) (n : ℕ) (A σ : ℝ) :=
  (Fintype.card (Co P.L (PAC G 1)):ℝ)*(earnings G P K p (n+1) A σ/2)

private theorem smooth_draw {n : ℕ} {σ A : ℝ} (hs : 0<σ) (ha : 0≤A) (hW : Sheet T.up σ A)
    (he : Bid.Larger (G:=G) S) (r : Reserve S) (o : Site c) :
    ContDiffAt ℝ n (ConditionalAffineIdealLog.root r k T.high T.up o) 0 := by
  unfold ConditionalAffineIdealLog.root
  apply ContDiffAt.sum; intro i _
  by_cases h : home S i=o
  · simp only [h,if_true]
    exact (ConditionalAffineIdealLog.spectral (t:=k) (p:=T.high) (n:=n) hs ha hW he r i).1
  · simp only [h,if_false]; exact contDiffAt_const

/-- The authentic one-parent tree draw realizes both true full padded
operators on the two original forests, at every curved field. -/
theorem logarithm {n : ℕ} {σ A : ℝ} (hs : 0<σ) (ha : 0≤A) (hW : Sheet T.up σ A)
    (he : Bid.Larger (G:=G) S) (F U : Forest S.ratio) (z o : Site c) (hu : changed S F U z)
    (l : List (raw G c)) (hl : l.length≤n) :
    let d := width G S.patch S.kernel T.high (n+1) A σ
    let M := spectralFee G S.patch S.kernel T.high n A σ
    let L (V : Forest S.ratio) := PhysicalAffineScalarSpectralRoot.halfLog T k V o
    ContDiffAt ℝ n (L F) 0 ∧ ContDiffAt ℝ n (L U) 0 ∧
      (marks G c d).pay l o*|jet (ray G c) (L F) l 0|≤M ∧
      (native c).weight d o z*(marks G c d).pay l o*
        |jet (ray G c) (L U) l 0-jet (ray G c) (L F) l 0|≤M := by
  intro d M L
  obtain ⟨r,s,hsite,hF,hU⟩ := ConditionalAffineDraws.realize F U z hu
  have hwhole := ConditionalAffineDraws.whole (G:=G) (S:=S) (allot s) U hU k T.high T.up all
  have eF : ConditionalAffineIdealLog.root r k T.high T.up o=L F := by
    change L (allot r)=L F; rw [hF]
  have eU : ConditionalAffineIdealLog.root s k T.high T.up o=L U := by
    change PhysicalAffineScalarSpectralRoot.halfLog T k (allot s) o=PhysicalAffineScalarSpectralRoot.halfLog T k U o
    unfold PhysicalAffineScalarSpectralRoot.halfLog; rw [hwhole]
  rw [←eF,←eU]
  exact ⟨smooth_draw T k hs ha hW he r o,smooth_draw T k hs ha hW he s o,
    ConditionalAffineIdealLog.rooted_entries (t:=k) (p:=T.high) (n:=n+1) hs ha hW he r s z hsite o l (by omega)⟩

end FullLog

private theorem shrink {P p W w a y M : ℝ} (hp : 0≤p) (hP : p≤P) (hw : 0≤w) (hW : w≤W)
    (ha : |a|≤1) (H : W*P*|y|≤M) : p*(w*|a*y|)≤M := by
  have hPW := mul_le_mul hW hP hp (hw.trans hW)
  have hxy : |a*y|≤|y| := by rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ha
  calc p*(w*|a*y|) = (w*p)*|a*y| := by ring
       _ ≤ (W*P)*|y| := mul_le_mul hPW hxy (abs_nonneg _) (mul_nonneg (hw.trans hW) (hp.trans hP))
       _ ≤ _ := H

private theorem add_price {w x y M N : ℝ} (hw : 0≤w) (hx : w*|x|≤M) (hy : w*|y|≤N) :
    w*|x+y|≤M+N := by
  calc _ ≤ w*(|x|+|y|) := mul_le_mul_of_nonneg_left (abs_add_le ..) hw
       _ ≤ _ := by rw [mul_add]; exact add_le_add hx hy

variable {G : Gauge} {I : Type} [DecidableEq I] {Γ : Census I}
    (R : Run G) (d : LocalFormal.Datum R.family Γ)
local notation "S" => R.family.path.levels.clock.op d.level d.period
local notation "T" => ships R.alloy.B d.cutoff d.level d.period
local notation "c₀" => R.family.side d.level d.period
local notation "E" => Vec G c₀ 1
local notation "j₁" => R.alloy.B.a.clock.J (d.level+1)
local notation "j₀" => R.alloy.B.a.clock.J d.level
local notation "Pt" => query R.metals.p R.metals.K j₁ j₀
local notation "β" => (R.family.path.rep d.cutoff d.period (d.level+1)).beta
local notation "g₀" => Next.SectorChange.coupling β
local notation "a₀" => (Pt).top.paths
local notation "σ₀" => (Pt).top.width

/-- This is the complete independently defined physical Gaussian scalar,
evaluated directly in the original fine field variable. -/
def scalar (k : (S).Choices) (F : Forest (S).ratio) (o : Site c₀) (B : E) :=
  PhysicalAffineScalarSpectralRoot.stationaryScalar T k F g₀ o (g₀ • B)

abbrev spatial := ManuscriptQLocalIdealSquare.densityWidth
abbrev tariff := ManuscriptQLocalIdealSquare.densityFee

/-- A real meter on the same literal periodic measured run. The two error
sources add on each original choice before independent fields are summed. -/
theorem rooted {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalIdealSquare.Paid n R.kit) (k : (S).Choices)
    (F U : Forest (S).ratio) (z o : Site c₀) (hu : changed S F U z) (l : List (raw G c₀))
    (hl : l.length≤n j₁ j₀) :
    let r := p.choose j₁ j₀
    let δ := spatial G (S).patch (Pt) (n j₁ j₀) r
    let M := tariff G (S).patch (Pt) (n j₁ j₀) r
    0<δ ∧ 0≤M ∧ (marks G c₀ δ).pay l o*|jet (ray G c₀) (scalar R d k F o) l 0|≤M ∧
      (marks G c₀ δ).pay l o*((native c₀).weight δ o z*|jet (ray G c₀)
        (fun B => scalar R d k U o B-scalar R d k F o B) l 0|)≤M := by
  intro r δ M
  let N := n j₁ j₀
  let L := width G (S).patch (S).kernel (T).high (N+1) a₀ σ₀
  let C := spectralFee G (S).patch (S).kernel (T).high N a₀ σ₀
  let Q := ManuscriptQLocalIdealSquare.tariff G (S).patch.L N r
  have hf := Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below
  have hK : (S).kernel = (Pt).bind := hf.knobs
  have hT : (T).high = (Pt).top.clip := hf.high
  have de : δ=min r.spatial L := by dsimp only [δ,spatial,ManuscriptQLocalIdealSquare.densityWidth,L,N]; rw [hK,hT]
  have me : M=|C|+2*Q := by dsimp only [M,tariff,ManuscriptQLocalIdealSquare.densityFee,C,Q,N,spectralFee]; rw [hK,hT]
  obtain ⟨_,_,hW,_⟩ := hf.feeds
  have hL : 0<L := (gauged G (S).patch (S).kernel (T).high (N+1) (Pt).top.width_pos (Pt).top.paths_pos.le).pos
  have hδ : 0<δ := de ▸ lt_min r.spatial_pos hL
  have hd₁ : δ≤r.spatial := de ▸ min_le_left ..; have hd₂ : δ≤L := de ▸ min_le_right ..
  let A (V : Forest (S).ratio) := PhysicalAffineScalarSpectralRoot.halfLog T k V o
  let B (V : Forest (S).ratio) := ManuscriptQLocalIdealSquare.graded R d k V g₀ o
  let A₁ (V : Forest (S).ratio) := fun b : E => A V (g₀ • b)
  let v := ray G c₀
  have hw := logarithm T k (n:=N) (Pt).top.width_pos (Pt).top.paths_pos.le hW.rows
    (ManuscriptQLocalStationaryGeometry.larger R d.cutoff d.level d.period d.below) F U z o hu l hl
  obtain ⟨hF,hU,hA,hA'⟩ := hw
  have H := ManuscriptQLocalIdealSquare.realized R d p k F U z hu
  have hn : l.length ≤ max 1 N := hl.trans (le_max_right ..)
  have hB := ManuscriptQLocalIdealSquare.rooted R d p k F U z o hu l hl
  have hg := ManuscriptQLocalIdealSquare.fine R d p
  have hpow : |g₀^l.length|≤1 := by rw [abs_of_pos (pow_pos hg.1 _)]; exact pow_le_one₀ hg.1.le hg.2
  have eg (J : Forest (S).ratio) (hJ : ContDiffAt ℝ N (A J) 0) :
      jet v (A₁ J) l 0=g₀^l.length*jet v (A J) l 0 :=
    PhysicalAffineScalarIdealGrading.pulled_jet g₀ v _ l (smooth_of_le hJ hl)
  have sm (J : Forest (S).ratio) (hJ : ContDiffAt ℝ N (A J) 0) : ContDiffAt ℝ l.length (A₁ J) 0 := by
    have hh : ContDiffAt ℝ l.length (A J) (g₀ • (0:E)) := by rw [smul_zero]; exact smooth_of_le hJ hl
    have hscale : ContDiffAt ℝ l.length (fun B : E => g₀ • B) 0 :=
      (g₀ • ContinuousLinearMap.id ℝ E).contDiff.contDiffAt
    exact hh.comp 0 hscale
  have sf := smooth_of_le (ManuscriptQLocalIdealSquare.graded_smooth R d k F g₀ o H.left) hn
  have su := smooth_of_le (ManuscriptQLocalIdealSquare.graded_smooth R d k U g₀ o H.right) hn
  have split (J : Forest (S).ratio) : scalar R d k J o = fun b => A₁ J b+B J b := by
    funext b
    change scalar R d k J o b = A₁ J b + (scalar R d k J o b - A₁ J b)
    rw [add_comm,sub_add_cancel]
  have splite : (fun b => scalar R d k U o b-scalar R d k F o b) =
      fun b => (A₁ U b-A₁ F b)+(B U b-B F b) := by funext b; rw [split U,split F]; ring
  have eΔ : jet v (fun b => A₁ U b-A₁ F b) l 0=g₀^l.length*(jet v (A U) l 0-jet v (A F) l 0) := by
    rw [jet_sub v l (sm U hU) (sm F hF),eg U hU,eg F hF,mul_sub]
  let m (w : ℝ) := (marks G c₀ w).pay l o
  let w (t : ℝ) := (native c₀).weight t o z
  have pm (d' : ℝ) (hd' : δ≤d') : m δ ≤ m d' := ConditionalAffineRootContraction.pay_le (D:=native c₀) (p:=hearth) hd' l o
  have wm (d' : ℝ) (hd' : δ≤d') : w δ≤w d' := (native c₀).weight_mono hd' o z
  have mp (d' : ℝ) : 0 ≤ m d' := ((marks G c₀ d').pay_pos ..).le
  have wp (d' : ℝ) : 0≤w d' := (native c₀).weight_nn ..
  have hv : 0≤physicalVolume G (S).patch.L r.spatial := (Finset.sum_nonneg fun _ _ => (native c₀).weight_nn ..).trans
    ((row_volume (S) r.spatial r.spatial_pos).bound o)
  have hQ : 0 ≤ Q := mul_nonneg hv
    (mul_nonneg (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) _) (mul_self_nonneg r.source))
  have a₀' : m L * |jet v (A F) l 0| ≤ C := hA
  have q₀ : m r.spatial * |jet v (B F) l 0| ≤ Q := hB.1
  have qΔ : m r.spatial * (w r.spatial * |jet v (fun b => B U b - B F b) l 0|) ≤ 2*Q := hB.2
  rw [me]
  refine ⟨hδ,by positivity,?_,?_⟩
  · rw [split F,jet_add v l (sm F hF) sf,eg F hF]
    have q₁ : m δ*|g₀^l.length*jet v (A F) l 0|≤|C| := by
      have h := shrink (a:=g₀^l.length) (y:=jet v (A F) l 0) (M:=C)
        (mp δ) (pm L hd₂) zero_le_one (le_refl (1:ℝ)) hpow (by rw [one_mul]; exact a₀')
      rw [one_mul] at h
      exact h.trans (le_abs_self C)
    have q₂ : m δ*|jet v (B F) l 0|≤2*Q := (le_trans (mul_le_mul_of_nonneg_right (pm r.spatial hd₁) (abs_nonneg _)) q₀).trans (by linarith only [hQ])
    exact add_price (mp δ) q₁ q₂
  · rw [splite,jet_add v l ((sm U hU).sub (sm F hF)) (su.sub sf),eΔ]
    let X := g₀^l.length*(jet v (A U) l 0-jet v (A F) l 0)
    have q₁ : (m δ*w δ)*|X|≤|C| := by
      rw [mul_assoc]; exact (shrink (mp δ) (pm L hd₂) (wp δ) (wm L hd₂) hpow hA').trans (le_abs_self C)
    have q₂ : (m δ*w δ)*|jet v (fun b => B U b-B F b) l 0|≤2*Q := by
      apply (mul_le_mul_of_nonneg_right (mul_le_mul (pm r.spatial hd₁) (wm r.spatial hd₁) (wp δ) (mp r.spatial)) (abs_nonneg _)).trans
      rw [mul_assoc]; exact qΔ
    rw [←mul_assoc]
    exact add_price (mul_nonneg (mp δ) (wp δ)) q₁ q₂

/-- Full ordinary and one-tree multilinear tensors of the complete
prescribed scalar. The second component sums the actual changed site. -/
theorem original {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalIdealSquare.Paid n R.kit) (k : (S).Choices)
    (F : Forest (S).ratio) (U : ∀ z : Site c₀, {U : Forest (S).ratio // changed S F U z})
    (o : Site c₀) (j : ℕ) (hj : j≤n j₁ j₀) :
    let r := p.choose j₁ j₀
    let δ := spatial G (S).patch (Pt) (n j₁ j₀) r
    let M := tariff G (S).patch (Pt) (n j₁ j₀) r
    let V := torusPay (PAC G 1) (δ/2)
    PhysicalAffineScalarFieldContraction.Root j (δ/2) o (fun _ : PUnit => o)
      (fun _ => scalar R d k F o) (V^j*M) ∧
    PhysicalAffineScalarFieldContraction.Root j (δ/2) o id
      (fun z B => scalar R d k (U z).val o B-scalar R d k F o B) ((torusPay PUnit (δ/2)*V^j)*M) := by
  intro r δ M V
  have H := rooted R d p k F (U o).val o o (U o).prop [] (Nat.zero_le _)
  constructor
  · apply PhysicalAffineScalarFieldContraction.regular G c₀ δ M H.1 H.2.1 o
    intro v
    exact (rooted R d p k F (U o).val o o (U o).prop (List.ofFn v) (by simpa only [List.length_ofFn] using hj)).2.2.1
  · apply PhysicalAffineScalarFieldContraction.tagged G c₀ δ M H.1 H.2.1 o
    intro z v
    exact (rooted R d p k F (U z).val z o (U z).prop (List.ofFn v) (by simpa only [List.length_ofFn] using hj)).2.2.2

private theorem enlarge {κ : Type*} [Fintype κ] {j : ℕ} {s A B : ℝ} {o : Site c₀}
    {q : κ→Site c₀} {f : κ→E→ℝ} (H : PhysicalAffineScalarFieldContraction.Root j s o q f A) (h : A≤B) :
    PhysicalAffineScalarFieldContraction.Root j s o q f B := by
  refine ⟨H.coefficients.trans h,?_⟩
  intro b v hv hb
  exact (H.fields b v hv hb).trans (mul_le_mul_of_nonneg_left h (Finset.prod_nonneg fun i _ => hv i))

/-- The complete root tensor and its actual one-block difference are both
bought by the original numeric schedule, before any fine period or slots. -/
theorem financed {n : ℕ→ℕ→ℕ} (p : ManuscriptQLocalIdealSquare.Paid n R.kit)
    {V : Type} {Q : Request V} (sale : NumericSchedule R.family Q) (k : (S).Choices)
    (F : Forest (S).ratio) (U : ∀ z : Site c₀, {U : Forest (S).ratio // changed S F U z})
    (o : Site c₀) (j : ℕ) (hj : j≤n j₁ j₀) :
    let r := p.choose j₁ j₀
    let s := spatial G (S).patch (Pt) (n j₁ j₀) r/2
    PhysicalAffineScalarFieldContraction.Root j s o (fun _ : PUnit => o)
      (fun _ => scalar R d k F o) (sale.admittedCost d.level) ∧
    PhysicalAffineScalarFieldContraction.Root j s o id
      (fun z B => scalar R d k (U z).val o B-scalar R d k F o B) (sale.admittedCost d.level) := by
  intro r s
  let N := n j₁ j₀
  let W := torusPay PUnit s
  let X := torusPay (PAC G 1) s
  let M := tariff G (S).patch (Pt) N r
  have P := original R d p k F U o j hj
  have hs := rooted R d p k F (U o).val o o (U o).prop [] (Nat.zero_le _)
  have hM : 0≤M := hs.2.1
  have hX : 0≤X := torusPay_nn _ _ (half_pos hs.1)
  have hW : 0≤W := torusPay_nn _ _ (half_pos hs.1)
  have hQ : X^j≤(max 1 X)^N := (pow_le_pow_left₀ hX (le_max_right ..) j).trans (pow_le_pow_right₀ (le_max_left ..) hj)
  have H := ManuscriptQLocalIdealSquare.numeric R d p sale
  have hj₁ : X^j*M≤(max 1 W*(max 1 X)^N)*M := mul_le_mul_of_nonneg_right
    (hQ.trans (le_mul_of_one_le_left (pow_nonneg (by positivity) _) (le_max_left ..))) hM
  have hj₂ : (W*X^j)*M≤(max 1 W*(max 1 X)^N)*M := mul_le_mul_of_nonneg_right
    (mul_le_mul (le_max_right ..) hQ (pow_nonneg hX _) (by positivity)) hM
  exact ⟨enlarge R d P.1 (hj₁.trans H),enlarge R d P.2 (hj₂.trans H)⟩

end YM.Integration.ManuscriptQLocalGaussianScalar
end

