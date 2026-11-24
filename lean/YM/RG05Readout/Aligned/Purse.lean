import YM.RG05Readout.Aligned.Geometry
import YM.RG05Readout.Aligned.Generate
/-!
# Afford capture / readout after measured-column normalization

On the actual n-copy budgets. Includes accumulation through arbitrarily
many scales ending at a fixed physical reference. NOT spending any spatial
exponent b−a on the close interval (heights coalesce!), nor obtaining a
power gain across it. Real estimates, non-high-order use. Uniform in
admitted positions at measured scale, and cutoff N and period subject to
same-family spacing & fitting constraints. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Aligned
open Filter Topology OPE Set Function Lattice RG Wilson Source
open MergeProof Accent Ribbons ManyCopies
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Bandage
open Next.Rank Bid
open scoped Topology BigOperators Classical
variable {G:Gauge} {C:Family G} {f:Extraction.Order} {S:Table C.book}
    (hG:G.Simple) {W D r} (L:Package C W r D) {J k:ℕ}
    {I Y:Type}[Fintype I]{l:Filter Y} {T e u g:Y→ℝ}{j m:Y→ℕ}

set_option quotPrecheck false
local notation "ℓ"=> C.path.levels
local notation "δ"=> renal C.path.levels
local notation "η"=> near C.path.levels
local notation "ν"=> fly C.path.levels
local notation "X"=> bling C.path.levels
variable (d:I→ℕ) (β:I→ℝ) (p:ℕ)
include hG L
/-- Choice of output marker radii, allowing many alternatives through the
close window. Compared to fixed reference labels, calibration changes the
literal densities by positive powers of a. That's paid HERE before using the
copy/root bound. -/
lemma arms (hh:Height C.S l T m 1)(hj:Height C.S l T j 1)(ht:Tendsto T l atTop)
    (hβ:∀ i,0 < β i)(hN:0 < Fintype.card I):
    ∃ α:ℕ→ℝ, ∃ w:Y→ℝ,
      RateIs l T w 0 ∧ (∀ i,0<α i ∧ α i ≤1 ∧ ∀ j,j ≤ i→ α i ≤ license C.path δ (Fintype.card I) (carpet C.path j) (j+1)) ∧
      ∀ t:Y,w t=ManyCopies.initial C.path δ η (m t) (j t) (α (j t)) (∏ i, ν (d i) (j t)/β i) (Fintype.card I) := by
      obtain ⟨α,ha,hv,hp⟩:= halls hG L.halos (Fintype.card I) hN
      refine ⟨α,_,?_,fun i=> ⟨ha.pos _,hv _,hp _⟩,fun t=>rfl⟩
      have he : RateIs l T (fun t=>∏ i, ν (d i) (j t)/β i) 0 := by
        have hQ (i:I): RateIs l T (fun t=> ν (d i) (j t)/β i) 0 := ((flyRate hG hj (d i)).div (RateIs.const ht (hβ i))).swap (by ring)
        exact (RateIs.prod (b:=fun _=>0) (fun i _=> hQ i) ht).swap (by simp)
      apply (Height.gathered hh hj ht (height0 ha hj) he hG (Fintype.card I)).swap (by ring)

local notation "s"=> C.S.scale
-- terminalJ same role k as previous Terrain, fixed physical. Ages under study.
def markRadius (C:Family G) (d m :ℕ) := Real.exp (((d:ℝ)+1/16)*C.S.scale m)
-- radius assigned to final b replicas
include hG L
lemma repayment (hh:Height C.S l T m 1)(hj:Height C.S l T j 1)(ht:Tendsto T l atTop)
    (hk:C.ref p ≤ k)(hp:RateIs l T u 0) (he:RateIs l T e (-(p:ℝ))):
    ∀ᶠ i in l,
      let w:=markRadius C p (j i)
      march (fun _:Unit=> w) η k (m i) () ≤ δ (m i)*(u i/(16*X (m i))) ∧
      32*(1+(C.path.levels.params (m i)).columns)*w*‖alto C.path k p‖*(e i/gainChart C.path (m i) k) ≤ ν p k / 2 := by
      let w i:= markRadius C p (j i)
      let p':= (p:ℝ)
      have hw : RateIs l T w (p'+1/16) := by
          apply RateIs.exp'
          exact Tendsto.congr' (by filter_upwards with i; rw [mul_div_assoc]) (show Tendsto (fun i=> (p'+1/16) * (s (j i)/T i)) l (𝓝 (p'+1/16)) from by simpa only [mul_one] using! hj.pace.const_mul (p'+1/16)) -- check rw
      have hs : RateIs l T (fun i=> gainChart C.path (m i) k) (1/8):=by
          have hx:= hh.pace.sub (show Tendsto (fun i=> s k/T i) l (𝓝 0) from tendsto_const_nhds.div_atTop ht)
          have hc : Tendsto (fun i=> (1/8:ℝ)*(s (m i)/T i-s k/T i)) l (𝓝 (1/8)) := by simpa only [sub_zero,mul_one] using! hx.const_mul (1/8:ℝ)
          apply RateIs.exp'; exact hc.congr fun i=>by ring
      have hk':0 < ν p k:= L.system.grows p k hk
      have hb:= (RateIs.const ht (C.S.a_pos k))
      have hy:= ((hw.mul ((hh.mesh.div hb).power (p+1))).mul ((flyRate hG hh p).div (RateIs.const ht hk')))
      have hZ:= (height0 (mintN C hG|>.1) hh).mul (hp.div ((RateIs.const ht (c:=16) (by norm_num)).mul (height0 (banket C hG) hh)))
      have hV:= ((RateIs.const ht (c:=32) (by norm_num)).mul ((RateIs.const ht one_pos).add (height0 (fuNote C) hh) ht)).mul hw
      filter_upwards [hh.grows.eventually_ge_atTop k, hZ.overtakes (hy.pays ht) ht (by rw [Nat.cast_add_one]; unfold p'; ring_nf; norm_num), (RateIs.const (c:= ν p k/2) ht (by positivity)).overtakes (((hV.pays ht).mul (RateLE.const (‖alto C.path k p‖) ht)).mul ((he.div hs).pays ht)) ht (by simp [p']; linarith)] with i hi he hz
      exact ⟨(seeing C p L.system (show 0 < w i from Real.exp_pos _) (m i) k hk hi).trans he.le,hz.le⟩

-- Every period, K-frame calibrated at level m
omit hG L in
lemma spendMaster (hC:C.Makes) {N i n d:ℕ} (hd:C.ref d ≤ i) (hv:i ≤ N) (x:C.label d) :
    Spindle.paid C d i N n (masterRef hC d i N n x)= (C.labels.level d).coeffSize x := by
      let S:= C.labels.level d
      let a := (C.S.a i:ℂ)^d
      let M:= (masterRef hC d i N n x)
      have ht : Price.columns C d i N n M= a • x := by
          rw [← show Extra.Histories.Charts.window C hC d i N n M=Price.columns C d i N n M from Extra.Histories.Charts.peek C hC d N n i hd hv M]
          exact window_masterRef ..
      have hf : a≠0 := pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (C.S.a_pos _).ne')
      change S.coeffSize (a⁻¹ • Price.columns C d i N n M)=_
      rw [ht,smul_smul,inv_mul_cancel₀ hf,one_smul]
end YM.RG05Readout.Aligned
